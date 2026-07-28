//! Self-contained tests and microbenchmark for the arity-annotated apply-n path
//! (`eval.applyMany`). These build a minimal `TypeChecker` over an empty
//! environment and exercise pure beta reduction of deeply curried lambdas, for
//! which no declarations are needed. The correctness tests assert that the fast
//! apply-n path agrees, pointer-for-pointer, with folding the one-argument
//! `apply` over the same argument vector. The (non-asserting) microbenchmark
//! reports the wall-clock difference so the mechanism can be measured without an
//! external Lean export.

const std = @import("std");

const Arena = @import("Arena.zig");
const Dag = @import("Dag.zig");
const TcCtx = @import("TcCtx.zig");
const tc = @import("tc.zig");
const eval = @import("eval.zig");
const value = @import("value.zig");
const env = @import("env.zig");
const expr = @import("expr.zig");
const name = @import("name.zig");
const level = @import("level.zig");
const swiss_map = @import("swiss_map.zig");
const export_file_mod = @import("export_file.zig");

const ExportFile = export_file_mod.ExportFile;
const Config = export_file_mod.Config;
const NamePtr = @import("ptr.zig").NamePtr;
const LevelPtr = @import("ptr.zig").LevelPtr;
const ExprPtr = @import("ptr.zig").ExprPtr;
const V = value.V;

fn nowNs() u64 {
    var ts: std.c.timespec = undefined;
    _ = std.c.clock_gettime(std.c.CLOCK.MONOTONIC, &ts);
    return @as(u64, @intCast(ts.sec)) *% std.time.ns_per_s +% @as(u64, @intCast(ts.nsec));
}

/// A minimal, self-owned type-checking harness over an empty environment.
const Harness = struct {
    arena: Arena,
    ef_dag: Dag,
    ef: ExportFile,
    ctx: TcCtx,
    e0: env.Env,
    cache: tc.TcCache,
    checker: tc.TypeChecker,

    fn create(alloc: std.mem.Allocator) *Harness {
        const h = alloc.create(Harness) catch @panic("oom");
        h.arena = Arena.init(alloc);
        const config = Config{};
        h.ef_dag = Dag.init(&config);
        const anon = NamePtr.global(h.arena.alloc(name.Name, name.Name.anon));
        const zero = LevelPtr.global(h.ef_dag.levels.intern(&h.arena, level.Level.zero));
        h.ef = .{
            .dag = h.ef_dag,
            .anon = anon,
            .zero = zero,
            .declars = env.DeclarMap.empty,
            .name_cache = h.ef_dag.mkNameCache(anon),
            .config = config,
            .mutual_block_sizes = swiss_map.FxHashMap(NamePtr, struct { usize, usize }).empty,
        };
        h.ctx = TcCtx.init(&h.ef, &h.arena);
        h.e0 = h.ef.newEnv(.empty);
        h.cache = tc.TcCache.empty;
        h.checker = tc.TypeChecker.init(&h.ctx, &h.e0, &h.arena, null, &h.cache);
        return h;
    }

    fn destroy(h: *Harness, alloc: std.mem.Allocator) void {
        h.checker.deinit();
        h.cache.deinit();
        h.ctx.deinit();
        h.ef_dag.deinit();
        h.arena.deinit();
        alloc.destroy(h);
    }

    /// `λ … λ. (bvar sel_idx)` with `k` binders, all of binder type `Prop`.
    fn nestLambda(h: *Harness, k: u16, sel_idx: u16) ExprPtr {
        const anon = h.ef.anon;
        const prop = TcCtx.mkSort(&h.ctx, h.ef.zero);
        var body = TcCtx.mkVar(&h.ctx, sel_idx);
        var i: u16 = 0;
        while (i < k) : (i += 1) {
            body = TcCtx.mkLambda(&h.ctx, anon, .default, prop, body);
        }
        return body;
    }

    /// `k` distinct `Sort` values to use as arguments.
    fn mkArgs(h: *Harness, alloc: std.mem.Allocator, k: usize) []V {
        const args = alloc.alloc(V, k) catch @panic("oom");
        for (args, 0..) |*a, i| {
            _ = i;
            a.* = value.mkSort(&h.arena, h.ef.zero);
        }
        return args;
    }

    fn evalLam(h: *Harness, f_expr: ExprPtr) V {
        return eval.eval(&h.checker, 0, value.envEmpty(), f_expr);
    }

    fn applyFold(h: *Harness, f0: V, args: []const V) V {
        var f = f0;
        for (args) |a| f = eval.apply(&h.checker, 0, f, a);
        return f;
    }
};

// applyMany must agree, pointer-for-pointer, with folding `apply`, and both
// must select the argument the de Bruijn body names.
test "applyMany agrees with apply fold on curried selection" {
    const gpa = std.testing.allocator;
    const configs = [_]struct { k: u16, sel: u16 }{
        .{ .k = 1, .sel = 0 },
        .{ .k = 2, .sel = 0 },
        .{ .k = 2, .sel = 1 },
        .{ .k = 3, .sel = 2 },
        .{ .k = 8, .sel = 0 },
        .{ .k = 8, .sel = 7 },
        .{ .k = 8, .sel = 3 },
        .{ .k = 70, .sel = 0 }, // exercises the >64 loose-bvar env path
        .{ .k = 70, .sel = 69 },
    };
    for (configs) |cfg| {
        const h = Harness.create(gpa);
        defer h.destroy(gpa);
        const args = h.mkArgs(gpa, cfg.k);
        defer gpa.free(args);

        const f_expr = h.nestLambda(cfg.k, cfg.sel);
        const lam = h.evalLam(f_expr);
        try std.testing.expect(lam.* == .lam);
        try std.testing.expectEqual(@as(u32, cfg.k), eval.lamArity(&h.checker, lam));

        const slow = h.applyFold(lam, args);
        const fast = eval.applyMany(&h.checker, 0, lam, args);

        // de Bruijn body `bvar sel` under `k` binders selects args[k-1-sel].
        const expected = args[cfg.k - 1 - cfg.sel];
        try std.testing.expectEqual(expected, slow);
        try std.testing.expectEqual(expected, fast);
        try std.testing.expectEqual(slow, fast);
    }
}

// Splitting the argument vector across two applyMany calls (a partial
// application / PAP is materialised in between) matches applying it all at once.
test "applyMany partial application composes" {
    const gpa = std.testing.allocator;
    const k: u16 = 6;
    const sel: u16 = 5; // selects the first argument (args[0])
    const h = Harness.create(gpa);
    defer h.destroy(gpa);

    const args = h.mkArgs(gpa, k);
    defer gpa.free(args);

    const lam = h.evalLam(h.nestLambda(k, sel));
    try std.testing.expect(lam.* == .lam);

    const whole = eval.applyMany(&h.checker, 0, lam, args);
    const pap = eval.applyMany(&h.checker, 0, lam, args[0..3]);
    try std.testing.expect(pap.* == .lam); // under-applied: still a lambda
    try std.testing.expectEqual(@as(u32, 3), eval.lamArity(&h.checker, pap));
    const split = eval.applyMany(&h.checker, 0, pap, args[3..]);

    try std.testing.expectEqual(args[0], whole);
    try std.testing.expectEqual(args[0], split);
}

// applyMany over an empty vector is the identity.
test "applyMany empty is identity" {
    const gpa = std.testing.allocator;
    const h = Harness.create(gpa);
    defer h.destroy(gpa);
    const lam = h.evalLam(h.nestLambda(3, 0));
    try std.testing.expectEqual(lam, eval.applyMany(&h.checker, 0, lam, &.{}));
}

const Strategy = enum { fold, many };

// Runs `iters` independent saturations of a `k`-ary curried lambda on a FRESH
// harness (hence a fresh value arena), so the two strategies are compared on
// equal footing rather than one inheriting the other's arena bloat. Returns
// nanoseconds for the timed region.
fn benchRun(gpa: std.mem.Allocator, k: u16, iters: usize, strat: Strategy, sink: *usize) u64 {
    const h = Harness.create(gpa);
    defer h.destroy(gpa);
    const args = h.mkArgs(gpa, k);
    defer gpa.free(args);
    const f_expr = h.nestLambda(k, k - 1);

    const t0 = nowNs();
    for (0..iters) |_| {
        h.cache.clear();
        const lam = h.evalLam(f_expr);
        const r = switch (strat) {
            .fold => h.applyFold(lam, args),
            .many => eval.applyMany(&h.checker, 0, lam, args),
        };
        sink.* +%= @intFromPtr(r);
    }
    return nowNs() - t0;
}

// Non-asserting microbenchmark: times the fast apply-n path against the
// one-argument apply fold on a wide curried application, clearing the eval
// caches each iteration so real reduction work is measured, not memoisation.
// Best-of-N to damp noise. Prints to stderr; `zig build test 2>&1 | grep apply-n`.
test "microbench applyMany vs apply fold" {
    if (@import("builtin").mode == .Debug) return error.SkipZigTest;
    const gpa = std.testing.allocator;
    const k: u16 = 32;
    const iters: usize = 4000;
    const reps = 5;

    var sink: usize = 0;
    // Warmup (also primes the global allocator).
    _ = benchRun(gpa, k, iters, .fold, &sink);
    _ = benchRun(gpa, k, iters, .many, &sink);

    var fold_ns: u64 = std.math.maxInt(u64);
    var many_ns: u64 = std.math.maxInt(u64);
    for (0..reps) |_| {
        fold_ns = @min(fold_ns, benchRun(gpa, k, iters, .fold, &sink));
        many_ns = @min(many_ns, benchRun(gpa, k, iters, .many, &sink));
    }

    std.debug.print(
        "\napply-n microbench (k={d}, {d} iters, best of {d}): apply-fold {d} ns, applyMany {d} ns ({d:.2}x speedup); sink={x}\n",
        .{ k, iters, reps, fold_ns, many_ns, @as(f64, @floatFromInt(fold_ns)) / @as(f64, @floatFromInt(many_ns)), sink },
    );
}
