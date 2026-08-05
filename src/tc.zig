const std = @import("std");
const interner = @import("interner.zig");
const inference = @import("infer.zig");
const Arena = @import("Arena.zig");
const env = @import("env.zig");
const inductive = @import("inductive.zig");
const quot = @import("quot.zig");
const util = @import("util.zig");
const value = @import("value.zig");
const root = @import("root.zig");
const swiss_map = @import("swiss_map.zig");
const union_find = @import("union_find.zig");

const ExprPtr = @import("ptr.zig").ExprPtr;
const LevelPtr = @import("ptr.zig").LevelPtr;
const LevelsPtr = @import("ptr.zig").LevelsPtr;
const NamePtr = @import("ptr.zig").NamePtr;
const TcCtx = @import("TcCtx.zig");
const ExportFile = @import("export_file.zig").ExportFile;
const Env = env.Env;
const Declar = env.Declar;
const DeclarInfo = env.DeclarInfo;
const E = value.E;
const V = value.V;
const S = value.S;

pub const prune_dm_len: usize = 1024;

pub const PruneEntry = struct { e: usize, mask: u64, r: E };

pub const TcCache = struct {
    value_eq: union_find.UnionFind(usize) = .empty,
    unfold_const_cache: swiss_map.FxHashMap(struct { NamePtr, LevelsPtr }, V) = .empty,
    rec_rule_cache: swiss_map.FxHashMap(struct { ExprPtr, LevelsPtr }, V) = .empty,
    const_head_type_cache: swiss_map.FxHashMap(struct { NamePtr, LevelsPtr }, V) = .empty,
    const_head_value_cache: swiss_map.FxHashMap(struct { NamePtr, LevelsPtr }, V) = .empty,
    const_result_level_cache: swiss_map.FxHashMap(struct { NamePtr, LevelsPtr }, LevelPtr) = .empty,
    conv_cache_neg: swiss_map.FxHashSet(struct { usize, usize }) = .empty,
    conv_cache_neg_probe: swiss_map.FxHashSet(struct { usize, usize }) = .empty,
    probe_depth: u32 = 0,
    closed_eval_cache: swiss_map.FxHashMap(ExprPtr, V) = .empty,
    open_eval_cache: swiss_map.FxHashMap(struct { usize, ExprPtr }, V) = .empty,
    bvar_hc: swiss_map.FxHashMap(struct { u32, usize }, V) = .empty,
    spine_hc: swiss_map.FxHashMap(struct { usize, u64 }, S) = .empty,
    lam_hc: swiss_map.FxHashMap(struct { ExprPtr, usize, ExprPtr }, V) = .empty,
    pi_hc: swiss_map.FxHashMap(struct { usize, usize, ExprPtr, usize }, V) = .empty,
    type_cache: swiss_map.FxHashMap(struct { usize, ExprPtr }, inference.CachedType) = .empty,
    thunk_hc: swiss_map.FxHashMap(struct { usize, ExprPtr }, V) = .empty,
    level_subs: swiss_map.FxHashMap(struct { LevelsPtr, LevelsPtr }, *const value.LevelSub) = .empty,
    lsub_bases: swiss_map.FxHashMap(usize, E) = .empty,
    rigid_hc: swiss_map.FxHashMap(struct { u8, u64, u64, usize }, V) = .empty,
    unfold_hc: swiss_map.FxHashMap(struct { NamePtr, LevelsPtr, usize, usize }, V) = .empty,
    iota_stuck: swiss_map.FxHashSet(usize) = .empty,
    struct_eta_cache: swiss_map.FxHashMap(struct { usize, NamePtr }, ?V) = .empty,
    iota_cache: swiss_map.FxHashMap(usize, V) = .empty,
    canon_cache: swiss_map.FxHashMap(usize, V) = .empty,
    content_hc: swiss_map.FxHashMap(struct { u8, u64 }, V) = .empty,
    free_bvar_cache: swiss_map.FxHashMap(usize, bool) = .empty,
    frames: interner.FrameInterner = .empty,
    prune_dm: [prune_dm_len]PruneEntry = @splat(.{ .e = 0, .mask = 0, .r = undefined }),
    quote_cache: swiss_map.FxHashMap(struct { usize, u32 }, ExprPtr) = .empty,

    pub const empty: TcCache = .{};

    pub fn deinit(self: *TcCache) void {
        inline for (@typeInfo(TcCache).@"struct".fields) |f| {
            if (comptime std.mem.eql(u8, f.name, "value_eq") or std.mem.eql(u8, f.name, "frames")) {
                @field(self, f.name).deinit();
            } else if (comptime (std.mem.eql(u8, f.name, "probe_depth") or std.mem.eql(u8, f.name, "prune_dm"))) {} else {
                @field(self, f.name).deinit(util.smp_allocator);
            }
        }
    }

    const keep_cap: usize = 1 << 15;

    pub fn clearAll(self: *TcCache) void {
        inline for (@typeInfo(TcCache).@"struct".fields) |f| {
            if (comptime std.mem.eql(u8, f.name, "value_eq")) {
                @field(self, f.name).clearShrink(keep_cap);
            } else if (comptime std.mem.eql(u8, f.name, "frames")) {
                @field(self, f.name).clearShrink(keep_cap);
            } else if (comptime std.mem.eql(u8, f.name, "prune_dm")) {
                @memset(&self.prune_dm, .{ .e = 0, .mask = 0, .r = undefined });
            } else if (comptime std.mem.eql(u8, f.name, "probe_depth")) {} else {
                @field(self, f.name).clearShrink(util.smp_allocator, keep_cap);
            }
        }
    }
};

pub const Reject = error{ CheckFailed, Declined };

var check_failed = std.atomic.Value(bool).init(false);
var check_declined = std.atomic.Value(bool).init(false);

pub fn checkingFailed() bool {
    return check_failed.load(.monotonic);
}

pub fn checkingDeclined() bool {
    return check_declined.load(.monotonic);
}

pub fn fail() void {
    check_failed.store(true, .monotonic);
}

pub fn reject(comptime fmt: []const u8, args: anytype) error{CheckFailed} {
    std.debug.print("kernel: rejected: " ++ fmt ++ "\n", args);
    return error.CheckFailed;
}

pub fn decline(comptime fmt: []const u8, args: anytype) error{Declined} {
    std.debug.print("kernel: declined: " ++ fmt ++ "\n", args);
    return error.Declined;
}

pub const TypeChecker = struct {
    ctx: *TcCtx,
    env: *const Env,
    tc_cache: *TcCache,
    arena: *Arena,
    declar_info: ?DeclarInfo,
    nat_extension: bool,

    pub fn init(
        dag: *TcCtx,
        env_: *const Env,
        arena_: *Arena,
        declar_info: ?DeclarInfo,
        cache: *TcCache,
    ) TypeChecker {
        const nat_extension = dag.export_file.config.nat_extension;
        return TypeChecker{
            .ctx = dag,
            .env = env_,
            .tc_cache = cache,
            .arena = arena_,
            .declar_info = declar_info,
            .nat_extension = nat_extension,
        };
    }
};

fn checkDeclarWith(self: *const ExportFile, d: *const Declar, ar: *Arena, ctx: *TcCtx, cache: *TcCache) void {
    if (d.* == .inductive) {
        return inductive.checkInductiveDeclar(self, d);
    }
    if (d.* == .quot) {
        quot.checkQuot(ctx, ar, d) catch |err| reportWithName(d, err);
        return;
    }
    var e = self.newEnv(.{ .by_name = d.info().name });
    var checker = TypeChecker.init(ctx, &e, ar, d.info().*, cache);
    switch (d.*) {
        .theorem, .definition, .opaque_ => inference.checkDefLike(&checker, d) catch |err| reportWithName(d, err),
        .axiom, .constructor, .recursor => inference.checkDeclarInfo(&checker, d) catch |err| reportWithName(d, err),
        .inductive, .quot => unreachable,
    }
    switch (d.*) {
        .constructor => |ctor_data| {
            if (self.declars.get(ctor_data.inductive_name) == null) {
                reject("constructor's parent inductive is not declared", .{}) catch fail();
            }
        },
        .recursor => |recursor_data| for (recursor_data.all_inductives) |ind_name| {
            if (self.declars.get(ind_name) == null) {
                reject("recursor references an undeclared inductive", .{}) catch fail();
            }
        },
        else => {},
    }
}

pub fn reportWithName(d: *const Declar, err: Reject) void {
    var buf: [512]u8 = undefined;
    var w = std.Io.Writer.fixed(&buf);
    @import("debug_printer.zig").debugPrint(&w, d.info().name) catch {};
    switch (err) {
        error.CheckFailed => {
            std.debug.print("kernel: rejected declaration: {s}\n", .{w.buffered()});
            fail();
        },
        error.Declined => {
            std.debug.print("kernel: declined declaration: {s}\n", .{w.buffered()});
            check_declined.store(true, .monotonic);
        },
    }
}

const session_budget: usize = 1 << 23;

const Session = struct {
    ar: Arena,
    ctx: TcCtx,
    cache: TcCache,

    fn init(ef: *const ExportFile, self: *Session) void {
        self.ar = Arena.init(util.smp_allocator);
        self.ctx = TcCtx.init(ef, &self.ar);
        self.cache = .empty;
    }

    fn deinit(self: *Session) void {
        self.cache.deinit();
        TcCtx.deinit(&self.ctx);
        self.ar.deinit();
    }

    fn recycle(self: *Session) void {
        self.cache.clearAll();
        self.ctx.dag.clear();
        self.ctx.level_cache.simplify_cache.clearRetainingCapacity();
        self.ctx.level_cache.eq_cache.clearRetainingCapacity();
        self.ar.reset();
    }
};

pub fn checkAllDeclarsSerial(self: *const ExportFile) void {
    const Worker = struct {
        fn run(ef: *const ExportFile) void {
            var s: Session = undefined;
            Session.init(ef, &s);
            defer s.deinit();
            var it = ef.declars.iterator();
            while (it.next()) |entry| {
                checkDeclarWith(ef, entry.value_ptr, &s.ar, &s.ctx, &s.cache);
                if (s.ar.bytes > session_budget) s.recycle();
            }
        }
    };
    const t = std.Thread.spawn(.{ .stack_size = root.stack_size }, Worker.run, .{self}) catch util.oom();
    t.join();
}

const chunk_size: usize = 64;

fn checkAllDeclarsPar(self: *const ExportFile, num_threads: usize) void {
    var task_num = std.atomic.Value(usize).init(0);
    const Worker = struct {
        fn run(ef: *const ExportFile, counter: *std.atomic.Value(usize)) void {
            var s: Session = undefined;
            Session.init(ef, &s);
            defer s.deinit();
            const total = ef.declars.count();
            while (true) {
                const start = counter.fetchAdd(chunk_size, .monotonic);
                if (start >= total) break;
                const end = @min(start + chunk_size, total);
                for (ef.declars.values()[start..end]) |*d| {
                    checkDeclarWith(ef, d, &s.ar, &s.ctx, &s.cache);
                    if (s.ar.bytes > session_budget) s.recycle();
                }
            }
        }
    };
    var handles = std.ArrayList(std.Thread).empty;
    defer handles.deinit(util.smp_allocator);
    var i: usize = 0;
    while (i < num_threads) : (i += 1) {
        const t = std.Thread.spawn(
            .{ .stack_size = root.stack_size },
            Worker.run,
            .{ self, &task_num },
        ) catch util.oom();
        handles.append(util.smp_allocator, t) catch util.oom();
    }
    for (handles.items) |t| {
        t.join();
    }
}

pub fn checkAllDeclars(self: *const ExportFile) void {
    if (self.config.num_threads > 1) {
        checkAllDeclarsPar(self, self.config.num_threads);
    } else {
        checkAllDeclarsSerial(self);
    }
}
