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
    spine_hc: swiss_map.FxHashMap(struct { usize, u8, u64, u64 }, S) = .empty,
    lam_hc: swiss_map.FxHashMap(struct { ExprPtr, usize, ExprPtr }, V) = .empty,
    pi_hc: swiss_map.FxHashMap(struct { usize, usize, ExprPtr, u8, usize }, V) = .empty,
    type_cache: swiss_map.FxHashMap(struct { usize, ExprPtr }, inference.CachedType) = .empty,
    thunk_hc: swiss_map.FxHashMap(struct { usize, ExprPtr }, V) = .empty,
    frame_envs: swiss_map.FxHashMap(usize, E) = .empty,
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
    quote_cache: swiss_map.FxHashMap(struct { usize, u32 }, ExprPtr) = .empty,

    pub const empty: TcCache = .{};

    pub fn deinit(self: *TcCache) void {
        inline for (@typeInfo(TcCache).@"struct".fields) |f| {
            if (comptime std.mem.eql(u8, f.name, "value_eq")) {
                @field(self, f.name).deinit();
            } else if (comptime std.mem.eql(u8, f.name, "probe_depth")) {} else {
                @field(self, f.name).deinit(util.smp_allocator);
            }
        }
    }

    pub fn clear(self: *TcCache) void {
        inline for (@typeInfo(TcCache).@"struct".fields) |f| {
            if (comptime std.mem.eql(u8, f.name, "value_eq")) {
                @field(self, f.name).clear();
            } else if (comptime (std.mem.eql(u8, f.name, "probe_depth") or std.mem.eql(u8, f.name, "closed_eval_cache"))) {} else {
                @field(self, f.name).clearRetainingCapacity();
            }
        }
    }
};

pub const InferFlag = enum {
    InferOnly,
    Check,
};

pub const Reject = error{CheckFailed};

var check_failed = std.atomic.Value(bool).init(false);

pub fn checkingFailed() bool {
    return check_failed.load(.monotonic);
}

pub fn fail() void {
    check_failed.store(true, .monotonic);
}

pub fn reject(comptime fmt: []const u8, args: anytype) Reject {
    std.debug.print("kernel: rejected: " ++ fmt ++ "\n", args);
    return error.CheckFailed;
}

pub const TypeChecker = struct {
    ctx: *TcCtx,
    env: *const Env,
    tc_cache: *TcCache,
    arena: *Arena,
    declar_info: ?DeclarInfo,
    nat_extension: bool,
    frames: interner.FrameInterner,

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
            .frames = .empty,
        };
    }

    pub fn deinit(self: *TypeChecker) void {
        self.frames.deinit();
    }
};

fn checkDeclarWith(self: *const ExportFile, d: *const Declar, ar: *Arena, ctx: *TcCtx, cache: *TcCache) void {
    if (d.* == .inductive) {
        return inductive.checkInductiveDeclar(self, d);
    }
    if (d.* == .quot) {
        quot.checkQuot(ctx, ar, d) catch fail();
        return;
    }
    var e = self.newEnv(.{ .by_name = d.info().name });
    var checker = TypeChecker.init(ctx, &e, ar, d.info().*, cache);
    defer checker.deinit();
    switch (d.*) {
        .theorem, .definition, .opaque_ => inference.checkDefLike(&checker, d) catch failWithName(d),
        .axiom, .constructor, .recursor => inference.checkDeclarInfo(&checker, d) catch failWithName(d),
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

pub fn failWithName(d: *const Declar) void {
    var buf: [512]u8 = undefined;
    var w = std.Io.Writer.fixed(&buf);
    @import("debug_printer.zig").debugPrint(&w, d.info().name) catch {};
    std.debug.print("kernel: rejected declaration: {s}\n", .{w.buffered()});
    fail();
}

pub fn checkDeclar(self: *const ExportFile, d: *const Declar) void {
    var ar = Arena.init(util.smp_allocator);
    defer ar.deinit();
    var ctx = TcCtx.init(self, &ar);
    defer TcCtx.deinit(&ctx);
    var cache: TcCache = .empty;
    defer cache.deinit();
    checkDeclarWith(self, d, &ar, &ctx, &cache);
}

pub fn checkAllDeclarsSerial(self: *const ExportFile) void {
    const Worker = struct {
        fn run(ef: *const ExportFile) void {
            var it = ef.declars.iterator();
            while (it.next()) |entry| {
                checkDeclar(ef, entry.value_ptr);
            }
        }
    };
    const t = std.Thread.spawn(.{ .stack_size = root.stack_size }, Worker.run, .{self}) catch util.oom();
    t.join();
}

fn checkAllDeclarsPar(self: *const ExportFile, num_threads: usize) void {
    var task_num = std.atomic.Value(usize).init(0);
    const Worker = struct {
        fn run(ef: *const ExportFile, counter: *std.atomic.Value(usize)) void {
            while (true) {
                const idx = counter.fetchAdd(1, .monotonic);
                if (idx < ef.declars.count()) {
                    checkDeclar(ef, &ef.declars.values()[idx]);
                } else {
                    break;
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
