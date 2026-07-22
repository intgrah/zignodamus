const std = @import("std");
const level = @import("level.zig");
const expr = @import("expr.zig");
const Arena = @import("Arena.zig");
const conv = @import("conv.zig");
const env = @import("env.zig");
const inductive = @import("inductive.zig");
const quot = @import("quot.zig");
const util = @import("util.zig");
const value = @import("value.zig");
const num_bigint = @import("big_uint.zig");
const root = @import("root.zig");
const nat = @import("nat.zig");
const swiss_map = @import("swiss_map.zig");
const union_find = @import("union_find.zig");
const NatRed = @import("Dag.zig").NatRed;

const ExprPtr = @import("ptr.zig").ExprPtr;
const LevelPtr = @import("ptr.zig").LevelPtr;
const LevelsPtr = @import("ptr.zig").LevelsPtr;
const NamePtr = @import("ptr.zig").NamePtr;
const StringPtr = @import("ptr.zig").StringPtr;
const TcCtx = @import("TcCtx.zig");
const ExportFile = @import("export_file.zig").ExportFile;
const Env = env.Env;
const Declar = env.Declar;
const DeclarInfo = env.DeclarInfo;
const InductiveData = env.InductiveData;
const ConstructorData = env.ConstructorData;
const RecursorData = env.RecursorData;
const RecRule = env.RecRule;
const E = value.E;
const V = value.V;
const S = value.S;

const TcCache = struct {
    infer_cache_check: swiss_map.UniqueHashMap(ExprPtr, ExprPtr) = .empty,
    infer_cache_no_check: swiss_map.UniqueHashMap(ExprPtr, ExprPtr) = .empty,
    whnf_cache: swiss_map.UniqueHashMap(ExprPtr, ExprPtr) = .empty,
    whnf_no_unfolding_cache: swiss_map.UniqueHashMap(ExprPtr, ExprPtr) = .empty,
    eq_cache: union_find.UnionFind(ExprPtr) = .empty,
    unfold_const_cache: swiss_map.FxHashMap(struct { NamePtr, LevelsPtr }, V) = .empty,
    rec_rule_cache: swiss_map.FxHashMap(struct { ExprPtr, LevelsPtr }, V) = .empty,
    const_head_type_cache: swiss_map.FxHashMap(struct { NamePtr, LevelsPtr }, V) = .empty,
    const_head_value_cache: swiss_map.FxHashMap(struct { NamePtr, LevelsPtr }, V) = .empty,
    const_result_level_cache: swiss_map.FxHashMap(struct { NamePtr, LevelsPtr }, LevelPtr) = .empty,
    conv_cache: swiss_map.FxHashSet(struct { usize, usize }) = .empty,
    conv_cache_neg: swiss_map.FxHashSet(struct { usize, usize }) = .empty,
    conv_cache_neg_probe: swiss_map.FxHashSet(struct { usize, usize }) = .empty,
    probe_depth: u32 = 0,
    closed_eval_cache: swiss_map.FxHashMap(ExprPtr, V) = .empty,
    open_eval_cache: swiss_map.FxHashMap(struct { usize, ExprPtr }, V) = .empty,
    open_eval_seen: swiss_map.FxHashSet(ExprPtr) = .empty,
    bvar_hc: swiss_map.FxHashMap(struct { u32, usize }, V) = .empty,
    env_hc: swiss_map.FxHashMap(struct { usize, usize }, E) = .empty,
    spine_hc: swiss_map.FxHashMap(struct { usize, u8, u64, u64 }, S) = .empty,
    lam_hc: swiss_map.FxHashMap(struct { ExprPtr, usize, ExprPtr }, V) = .empty,
    pi_hc: swiss_map.FxHashMap(struct { usize, usize, ExprPtr }, V) = .empty,
    rigid_hc: swiss_map.FxHashMap(struct { u8, u64, u64, usize }, V) = .empty,
    unfold_hc: swiss_map.FxHashMap(struct { NamePtr, LevelsPtr, usize, usize }, V) = .empty,
    iota_stuck: swiss_map.FxHashSet(usize) = .empty,
    struct_eta_cache: swiss_map.FxHashMap(struct { usize, NamePtr }, ?V) = .empty,
    iota_cache: swiss_map.FxHashMap(usize, V) = .empty,
    canon_cache: swiss_map.FxHashMap(usize, V) = .empty,
    content_hc: swiss_map.FxHashMap(struct { u8, u64 }, V) = .empty,
    fvar_cache: swiss_map.FxHashMap(usize, bool) = .empty,

    pub const empty: TcCache = .{};

    pub fn deinit(self: *TcCache) void {
        inline for (@typeInfo(TcCache).@"struct".fields) |f| {
            if (comptime std.mem.eql(u8, f.name, "eq_cache")) {
                self.eq_cache.deinit();
            } else if (comptime std.mem.eql(u8, f.name, "probe_depth")) {} else {
                @field(self, f.name).deinit(util.smp_allocator);
            }
        }
    }

    pub fn clear(self: *TcCache) void {
        inline for (@typeInfo(TcCache).@"struct".fields) |f| {
            if (comptime std.mem.eql(u8, f.name, "eq_cache")) {
                self.eq_cache.clear();
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
    tc_cache: TcCache,
    arena: *Arena,
    local_v_cache: swiss_map.FxHashMap(ExprPtr, V),
    declar_info: ?DeclarInfo,
    nat_extension: bool,

    pub fn init(
        dag: *TcCtx,
        env_: *const Env,
        arena_: *Arena,
        declar_info: ?DeclarInfo,
    ) TypeChecker {
        util.assert(dag.dbj_level_counter == 0);
        const nat_extension = dag.export_file.config.nat_extension;
        return TypeChecker{
            .ctx = dag,
            .env = env_,
            .tc_cache = .empty,
            .arena = arena_,
            .local_v_cache = .{},
            .declar_info = declar_info,
            .nat_extension = nat_extension,
        };
    }

    pub fn deinit(self: *TypeChecker) void {
        self.tc_cache.deinit();
        self.local_v_cache.deinit(util.smp_allocator);
    }
};

fn checkDefLike(checker: *TypeChecker, d: *const Declar) Reject!void {
    try checkDeclarInfo(checker, d);
    const val = switch (d.*) {
        .theorem => |x| x.val,
        .definition => |x| x.val,
        .opaque_ => |x| x.val,
        else => unreachable,
    };
    const inferred_type = try infer(checker, val, .Check);
    try assertDefEq(checker, inferred_type, d.info().ty);
}

pub fn checkDeclar(self: *const ExportFile, d: *const Declar) void {
    if (d.* == .inductive) {
        return inductive.checkInductiveDeclar(self, d);
    }
    var ar = Arena.init(util.smp_allocator);
    defer ar.deinit();
    var ctx = TcCtx.init(self, &ar);
    defer TcCtx.deinit(&ctx);
    if (d.* == .quot) {
        quot.checkQuot(&ctx, &ar, d) catch fail();
        return;
    }
    var e = self.newEnv(.{ .by_name = d.info().name });
    var checker = TypeChecker.init(&ctx, &e, &ar, d.info().*);
    defer checker.deinit();
    switch (d.*) {
        .theorem, .definition, .opaque_ => checkDefLike(&checker, d) catch fail(),
        .axiom, .constructor, .recursor => checkDeclarInfo(&checker, d) catch fail(),
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

pub fn checkDeclarInfo(self: *TypeChecker, d: *const Declar) Reject!void {
    const info = d.info();
    if (!level.noDupesAllParams(self.ctx, info.uparams)) {
        return reject("duplicate universe parameters in declaration", .{});
    }
    if (expr.hasFvars(info.ty)) {
        return reject("declaration type contains free variables", .{});
    }
    const inferred_type = try infer(self, info.ty, .Check);
    const sort = try ensureSort(self, inferred_type);

    if (d.* == .theorem) {
        if (!level.isZero(self.ctx, sort)) {
            return reject("theorem type must be Prop (sort 0)", .{});
        }
    }
}

fn inferConst(self: *TypeChecker, c_name: NamePtr, c_uparams: LevelsPtr, flag: InferFlag) Reject!ExprPtr {
    if (env.Env.getDeclar(self.env, c_name)) |declar_| {
        const declar_info = declar_.info().*;
        if (flag == .Check) {
            if (self.declar_info) |this_declar_info| {
                for (c_uparams.asRef()) |c_uparam| {
                    util.assert(level.allUparamsDefined(self.ctx, c_uparam, this_declar_info.uparams));
                }
            }
        }
        return expr.substDeclarInfoLevels(self.ctx, declar_info, c_uparams);
    } else {
        return reject("declaration not found in infer_const", .{});
    }
}

fn getRecRule(rec_rules: []const RecRule, major_const: ExprPtr) ?RecRule {
    switch (major_const.asRef().kind) {
        .@"const" => |c| {
            const major_ctor_name = c.name;
            for (rec_rules) |r| {
                if (r.ctor_name == major_ctor_name) {
                    return r;
                }
            }
        },
        else => {},
    }
    return null;
}

fn expandEtaStructAux(self: *TypeChecker, e_type: ExprPtr, e: ExprPtr) ?ExprPtr {
    const uca = expr.unfoldConstApps(self.ctx.bump, e_type) orelse return null;
    const c_name = uca.name;
    const c_levels = uca.levels;
    const args = uca.args;
    const ind = env.Env.getInductive(self.env, c_name) orelse return null;
    const all_ctor_names = ind.all_ctor_names;
    if (all_ctor_names.len == 0) return null;
    const ctor_name0 = all_ctor_names[0];
    const ctor_data = env.Env.getConstructor(self.env, ctor_name0).?;
    const num_params = ctor_data.num_params;
    const num_fields = ctor_data.num_fields;
    var out = TcCtx.mkConst(self.ctx, ctor_name0, c_levels);
    var i: usize = 0;
    while (i < @as(usize, num_params)) : (i += 1) {
        out = TcCtx.mkApp(self.ctx, out, args.items[i]);
    }
    i = 0;
    while (i < @as(usize, num_fields)) : (i += 1) {
        const proj = TcCtx.mkProj(self.ctx, c_name, i, e);
        out = TcCtx.mkApp(self.ctx, out, proj);
    }
    return out;
}

pub fn ensureInfersAsSort(self: *TypeChecker, e: ExprPtr) Reject!LevelPtr {
    const infd = try infer(self, e, .Check);
    return try ensureSort(self, infd);
}

pub fn ensureSort(self: *TypeChecker, e: ExprPtr) Reject!LevelPtr {
    switch (e.asRef().kind) {
        .sort => |s| return s.level,
        else => {},
    }
    const whnfd = whnf(self, e);
    switch (whnfd.asRef().kind) {
        .sort => |s| return s.level,
        else => return reject("expected a sort", .{}),
    }
}

fn ensurePi(self: *TypeChecker, e: ExprPtr) Reject!ExprPtr {
    switch (e.asRef().kind) {
        .pi => return e,
        else => {},
    }
    const whnfd = whnf(self, e);
    switch (whnfd.asRef().kind) {
        .pi => return whnfd,
        else => return reject("expected a pi type", .{}),
    }
}

pub fn inferSortOf(self: *TypeChecker, e: ExprPtr, flag: InferFlag) Reject!LevelPtr {
    const whnfd = try inferThenWhnf(self, e, flag);
    switch (whnfd.asRef().kind) {
        .sort => |s| return s.level,
        else => return reject("expected a sort", .{}),
    }
}

fn strLitToCtorReducing(self: *TypeChecker, x: StringPtr) ?ExprPtr {
    if (expr.strLitToConstructor(self.ctx, x)) |c| {
        return whnf(self, c);
    }
    return null;
}

fn doNatBin(self: *TypeChecker, x_in: ExprPtr, y_in: ExprPtr, op: NatRed) ?ExprPtr {
    const x = whnf(self, x_in);
    const y = whnf(self, y_in);
    const arg1 = expr.getBignumFromExpr(self.ctx, x) orelse return null;
    defer num_bigint.free(arg1);
    const arg2 = expr.getBignumFromExpr(self.ctx, y) orelse return null;
    defer num_bigint.free(arg2);
    return switch (op) {
        .succ, .div_go, .mod_core_go => unreachable,
        .add => TcCtx.mkNatLitQuick(self.ctx, nat.natAdd(arg1, arg2)),
        .sub => TcCtx.mkNatLitQuick(self.ctx, nat.natSub(arg1, arg2)),
        .mul => TcCtx.mkNatLitQuick(self.ctx, nat.natMul(arg1, arg2)),
        .pow => if (nat.natPow(arg1, arg2)) |r| TcCtx.mkNatLitQuick(self.ctx, r) else null,
        .div => TcCtx.mkNatLitQuick(self.ctx, nat.natDiv(arg1, arg2)),
        .mod => TcCtx.mkNatLitQuick(self.ctx, nat.natMod(arg1, arg2)),
        .gcd => TcCtx.mkNatLitQuick(self.ctx, nat.natGcd(&arg1, &arg2)),
        .land => TcCtx.mkNatLitQuick(self.ctx, nat.natLand(arg1, arg2)),
        .lor => TcCtx.mkNatLitQuick(self.ctx, nat.natLor(arg1, arg2)),
        .xor => TcCtx.mkNatLitQuick(self.ctx, nat.natXor(&arg1, &arg2)),
        .shl => if (nat.natShl(arg1, arg2)) |r| TcCtx.mkNatLitQuick(self.ctx, r) else null,
        .shr => if (nat.natShr(arg1, arg2)) |r| TcCtx.mkNatLitQuick(self.ctx, r) else null,
        .beq => expr.boolToExpr(self.ctx, nat.natEq(arg1, arg2)),
        .ble => expr.boolToExpr(self.ctx, nat.natLe(arg1, arg2)),
    };
}

pub fn tryReduceNat(self: *TypeChecker, e: ExprPtr) ?ExprPtr {
    if (!self.ctx.export_file.config.nat_extension) {
        return null;
    }
    if (expr.hasFvars(e)) {
        return null;
    }
    const ua = expr.unfoldApps(self.ctx.bump, e);
    const f = ua.fun;
    const args = ua.args;
    const name_cache = &self.ctx.export_file.name_cache;
    switch (f.asRef().kind) {
        .@"const" => |c| {
            const kind = name_cache.nat_red.get(c.name) orelse return null;
            switch (kind) {
                .succ => {
                    if (args.items.len != 1) return null;
                    const v_expr = whnf(self, args.items[0]);
                    return expr.getBignumSuccFromExpr(self.ctx, v_expr);
                },
                .div_go, .mod_core_go => return null,
                else => {
                    if (args.items.len != 2) return null;
                    return doNatBin(self, args.items[0], args.items[1], kind);
                },
            }
        },
        else => return null,
    }
}

fn reduceProj(self: *TypeChecker, idx: usize, structure_in: ExprPtr) ?ExprPtr {
    var structure = whnf(self, structure_in);
    switch (structure.asRef().kind) {
        .string_lit => |sl| {
            if (strLitToCtorReducing(self, sl.ptr)) |s| {
                structure = s;
            }
        },
        else => {},
    }
    const uca = expr.unfoldConstApps(self.ctx.bump, structure) orelse return null;
    const name = uca.name;
    const args = uca.args;
    const ctor_data = env.Env.getConstructor(self.env, name) orelse return null;
    const i = @as(usize, ctor_data.num_params) + idx;
    return args.items[i];
}

pub fn inferThenWhnf(self: *TypeChecker, e: ExprPtr, flag: InferFlag) Reject!ExprPtr {
    const ty = try infer(self, e, flag);
    return whnf(self, ty);
}

fn inferProj(self: *TypeChecker, _ty_name: NamePtr, idx: usize, structure: ExprPtr, flag: InferFlag) Reject!ExprPtr {
    _ = _ty_name;
    var structure_ty = try infer(self, structure, flag);
    structure_ty = whnf(self, structure_ty);
    const structure_ty_is_prop = isProposition(self, structure_ty)[0];
    const uca = expr.unfoldConstApps(self.ctx.bump, structure_ty).?;
    const struct_ty_name = uca.name;
    const struct_ty_levels = uca.levels;
    const struct_ty_args = uca.args;

    const ind = env.Env.getInductive(self.env, struct_ty_name).?;
    const inductive_info = ind.info;
    const all_ctor_names = ind.all_ctor_names;
    const num_params = ind.num_params;

    const ctor = env.Env.getConstructor(self.env, all_ctor_names[0]).?;
    const ctor_info = ctor.info;
    var ctor_ty = expr.substDeclarInfoLevels(self.ctx, ctor_info, struct_ty_levels);
    {
        var i: u16 = 0;
        while (i < num_params) : (i += 1) {
            ctor_ty = whnf(self, ctor_ty);
            switch (ctor_ty.asRef().kind) {
                .pi => |p| {
                    ctor_ty = expr.inst(self.ctx, p.body, &.{struct_ty_args.items[@as(usize, i)]});
                },
                else => return reject("ran out of param telescope in projection", .{}),
            }
        }
    }
    {
        var i: usize = 0;
        while (i < idx) : (i += 1) {
            ctor_ty = whnf(self, ctor_ty);
            switch (ctor_ty.asRef().kind) {
                .pi => |p| {
                    if (expr.numLooseBvars(p.body) != 0) {
                        if (structure_ty_is_prop and !isProposition(self, p.binder_type)[0]) {
                            return reject("projection of a non-proof field from a Prop structure", .{});
                        }
                        const arg = TcCtx.mkProj(self.ctx, inductive_info.name, i, structure);
                        ctor_ty = expr.inst(self.ctx, p.body, &.{arg});
                    } else {
                        ctor_ty = p.body;
                    }
                },
                else => return reject("ran out of constructor telescope in projection", .{}),
            }
        }
    }
    const reduced = whnf(self, ctor_ty);
    switch (reduced.asRef().kind) {
        .pi => |p| {
            if (structure_ty_is_prop and !isProposition(self, p.binder_type)[0]) {
                return reject("projection of a non-proof field from a Prop structure", .{});
            }
            return p.binder_type;
        },
        else => return reject("ran out of constructor telescope getting projection field", .{}),
    }
}

pub fn infer(self: *TypeChecker, e: ExprPtr, flag: InferFlag) Reject!ExprPtr {
    if (self.tc_cache.infer_cache_check.get(e)) |cached| {
        return cached;
    }
    if (flag == .InferOnly) {
        if (self.tc_cache.infer_cache_no_check.get(e)) |cached| {
            return cached;
        }
    }
    const r = switch (e.asRef().kind) {
        .local => |l| l.binder_type,
        .@"var" => return reject("loose bvar in infer", .{}),
        .sort => |s| try inferSort(self, s.level, flag),
        .app => try inferApp(self, e, flag),
        .pi => try inferPi(self, e, flag),
        .lambda => try inferLambda(self, e, flag),
        .let => |l| try inferLet(self, l.data.binder_type, l.data.val, l.data.body, flag),
        .@"const" => |c| try inferConst(self, c.name, c.levels, flag),
        .proj => |p| try inferProj(self, p.ty_name, p.idx, p.structure, flag),
        .nat_lit => blk: {
            util.assert(self.ctx.export_file.config.nat_extension);
            break :blk expr.natType(self.ctx).?;
        },
        .string_lit => blk: {
            util.assert(self.ctx.export_file.config.string_extension);
            break :blk expr.stringType(self.ctx).?;
        },
    };
    switch (flag) {
        .InferOnly => {
            self.tc_cache.infer_cache_no_check.put(util.smp_allocator, e, r) catch util.oom();
        },
        .Check => {
            self.tc_cache.infer_cache_check.put(util.smp_allocator, e, r) catch util.oom();
        },
    }
    return r;
}

fn inferSort(self: *TypeChecker, l: LevelPtr, flag: InferFlag) Reject!ExprPtr {
    if (flag == .Check) {
        if (self.declar_info) |declar_info| {
            if (!level.allUparamsDefined(self.ctx, l, declar_info.uparams)) {
                return reject("universe parameter not declared by the current declaration", .{});
            }
        }
    }
    const out = TcCtx.succ(self.ctx, l);
    return TcCtx.mkSort(self.ctx, out);
}

fn inferApp(self: *TypeChecker, e: ExprPtr, flag: InferFlag) Reject!ExprPtr {
    const ua = expr.unfoldAppsStack(self.ctx.bump, e);
    var fun = ua.fun;
    var args = ua.args;
    var ctx_sfa = std.heap.stackFallback(32 * @sizeOf(ExprPtr), self.arena.backingAllocator());
    const ctx_a = ctx_sfa.get();
    var ctx = std.ArrayList(ExprPtr).empty;
    defer ctx.deinit(ctx_a);
    fun = try infer(self, fun, flag);
    while (args.items.len != 0) {
        switch (fun.asRef().kind) {
            .pi => |p| {
                const arg = args.pop().?;
                if (flag == .Check) {
                    const arg_type = try infer(self, arg, flag);
                    const binder_type = expr.inst(self.ctx, p.binder_type, ctx.items);
                    try assertDefEq(self, binder_type, arg_type);
                }
                ctx.append(ctx_a, arg) catch util.oom();
                fun = p.body;
            },
            else => {
                var as_pi = expr.inst(self.ctx, fun, ctx.items);
                as_pi = try ensurePi(self, as_pi);
                switch (as_pi.asRef().kind) {
                    .pi => {
                        ctx.clearRetainingCapacity();
                        fun = as_pi;
                    },
                    else => unreachable,
                }
            },
        }
    }
    return expr.inst(self.ctx, fun, ctx.items);
}

fn inferLambda(self: *TypeChecker, e_in: ExprPtr, flag: InferFlag) Reject!ExprPtr {
    var e = e_in;
    var locals_sfa = std.heap.stackFallback(32 * @sizeOf(ExprPtr), self.arena.backingAllocator());
    const locals_a = locals_sfa.get();
    var locals = std.ArrayList(ExprPtr).empty;
    defer locals.deinit(locals_a);
    const start_pos = self.ctx.dbj_level_counter;
    while (true) {
        switch (e.asRef().kind) {
            .lambda => |la| {
                const binder_type = expr.inst(self.ctx, la.binder_type, locals.items);
                if (flag == .Check) {
                    _ = try inferSortOf(self, binder_type, flag);
                }
                const local = TcCtx.mkDbjLevel(self.ctx, la.binder_name, la.binder_style, binder_type);
                locals.append(locals_a, local) catch util.oom();
                e = la.body;
            },
            else => break,
        }
    }

    const instd = expr.inst(self.ctx, e, locals.items);
    const infd = try infer(self, instd, flag);
    var abstrd = expr.abstrLevels(self.ctx, infd, start_pos);
    while (locals.pop()) |local| {
        switch (local.asRef().kind) {
            .local => |l| {
                TcCtx.replaceDbjLevel(self.ctx, local);
                const t = expr.abstrLevels(self.ctx, l.binder_type, start_pos);
                abstrd = TcCtx.mkPi(self.ctx, l.binder_name, l.binder_style, t, abstrd);
            },
            else => unreachable,
        }
    }
    return abstrd;
}

fn inferPi(self: *TypeChecker, e_in: ExprPtr, flag: InferFlag) Reject!ExprPtr {
    var e = e_in;
    var universes_sfa = std.heap.stackFallback(32 * @sizeOf(LevelPtr), self.arena.backingAllocator());
    const universes_a = universes_sfa.get();
    var universes = std.ArrayList(LevelPtr).empty;
    defer universes.deinit(universes_a);
    var locals_sfa = std.heap.stackFallback(32 * @sizeOf(ExprPtr), self.arena.backingAllocator());
    const locals_a = locals_sfa.get();
    var locals = std.ArrayList(ExprPtr).empty;
    defer locals.deinit(locals_a);
    const c0 = self.ctx.dbj_level_counter;
    while (true) {
        switch (e.asRef().kind) {
            .pi => |p| {
                const binder_type = expr.inst(self.ctx, p.binder_type, locals.items);
                const dom_univ = try inferSortOf(self, binder_type, flag);
                universes.append(universes_a, dom_univ) catch util.oom();
                locals.append(locals_a, TcCtx.mkDbjLevel(self.ctx, p.binder_name, p.binder_style, binder_type)) catch util.oom();
                e = p.body;
            },
            else => break,
        }
    }
    const instd = expr.inst(self.ctx, e, locals.items);
    var infd = try inferSortOf(self, instd, flag);
    while (true) {
        const universe = universes.pop();
        const local = locals.pop();
        if (universe == null or local == null) break;
        infd = TcCtx.imax(self.ctx, universe.?, infd);
        TcCtx.replaceDbjLevel(self.ctx, local.?);
    }
    util.assert(c0 == self.ctx.dbj_level_counter);
    return TcCtx.mkSort(self.ctx, infd);
}

fn inferLet(
    self: *TypeChecker,
    binder_type: ExprPtr,
    val: ExprPtr,
    body_in: ExprPtr,
    flag: InferFlag,
) Reject!ExprPtr {
    if (flag == .Check) {
        _ = try inferSortOf(self, binder_type, flag);
        const val_ty = try infer(self, val, flag);
        try assertDefEq(self, val_ty, binder_type);
    }
    const body = expr.inst(self.ctx, body_in, &.{val});
    return try infer(self, body, flag);
}

pub fn whnf(self: *TypeChecker, e: ExprPtr) ExprPtr {
    switch (e.asRef().kind) {
        .nat_lit, .string_lit => return e,
        else => {},
    }
    if (self.tc_cache.whnf_cache.get(e)) |cached| {
        return cached;
    }
    var cursor = e;
    while (true) {
        const whnfd = whnfNoUnfolding(self, cursor);
        if (tryReduceNat(self, whnfd)) |reduce_nat_ok| {
            cursor = reduce_nat_ok;
        } else if (unfoldDef(self, whnfd)) |next_term| {
            cursor = next_term;
        } else {
            self.tc_cache.whnf_cache.put(util.smp_allocator, e, whnfd) catch util.oom();
            return whnfd;
        }
    }
}

pub fn whnfNoUnfolding(self: *TypeChecker, e: ExprPtr) ExprPtr {
    if (self.tc_cache.whnf_no_unfolding_cache.get(e)) |cached| {
        return cached;
    }
    const ua = expr.unfoldApps(self.ctx.bump, e);
    const e_fun = ua.fun;
    const args = ua.args;
    var should_cache = false;
    var eprime: ExprPtr = undefined;
    switch (e_fun.asRef().kind) {
        .proj => |p| {
            if (reduceProj(self, p.idx, p.structure)) |re| {
                const folded = expr.foldlApps(self.ctx, re, args.items);
                const w = whnfNoUnfolding(self, folded);
                should_cache = true;
                eprime = w;
            } else {
                should_cache = false;
                eprime = expr.foldlApps(self.ctx, e_fun, args.items);
            }
        },
        .sort => |s| {
            std.debug.assert(args.items.len == 0);
            const lvl = level.simplify(self.ctx, s.level);
            should_cache = false;
            eprime = TcCtx.mkSort(self.ctx, lvl);
        },
        .lambda => {
            if (args.items.len != 0) {
                var ee = e_fun;
                var n_args: usize = 0;
                while (true) {
                    if (n_args >= args.items.len) break;
                    switch (ee.asRef().kind) {
                        .lambda => |la| {
                            n_args += 1;
                            ee = la.body;
                        },
                        else => break,
                    }
                }
                ee = expr.inst(self.ctx, ee, args.items[0..n_args]);
                ee = expr.foldlApps(self.ctx, ee, args.items[n_args..]);
                should_cache = true;
                eprime = whnfNoUnfolding(self, ee);
            } else {
                std.debug.assert(args.items.len == 0);
                should_cache = false;
                eprime = expr.foldlApps(self.ctx, e_fun, args.items);
            }
        },
        .let => |l| {
            var ee = expr.inst(self.ctx, l.data.body, &.{l.data.val});
            ee = expr.foldlApps(self.ctx, ee, args.items);
            should_cache = true;
            eprime = whnfNoUnfolding(self, ee);
        },
        .@"const" => |c| {
            if (reduceQuot(self, c.name, args.items)) |reduced| {
                should_cache = true;
                eprime = whnfNoUnfolding(self, reduced);
            } else if (reduceRec(self, c.name, c.levels, args.items)) |reduced| {
                should_cache = true;
                eprime = whnfNoUnfolding(self, reduced);
            } else {
                should_cache = false;
                eprime = expr.foldlApps(self.ctx, e_fun, args.items);
            }
        },
        .@"var" => @panic("Loose bvars are not allowed"),
        .pi => {
            std.debug.assert(args.items.len == 0);
            should_cache = false;
            eprime = e_fun;
        },
        .app => unreachable,
        .local, .nat_lit, .string_lit => {
            should_cache = false;
            eprime = expr.foldlApps(self.ctx, e_fun, args.items);
        },
    }
    if (should_cache) {
        self.tc_cache.whnf_no_unfolding_cache.put(util.smp_allocator, e, eprime) catch util.oom();
    }
    return eprime;
}

pub fn assertDefEq(self: *TypeChecker, u: ExprPtr, v: ExprPtr) Reject!void {
    if (!defEq(self, u, v, false)) {
        return reject("def_eq failed", .{});
    }
}

pub fn defEq(self: *TypeChecker, x: ExprPtr, y: ExprPtr, skip_prop_check: bool) bool {
    if (x == y) {
        return true;
    }
    if (self.tc_cache.eq_cache.checkUfEq(x, y)) {
        return true;
    }
    if (!skip_prop_check and proofIrrelEq(self, x, y, skip_prop_check)) {
        self.tc_cache.eq_cache.unite(x, y);
        return true;
    }
    const r = conv.defEqCore(self, x, y);
    if (r) {
        self.tc_cache.eq_cache.unite(x, y);
    }
    return r;
}

fn mkNullaryCtor(self: *TypeChecker, e: ExprPtr, num_params: usize) ?ExprPtr {
    const uca = expr.unfoldConstApps(self.ctx.bump, e) orelse return null;
    const name = uca.name;
    const levels = uca.levels;
    const args = uca.args;
    const ind = env.Env.getInductive(self.env, name) orelse return null;
    const ctor_name = ind.all_ctor_names[0];
    const new_const = TcCtx.mkConst(self.ctx, ctor_name, levels);
    const take = @min(num_params, args.items.len);
    return expr.foldlApps(self.ctx, new_const, args.items[0..take]);
}

fn toCtorWhenK(self: *TypeChecker, major: ExprPtr, rec: *const RecursorData) ?ExprPtr {
    if (!rec.is_k) {
        return null;
    }
    const major_ty = inferThenWhnf(self, major, .InferOnly) catch @panic("infer failed in K-reduction");
    const f = expr.unfoldAppsFun(major_ty);
    switch (f.asRef().kind) {
        .@"const" => |c| {
            const n = expr.getMajorInduct(rec);
            if (n != null and c.name == n.?) {
                const new_ctor_app = mkNullaryCtor(self, major_ty, @as(usize, rec.num_params)) orelse return null;
                const new_type = infer(self, new_ctor_app, .InferOnly) catch @panic("infer failed in K-reduction");
                if (defEq(self, major_ty, new_type, false)) {
                    return new_ctor_app;
                } else {
                    return null;
                }
            }
            return null;
        },
        else => return null,
    }
}

fn isCtorApp(self: *const TypeChecker, e: ExprPtr) ?NamePtr {
    switch (expr.unfoldAppsFun(e).asRef().kind) {
        .@"const" => |c| {
            if (env.Env.getDeclar(self.env, c.name)) |d| {
                if (d.* == .constructor) {
                    return c.name;
                }
            }
        },
        else => {},
    }
    return null;
}

fn iotaTryEtaStruct(self: *TypeChecker, ind_name: NamePtr, e: ExprPtr) ExprPtr {
    if ((!env.Env.canBeStruct(self.env, ind_name)) or isCtorApp(self, e) != null) {
        return e;
    } else {
        const e_type = inferThenWhnf(self, e, .InferOnly) catch @panic("infer failed in eta-struct");
        const e_type_f = expr.unfoldAppsFun(e_type);
        switch (e_type_f.asRef().kind) {
            .@"const" => |c| {
                if (c.name == ind_name) {
                    const e_sort = inferThenWhnf(self, e_type, .InferOnly) catch @panic("infer failed in eta-struct");
                    if (e_sort == expr.prop(self.ctx)) {
                        return e;
                    } else {
                        return expandEtaStructAux(self, e_type, e) orelse e;
                    }
                }
                return e;
            },
            else => return e,
        }
    }
}

fn reduceRec(
    self: *TypeChecker,
    const_name: NamePtr,
    const_levels: LevelsPtr,
    args: []const ExprPtr,
) ?ExprPtr {
    const rec = env.Env.getRecursor(self.env, const_name) orelse return null;
    const info = rec.info;
    const rec_rules = rec.rec_rules;
    const num_params = rec.num_params;
    const num_motives = rec.num_motives;
    const num_minors = rec.num_minors;
    if (rec.majorIdx() >= args.len) return null;
    var major = args[rec.majorIdx()];
    major = toCtorWhenK(self, major, rec) orelse major;
    major = whnf(self, major);
    switch (major.asRef().kind) {
        .nat_lit => |nl| major = expr.natLitToConstructor(self.ctx, nl.ptr) orelse major,
        .string_lit => |sl| major = strLitToCtorReducing(self, sl.ptr) orelse major,
        else => {
            const ind_rec_name_prefix = expr.getMajorInduct(rec).?;
            major = iotaTryEtaStruct(self, ind_rec_name_prefix, major);
        },
    }
    const mua = expr.unfoldApps(self.ctx.bump, major);
    const major_ctor = mua.fun;
    const major_ctor_args = mua.args;
    const rec_rule = getRecRule(rec_rules, major_ctor) orelse return null;

    const num_extra_params_to_major = std.math.sub(usize, major_ctor_args.items.len, @as(usize, rec_rule.ctor_telescope_size_wo_params)) catch unreachable;
    const major_ctor_args_wo_params = major_ctor_args.items[num_extra_params_to_major..];
    var r = expr.substExprLevels(self.ctx, rec_rule.val, info.uparams, const_levels);
    const take = @min(@as(usize, num_params + num_motives + num_minors), args.len);
    r = expr.foldlApps(self.ctx, r, args[0..take]);
    r = expr.foldlApps(self.ctx, r, major_ctor_args_wo_params);
    return expr.foldlApps(self.ctx, r, args[rec.majorIdx() + 1 ..]);
}

pub fn reduceQuot(self: *TypeChecker, c_name: NamePtr, args: []const ExprPtr) ?ExprPtr {
    if (env.Env.getDeclar(self.env, c_name)) |d| {
        if (d.* != .quot) return null;
    } else {
        return null;
    }
    const name_cache = self.ctx.export_file.name_cache;
    var qmk: ExprPtr = undefined;
    var rest_idx: usize = undefined;
    if (name_cache.quot_lift != null and c_name == name_cache.quot_lift.?) {
        if (args.len <= 5) return null;
        qmk = whnf(self, args[5]);
        rest_idx = 6;
    } else if (name_cache.quot_ind != null and c_name == name_cache.quot_ind.?) {
        if (args.len <= 4) return null;
        qmk = whnf(self, args[4]);
        rest_idx = 5;
    } else {
        return null;
    }
    {
        const qua = expr.unfoldApps(self.ctx.bump, qmk);
        const qmk_const = qua.fun;
        const qmk_args = qua.args;
        switch (qmk_const.asRef().kind) {
            .@"const" => |c| {
                if (!(name_cache.quot_mk != null and c.name == name_cache.quot_mk.? and qmk_args.items.len == 3)) {
                    return null;
                }
            },
            else => return null,
        }
    }
    if (args.len <= 3) return null;
    const f = args[3];
    const appd = switch (qmk.asRef().kind) {
        .app => |a| TcCtx.mkApp(self.ctx, f, a.arg),
        else => @panic("Quot iota"),
    };
    return expr.foldlApps(self.ctx, appd, args[rest_idx..]);
}

fn unfoldDef(self: *TypeChecker, e: ExprPtr) ?ExprPtr {
    const ua = expr.unfoldApps(self.ctx.bump, e);
    const fun = ua.fun;
    const args = ua.args;
    const ci = expr.tryConstInfo(fun) orelse return null;
    const name = ci[0];
    const levels = ci[1];
    const dv = env.Env.getDeclarVal(self.env, name) orelse return null;
    const def_uparams = dv[0];
    const def_value = dv[1];
    if (levels.asRef().len == def_uparams.asRef().len) {
        const def_val = expr.substExprLevels(self.ctx, def_value, def_uparams, levels);
        return expr.foldlApps(self.ctx, def_val, args.items);
    } else {
        return null;
    }
}

pub fn isSortZero(self: *TypeChecker, e_in: ExprPtr) bool {
    const e = whnf(self, e_in);
    switch (e.asRef().kind) {
        .sort => |s| return s.level.asRef().kind == .zero,
        else => return false,
    }
}

pub fn isProposition(self: *TypeChecker, e: ExprPtr) struct { bool, ExprPtr } {
    const infd = infer(self, e, .InferOnly) catch @panic("infer failed in conversion");
    return .{ isSortZero(self, infd), infd };
}

pub fn isProof(self: *TypeChecker, e: ExprPtr) struct { bool, ExprPtr } {
    const infd = infer(self, e, .InferOnly) catch @panic("infer failed in conversion");
    return .{ isProposition(self, infd)[0], infd };
}

fn proofIrrelEq(self: *TypeChecker, x: ExprPtr, y: ExprPtr, skip_prop_check: bool) bool {
    const px = isProof(self, x);
    if (!px[0]) return false;
    const l_type = px[1];
    const py = isProof(self, y);
    if (!py[0]) return false;
    const r_type = py[1];
    return skip_prop_check or defEq(self, l_type, r_type, false);
}
