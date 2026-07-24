const std = @import("std");
const name_mod = @import("name.zig");
const level = @import("level.zig");
const env = @import("env.zig");
const expr = @import("expr.zig");
const tc = @import("tc.zig");
const util = @import("util.zig");
const name = @import("name.zig");
const Arena = @import("Arena.zig");

const ConstructorData = env.ConstructorData;
const Declar = env.Declar;
const DeclarInfo = env.DeclarInfo;
const DeclarMap = env.DeclarMap;
const InductiveData = env.InductiveData;
const RecRule = env.RecRule;
const RecursorData = env.RecursorData;
const EnvLimit = env.EnvLimit;
const Env = env.Env;

const BinderStyle = expr.BinderStyle;
const Expr = expr.Expr;

const InferFlag = tc.InferFlag;
const TypeChecker = tc.TypeChecker;

const ExportFile = @import("export_file.zig").ExportFile;
const ExprPtr = @import("ptr.zig").ExprPtr;
const swiss_map = @import("swiss_map.zig");
const FxIndexMap = swiss_map.FxIndexMap;
const LevelPtr = @import("ptr.zig").LevelPtr;
const LevelsPtr = @import("ptr.zig").LevelsPtr;
const NamePtr = @import("ptr.zig").NamePtr;
const TcCtx = @import("TcCtx.zig");

fn u16TryFrom(x: usize) u16 {
    if (x > std.math.maxInt(u16)) @panic("u16 overflow");
    return @intCast(x);
}

pub fn checkInductiveDeclar(self: *const ExportFile, d: *const Declar) void {
    const ind: *const InductiveData, const env_limit: EnvLimit = switch (d.*) {
        .inductive => |*i| blk: {
            const start, const size = self.mutual_block_sizes.get(i.info.name).?;
            break :blk .{ i, EnvLimit{ .by_index = start + size } };
        },
        else => @panic("expected inductive"),
    };
    checkInductiveDeclarChecked(self, d, ind, env_limit) catch tc.fail();
}

fn checkInductiveDeclarChecked(
    self: *const ExportFile,
    d: *const Declar,
    ind: *const InductiveData,
    env_limit: EnvLimit,
) tc.Reject!void {
    var ar = Arena.init(util.smp_allocator);
    defer ar.deinit();
    var ctx = TcCtx.init(self, &ar);
    defer TcCtx.deinit(&ctx);

    const unmodified_tys_ctors = blk: {
        var e = self.newEnv(env_limit);
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var tcr = TypeChecker.init(&ctx, &e, &ar, null, &cache);
        defer tcr.deinit();
        try tc.checkDeclarInfo(&tcr, d);
        break :blk collectUnmodifiedMutuals(&tcr, ind);
    };

    var st = blk: {
        var e = self.newEnv(env_limit);
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var tcr = TypeChecker.init(&ctx, &e, &ar, null, &cache);
        defer tcr.deinit();
        break :blk try specializeNested(&tcr, ind, cloneHeaders(&tcr, unmodified_tys_ctors));
    };

    {
        var e = self.newEnv(env_limit);
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var tcr = TypeChecker.init(&ctx, &e, &ar, null, &cache);
        defer tcr.deinit();
        try checkInductiveSpecs(&tcr, &st);
    }

    const ind_ty_ext1 = mkIndTysEnvExt(&ctx, &st);

    {
        var e = env.Env.initWithTempExt(&self.declars, &ind_ty_ext1, env_limit);
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var tcr = TypeChecker.init(&ctx, &e, &ar, null, &cache);
        defer tcr.deinit();
        for (st.all_inductives_incl_specialized.items) |*ind_| {
            for (ind_.ctors.items) |ctor| {
                try checkCtor(&tcr, &st, ind_.name, ctor.ty);
            }
        }
    }

    const ctor_extension = mkCtorsEnvExt(&ctx, &st, ind_ty_ext1);

    const recursors = blk: {
        var e = env.Env.initWithTempExt(&self.declars, &ctor_extension, env_limit);
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var tcr = TypeChecker.init(&ctx, &e, &ar, null, &cache);
        defer tcr.deinit();
        try mkElimLevel(&tcr, &st);
        initKTarget(&st);
        mkMajors(&tcr, &st);
        mkMotives(&tcr, &st);
        try mkMinors(&tcr, &st);
        break :blk try mkRecursors(&tcr, &st);
    };

    var recursor_extension = ctor_extension;
    for (recursors.items) |r| {
        recursor_extension.put(ctx.bump, Declar.info(&r).name, r) catch util.oom();
    }

    {
        var e = env.Env.initWithTempExt(&self.declars, &recursor_extension, env_limit);
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var tcr = TypeChecker.init(&ctx, &e, &ar, null, &cache);
        defer tcr.deinit();
        if (isNested(&st)) {
            try restoreAndCheck(&tcr, &st, &unmodified_tys_ctors, ind.all_ind_names);
        } else {
            try assertNonnestedTysDefEq(&tcr, ind, &st);
            try assertNonnestedCtorsDefEq(&tcr, &st);
            try assertNonnestedRecursorsDefEq(&tcr, &st, &recursors);
        }
    }
}

pub fn mkIndTysEnvExt(ctx: *TcCtx, st: *const InductiveCheckState) DeclarMap {
    const is_nested_ = st.nested_to_unspecialized_ty_nofvars.count() != 0;
    var all_ind_names = std.ArrayList(NamePtr).empty;
    for (st.all_inductives_incl_specialized.items) |x| {
        all_ind_names.append(ctx.bump, x.name) catch util.oom();
    }
    const all_ind_names_arc = all_ind_names.items;
    var env_extension = swiss_map.FxIndexMap(NamePtr, Declar).empty;
    for (st.all_inductives_incl_specialized.items, 0..) |inductive, idx| {
        const t = Declar{ .inductive = InductiveData{
            .info = DeclarInfo{ .name = inductive.name, .ty = inductive.ty, .uparams = st.uparams },
            .is_nested = is_nested_,
            .is_recursive = false,
            .num_params = u16TryFrom(st.local_params.items.len),
            .num_indices = u16TryFrom(st.local_indices.items[idx].items.len),
            .all_ind_names = all_ind_names_arc,
            .all_ctor_names = ctorNamesArc(ctx, inductive),
        } };
        env_extension.put(ctx.bump, inductive.name, t) catch util.oom();
    }
    return env_extension;
}

fn ctorNamesArc(ctx: *TcCtx, inductive: IndTyHeader) []const NamePtr {
    var names = std.ArrayList(NamePtr).empty;
    for (inductive.ctors.items) |x| {
        names.append(ctx.bump, x.name) catch util.oom();
    }
    return names.items;
}

pub fn mkCtorsEnvExt(ctx: *TcCtx, nest_st: *const InductiveCheckState, env_ext_in: DeclarMap) DeclarMap {
    var env_ext = env_ext_in;
    for (nest_st.all_inductives_incl_specialized.items) |inductive| {
        for (inductive.ctors.items, 0..) |ctor, idx| {
            const info = DeclarInfo{ .name = ctor.name, .ty = ctor.ty, .uparams = nest_st.uparams };
            const num_params = u16TryFrom(nest_st.local_params.items.len);
            const num_fields = expr.piTelescopeSize(ctor.ty) - num_params;
            const d = Declar{ .constructor = ConstructorData{
                .info = info,
                .inductive_name = inductive.name,
                .ctor_idx = u16TryFrom(idx),
                .num_params = num_params,
                .num_fields = num_fields,
            } };
            env_ext.put(ctx.bump, ctor.name, d) catch util.oom();
        }
    }
    return env_ext;
}

pub const InductiveCheckState = struct {
    nested_to_unspecialized_ty_wfvars: FxIndexMap(NamePtr, ExprPtr),
    nested_to_unspecialized_ty_nofvars: FxIndexMap(NamePtr, ExprPtr),
    uparams: LevelsPtr,
    num_params: u16,
    all_inductives_incl_specialized: std.ArrayList(IndTyHeader),
    next_ngen_idx: u64,
    local_params: std.ArrayList(ExprPtr),
    local_indices: std.ArrayList(std.ArrayList(ExprPtr)),
    block_codom: ?LevelPtr,
    is_zero: ?bool,
    is_nonzero: ?bool,
    ind_consts: std.ArrayList(ExprPtr),
    rec_uparams: ?LevelsPtr,
    elim_level: ?LevelPtr,
    k_target: ?bool,
    majors: std.ArrayList(ExprPtr),
    motives: std.ArrayList(ExprPtr),
    minors: std.ArrayList(std.ArrayList(ExprPtr)),
};

fn newState(
    info_uparams: LevelsPtr,
    num_params: u16,
    new_tys: std.ArrayList(IndTyHeader),
    local_params: std.ArrayList(ExprPtr),
) InductiveCheckState {
    return InductiveCheckState{
        .nested_to_unspecialized_ty_wfvars = swiss_map.FxIndexMap(NamePtr, ExprPtr).empty,
        .nested_to_unspecialized_ty_nofvars = swiss_map.FxIndexMap(NamePtr, ExprPtr).empty,
        .uparams = info_uparams,
        .num_params = num_params,
        .all_inductives_incl_specialized = new_tys,
        .next_ngen_idx = 1,
        .local_params = local_params,
        .local_indices = std.ArrayList(std.ArrayList(ExprPtr)).empty,
        .block_codom = null,
        .is_zero = null,
        .is_nonzero = null,
        .ind_consts = std.ArrayList(ExprPtr).empty,
        .rec_uparams = null,
        .elim_level = null,
        .k_target = null,
        .majors = std.ArrayList(ExprPtr).empty,
        .motives = std.ArrayList(ExprPtr).empty,
        .minors = std.ArrayList(std.ArrayList(ExprPtr)).empty,
    };
}

fn isNested(self: *const InductiveCheckState) bool {
    return self.nested_to_unspecialized_ty_nofvars.count() != 0;
}

pub const IndTyHeader = struct {
    name: NamePtr,
    ty: ExprPtr,
    ctors: std.ArrayList(CtorHeader),
};

pub const CtorHeader = struct {
    name: NamePtr,
    ty: ExprPtr,
};

fn cloneHeader(ctx: *TcCtx, h: IndTyHeader) IndTyHeader {
    var ctors = std.ArrayList(CtorHeader).empty;
    ctors.appendSlice(ctx.bump, h.ctors.items) catch util.oom();
    return IndTyHeader{ .name = h.name, .ty = h.ty, .ctors = ctors };
}

fn cloneHeaders(self: *TypeChecker, hs: std.ArrayList(IndTyHeader)) std.ArrayList(IndTyHeader) {
    var out = std.ArrayList(IndTyHeader).empty;
    for (hs.items) |h| {
        out.append(self.ctx.bump, cloneHeader(self.ctx, h)) catch util.oom();
    }
    return out;
}

fn ctorAppParamsOk(ctor_apps: []const ExprPtr, local_params: []const ExprPtr) bool {
    if (ctor_apps.len < local_params.len) {
        return false;
    }
    var i: usize = 0;
    while (i < local_params.len) : (i += 1) {
        if (ctor_apps[i] != local_params[i]) {
            return false;
        }
    }
    return true;
}

fn specializeNested(
    self: *TypeChecker,
    t_from_file: *const InductiveData,
    unmodified_tys_ctors: std.ArrayList(IndTyHeader),
) tc.Reject!InductiveCheckState {
    const lp = try getLocalParams(self, unmodified_tys_ctors.items[0].ty, t_from_file.num_params);
    const local_params = lp[0];

    var st = newState(
        t_from_file.info.uparams,
        u16TryFrom(local_params.items.len),
        unmodified_tys_ctors,
        local_params,
    );
    try specializeNestedAux(self, &st);

    for (st.all_inductives_incl_specialized.items) |ind| {
        util.assert(!ind.ty.hasFvars());
        for (ind.ctors.items) |c| {
            util.assert(!c.ty.hasFvars());
        }
    }
    return st;
}

fn specializeNestedAux(self: *TypeChecker, st: *InductiveCheckState) tc.Reject!void {
    var i: usize = 0;
    while (i < st.all_inductives_incl_specialized.items.len) {
        var new_ctors_for_i = std.ArrayList(CtorHeader).empty;
        const cloned = cloneHeader(self.ctx, st.all_inductives_incl_specialized.items[i]);
        for (cloned.ctors.items) |adjusted_ctor| {
            const glp = try getLocalParams(self, adjusted_ctor.ty, u16TryFrom(st.local_params.items.len));
            const ctor_local_params = glp[0];
            const ctor_type_instd = glp[1];
            const replaced_ctor_wo_params = try replaceAllNested(self, ctor_type_instd, st, &ctor_local_params);
            const replaced_ctor_w_params = expr.abstrPis(self.ctx, ctor_local_params.items, replaced_ctor_wo_params);
            util.assert(!replaced_ctor_w_params.hasFvars());
            new_ctors_for_i.append(self.ctx.bump, CtorHeader{ .name = adjusted_ctor.name, .ty = replaced_ctor_w_params }) catch util.oom();
        }
        if (i < st.all_inductives_incl_specialized.items.len) {
            st.all_inductives_incl_specialized.items[i].ctors = new_ctors_for_i;
        } else {
            return tc.reject("inductive type is missing", .{});
        }
        i += 1;
    }

    st.nested_to_unspecialized_ty_nofvars = blk: {
        var out = swiss_map.FxIndexMap(NamePtr, ExprPtr).empty;
        var it = st.nested_to_unspecialized_ty_wfvars.iterator();
        while (it.next()) |entry| {
            const e = expr.abstr(self.ctx, entry.value_ptr.*, st.local_params.items);
            out.put(self.ctx.bump, entry.key_ptr.*, e) catch util.oom();
        }
        break :blk out;
    };
}

fn getLocalParams(self: *TypeChecker, e_in: ExprPtr, num_params: u16) tc.Reject!struct { std.ArrayList(ExprPtr), ExprPtr } {
    var e = e_in;
    var param_locals = std.ArrayList(ExprPtr).empty;
    param_locals.ensureTotalCapacity(self.ctx.bump, num_params) catch util.oom();
    var i: u16 = 0;
    while (i < num_params) : (i += 1) {
        switch (e.asRef().kind) {
            .pi => |pi| {
                const local_ = TcCtx.mkUnique(self.ctx, pi.binder_name, pi.binder_style, pi.binder_type);
                e = expr.inst(self.ctx, pi.body, &.{local_});
                e = tc.whnf(self, e);
                param_locals.append(self.ctx.bump, local_) catch util.oom();
            },
            else => return tc.reject("exhausted telescope early", .{}),
        }
    }
    return .{ param_locals, e };
}

fn checkInductiveSpec0th(self: *TypeChecker, uparams: LevelsPtr, st: *InductiveCheckState) tc.Reject!void {
    self.tc_cache.clear();
    const ind0 = st.all_inductives_incl_specialized.items[0];
    const ind_name = ind0.name;
    var ind_ty_cursor = ind0.ty;
    ind_ty_cursor = tc.whnf(self, ind_ty_cursor);
    var indices_locals = std.ArrayList(ExprPtr).empty;
    var i: usize = 0;
    while (ind_ty_cursor.asRef().kind == .pi) {
        const pi = ind_ty_cursor.asRef().kind.pi;
        if (i < st.local_params.items.len) {
            const local_ = st.local_params.items[i];
            switch (local_.asRef().kind) {
                .local => |lc| {
                    self.tc_cache.clear();
                    try tc.assertDefEq(self, pi.binder_type, lc.binder_type);
                },
                else => return tc.reject("malformed inductive type", .{}),
            }
            ind_ty_cursor = expr.inst(self.ctx, pi.body, &.{st.local_params.items[i]});
            ind_ty_cursor = tc.whnf(self, ind_ty_cursor);
        } else {
            const local_ = TcCtx.mkUnique(self.ctx, pi.binder_name, pi.binder_style, pi.binder_type);
            ind_ty_cursor = expr.inst(self.ctx, pi.body, &.{local_});
            ind_ty_cursor = tc.whnf(self, ind_ty_cursor);
            indices_locals.append(self.ctx.bump, local_) catch util.oom();
        }
        i += 1;
    }
    const block_codom = try tc.ensureSort(self, ind_ty_cursor);
    const is_nonzero_ = level.isNonzero(self.ctx, block_codom);
    const is_zero_ = level.isZero(self.ctx, block_codom);
    const ind_const = TcCtx.mkConst(self.ctx, ind_name, uparams);

    st.local_indices.append(self.ctx.bump, indices_locals) catch util.oom();
    st.block_codom = block_codom;
    st.is_zero = is_zero_;
    st.is_nonzero = is_nonzero_;
    st.ind_consts.append(self.ctx.bump, ind_const) catch util.oom();
}

fn checkInductiveSpecsMutual1(self: *TypeChecker, st: *InductiveCheckState, ind: IndTyHeader) tc.Reject!void {
    self.tc_cache.clear();
    var ind_ty_cursor = tc.whnf(self, ind.ty);
    var indices_locals = std.ArrayList(ExprPtr).empty;
    var i: usize = 0;
    while (ind_ty_cursor.asRef().kind == .pi) {
        const pi = ind_ty_cursor.asRef().kind.pi;
        if (i < st.local_params.items.len) {
            ind_ty_cursor = expr.inst(self.ctx, pi.body, &.{st.local_params.items[i]});
            ind_ty_cursor = tc.whnf(self, ind_ty_cursor);
        } else {
            const local_ = TcCtx.mkUnique(self.ctx, pi.binder_name, pi.binder_style, pi.binder_type);
            ind_ty_cursor = expr.inst(self.ctx, pi.body, &.{local_});
            ind_ty_cursor = tc.whnf(self, ind_ty_cursor);
            indices_locals.append(self.ctx.bump, local_) catch util.oom();
        }
        i += 1;
    }
    const codom_level = try tc.ensureSort(self, ind_ty_cursor);
    util.assert(level.eqAntisymm(self.ctx, codom_level, st.block_codom.?));
    st.local_indices.append(self.ctx.bump, indices_locals) catch util.oom();
    st.ind_consts.append(self.ctx.bump, TcCtx.mkConst(self.ctx, ind.name, st.uparams)) catch util.oom();
}

fn checkInductiveSpecs(self: *TypeChecker, st: *InductiveCheckState) tc.Reject!void {
    const nbefore = st.all_inductives_incl_specialized.items.len;
    var i: usize = 0;
    while (i < st.all_inductives_incl_specialized.items.len) : (i += 1) {
        if (i == 0) {
            try checkInductiveSpec0th(self, st.uparams, st);
            util.assert(st.local_indices.items.len == 1);
        } else {
            util.assert(st.local_indices.items.len == i);
            try checkInductiveSpecsMutual1(self, st, cloneHeader(self.ctx, st.all_inductives_incl_specialized.items[i]));
        }
    }
    util.assert(st.all_inductives_incl_specialized.items.len == nbefore);
    util.assert(st.all_inductives_incl_specialized.items.len == st.local_indices.items.len);
}

fn isNestedIndApp(self: *TypeChecker, st: *const InductiveCheckState, e: ExprPtr) tc.Reject!?InductiveData {
    if (e.asRef().kind != .app) {
        return null;
    }
    const unfolded = expr.unfoldConstApps(self.ctx.bump, e) orelse return null;
    const name_ = unfolded.name;
    const args = unfolded.args;
    const ind_ty_declar = Env.getInductive(self.env, name_) orelse return null;
    const num_params = ind_ty_declar.num_params;
    if (@as(usize, num_params) > args.items.len) {
        return null;
    }
    var loose_bvars = false;
    var is_nested_ = false;
    var i: usize = 0;
    while (i < @as(usize, num_params)) : (i += 1) {
        const this_param = args.items[i];
        if (this_param.numLooseBvars() != 0) {
            loose_bvars = true;
        }
        const FindCtx = struct {
            st: *const InductiveCheckState,
            ctx: *TcCtx,
            fn pred(fc: *@This(), nptr: NamePtr) bool {
                for (fc.st.all_inductives_incl_specialized.items) |new_ty| {
                    if (new_ty.name == nptr) return true;
                }
                return false;
            }
        };
        var fc = FindCtx{ .st = st, .ctx = self.ctx };
        if (expr.findConst(self.ctx, this_param, &fc, FindCtx.pred)) {
            is_nested_ = true;
        }
    }
    if (!is_nested_) {
        return null;
    }
    if (loose_bvars) {
        return tc.reject("nested types cannot contain loose bvars", .{});
    }
    return ind_ty_declar.*;
}

fn headerOfCtor(t: *const ConstructorData) CtorHeader {
    return CtorHeader{ .name = t.info.name, .ty = t.info.ty };
}

fn headerOfTy(self: *const TypeChecker, t: *const InductiveData) IndTyHeader {
    var ctors = std.ArrayList(CtorHeader).empty;
    for (t.all_ctor_names) |ctor_name| {
        ctors.append(self.ctx.bump, headerOfCtor(Env.getConstructor(self.env, ctor_name).?)) catch util.oom();
    }
    return IndTyHeader{ .name = t.info.name, .ty = t.info.ty, .ctors = ctors };
}

fn collectUnmodifiedMutuals(self: *const TypeChecker, t_from_file: *const InductiveData) std.ArrayList(IndTyHeader) {
    var all_inductives = std.ArrayList(IndTyHeader).empty;
    for (t_from_file.all_ind_names) |n| {
        const t = Env.getInductive(self.env, n).?;
        all_inductives.append(self.ctx.bump, headerOfTy(self, t)) catch util.oom();
    }
    return all_inductives;
}

fn mkUniqueName(self: *TypeChecker, n: NamePtr, st: *InductiveCheckState) NamePtr {
    var idx: u64 = st.next_ngen_idx;
    while (idx < std.math.maxInt(u64)) : (idx += 1) {
        const tester = name_mod.appendIndexAfter(self.ctx, n, idx);
        if (Env.getOldDeclar(self.env, tester) == null) {
            st.next_ngen_idx = idx + 1;
            return tester;
        }
    }
    @panic("Unable to generate unique name, u64 exhausted");
}

fn replaceIfNested(
    self: *TypeChecker,
    e: ExprPtr,
    st: *InductiveCheckState,
    outgoing_param_locals: []const ExprPtr,
) tc.Reject!?ExprPtr {
    const nested_container_ty = (try isNestedIndApp(self, st, e)) orelse return null;
    const unfolded = expr.unfoldConstApps(self.ctx.bump, e).?;
    const f = unfolded.fun;
    const i_name = unfolded.name;
    const i_levels = unfolded.levels;
    const args = unfolded.args;
    util.assert(@as(usize, nested_container_ty.num_params) <= args.items.len);
    const i_as = expr.foldlApps(self.ctx, f, args.items[0..@as(usize, nested_container_ty.num_params)]);
    const i_params = expr.replaceParams(self.ctx, i_as, st.local_params.items, outgoing_param_locals);

    var found: ?NamePtr = null;
    {
        var it = st.nested_to_unspecialized_ty_wfvars.iterator();
        while (it.next()) |entry| {
            if (entry.value_ptr.* == i_params) {
                found = entry.key_ptr.*;
                break;
            }
        }
    }
    if (found) |aux_i_name| {
        var f2 = TcCtx.mkConst(self.ctx, aux_i_name, st.uparams);
        f2 = expr.foldlApps(self.ctx, f2, outgoing_param_locals);
        f2 = expr.foldlApps(self.ctx, f2, args.items[@as(usize, nested_container_ty.num_params)..args.items.len]);
        return f2;
    } else {
        var result: ?ExprPtr = null;
        for (nested_container_ty.all_ind_names) |nested_container_name| {
            const container = Env.getInductive(self.env, nested_container_name) orelse return null;
            const container_ty_info = container.info;
            const all_nested_container_ctor_names = container.all_ctor_names;
            const js = blk: {
                const base_const = TcCtx.mkConst(self.ctx, nested_container_name, i_levels);
                break :blk expr.foldlApps(self.ctx, base_const, args.items[0..@as(usize, nested_container_ty.num_params)]);
            };

            const aux_nested_container_name = blk: {
                const nested_pfx = TcCtx.str1(self.ctx, "_nested");
                const base = name_mod.concatName(self.ctx, nested_pfx, nested_container_name);
                break :blk mkUniqueName(self, base, st);
            };
            const nested_container_aux_type = blk: {
                const base = expr.substExprLevels(self.ctx, container_ty_info.ty, container_ty_info.uparams, i_levels);
                const instd = expr.instForallParams(self.ctx, base, @as(usize, nested_container_ty.num_params), args.items);
                const out = expr.abstrPis(self.ctx, outgoing_param_locals, instd);
                break :blk out;
            };
            const jsprime = expr.replaceParams(self.ctx, js, st.local_params.items, outgoing_param_locals);
            st.nested_to_unspecialized_ty_wfvars.put(self.ctx.bump, aux_nested_container_name, jsprime) catch util.oom();
            if (nested_container_name == i_name) {
                var f2 = TcCtx.mkConst(self.ctx, aux_nested_container_name, st.uparams);
                f2 = expr.foldlApps(self.ctx, f2, outgoing_param_locals);
                const args2 = args.items[@as(usize, nested_container_ty.num_params)..args.items.len];
                f2 = expr.foldlApps(self.ctx, f2, args2);
                result = f2;
            }
            var auxj_ctors = std.ArrayList(CtorHeader).empty;
            for (all_nested_container_ctor_names) |j_ctor_name| {
                const j_ctor = Env.getConstructor(self.env, j_ctor_name) orelse return null;
                const j_ctor_info = j_ctor.info;
                const auxj_ctor_name = name_mod.replacePfx(self.ctx, j_ctor_name, nested_container_name, aux_nested_container_name);
                var auxj_ctor_type = expr.substExprLevels(self.ctx, j_ctor_info.ty, j_ctor_info.uparams, i_levels);
                auxj_ctor_type = expr.instForallParams(self.ctx, auxj_ctor_type, @as(usize, nested_container_ty.num_params), args.items);
                auxj_ctor_type = expr.abstrPis(self.ctx, outgoing_param_locals, auxj_ctor_type);
                auxj_ctors.append(self.ctx.bump, CtorHeader{ .name = auxj_ctor_name, .ty = auxj_ctor_type }) catch util.oom();
            }
            st.all_inductives_incl_specialized.append(self.ctx.bump, IndTyHeader{
                .name = aux_nested_container_name,
                .ty = nested_container_aux_type,
                .ctors = auxj_ctors,
            }) catch util.oom();
        }
        return result;
    }
}

fn replaceAllNested(
    self: *TypeChecker,
    e: ExprPtr,
    st: *InductiveCheckState,
    outgoing_params: *const std.ArrayList(ExprPtr),
) tc.Reject!ExprPtr {
    if (try replaceIfNested(self, e, st, outgoing_params.items)) |eprime| {
        return eprime;
    } else {
        switch (e.asRef().kind) {
            .@"var", .sort, .@"const", .local, .nat_lit, .string_lit => return e,
            .pi => |pi| {
                const binder_type = try replaceAllNested(self, pi.binder_type, st, outgoing_params);
                const body = try replaceAllNested(self, pi.body, st, outgoing_params);
                return TcCtx.mkPi(self.ctx, pi.binder_name, pi.binder_style, binder_type, body);
            },
            .lambda => |la| {
                const binder_type = try replaceAllNested(self, la.binder_type, st, outgoing_params);
                const body = try replaceAllNested(self, la.body, st, outgoing_params);
                return TcCtx.mkLambda(self.ctx, la.binder_name, la.binder_style, binder_type, body);
            },
            .let => |le| {
                const binder_type = try replaceAllNested(self, le.data.binder_type, st, outgoing_params);
                const val = try replaceAllNested(self, le.data.val, st, outgoing_params);
                const body = try replaceAllNested(self, le.data.body, st, outgoing_params);
                return TcCtx.mkLet(self.ctx, le.data.binder_name, binder_type, val, body, le.data.nondep);
            },
            .app => |ap| {
                const fun = try replaceAllNested(self, ap.fun, st, outgoing_params);
                const arg = try replaceAllNested(self, ap.arg, st, outgoing_params);
                return TcCtx.mkApp(self.ctx, fun, arg);
            },
            .proj => |pr| {
                const structure = try replaceAllNested(self, pr.structure, st, outgoing_params);
                return TcCtx.mkProj(self.ctx, pr.ty_name, pr.idx, structure);
            },
        }
    }
}

fn checkPositivity1(self: *TypeChecker, st: *const InductiveCheckState, ctor_type_cursor_in: ExprPtr) tc.Reject!void {
    var ctor_type_cursor = ctor_type_cursor_in;
    while (true) {
        ctor_type_cursor = tc.whnf(self, ctor_type_cursor);
        if (!hasIndOcc(self, ctor_type_cursor, st.ind_consts.items)) {
            return;
        }
        switch (ctor_type_cursor.asRef().kind) {
            .pi => |pi| {
                if (hasIndOcc(self, pi.binder_type, st.ind_consts.items)) {
                    return tc.reject("non-positive occurrence in inductive", .{});
                }
                const local = TcCtx.mkUnique(self.ctx, pi.binder_name, pi.binder_style, pi.binder_type);
                ctor_type_cursor = expr.inst(self.ctx, pi.body, &.{local});
            },
            else => {
                if ((try whichValidIndApp(self, st, ctor_type_cursor)) == null) {
                    return tc.reject("expected a valid application of an inductive type", .{});
                }
                return;
            },
        }
    }
}

fn isValidIndApp(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    parent_ind_name: NamePtr,
    ind_ty_app: ExprPtr,
) tc.Reject!bool {
    const unfolded = expr.unfoldApps(self.ctx.bump, ind_ty_app);
    const base_const = unfolded.fun;
    const ctor_apps = unfolded.args;
    const ind_name, const appd_levels = switch (base_const.asRef().kind) {
        .@"const" => |co| if (co.name == parent_ind_name) .{ co.name, co.levels } else return false,
        else => return false,
    };
    var ind_name_pos: ?usize = null;
    for (st.ind_consts.items, 0..) |x, idx| {
        const matches = switch (x.asRef().kind) {
            .@"const" => |co| co.name == ind_name,
            else => return tc.reject("malformed constructor type", .{}),
        };
        if (matches) {
            ind_name_pos = idx;
            break;
        }
    }
    const pos = ind_name_pos.?;
    switch (st.ind_consts.items[pos].asRef().kind) {
        .@"const" => |co| {
            const lhs = appd_levels.asRef();
            const rhs = co.levels.asRef();
            if (lhs.len != rhs.len) {
                return false;
            }
            var i: usize = 0;
            while (i < lhs.len) : (i += 1) {
                if (!level.eqAntisymm(self.ctx, lhs[i], rhs[i])) {
                    return false;
                }
            }
        },
        else => return false,
    }
    const ind_name_num_indices = st.local_indices.items[pos].items.len;

    if (ctor_apps.items.len != (st.local_params.items.len + ind_name_num_indices)) {
        return false;
    }
    for (ctor_apps.items[st.local_params.items.len..]) |index_app| {
        if (hasIndOcc(self, index_app, st.ind_consts.items)) {
            return false;
        }
    }
    return ctorAppParamsOk(ctor_apps.items, st.local_params.items);
}

fn hasIndOcc(self: *TypeChecker, e: ExprPtr, haystack: []const ExprPtr) bool {
    const FindCtx = struct {
        haystack: []const ExprPtr,
        ctx: *TcCtx,
        fn pred(fc: *@This(), nptr: NamePtr) bool {
            for (fc.haystack) |c| {
                switch (c.asRef().kind) {
                    .@"const" => |co| if (co.name == nptr) return true,
                    else => @panic("malformed constructor type"),
                }
            }
            return false;
        }
    };
    var fc = FindCtx{ .haystack = haystack, .ctx = self.ctx };
    return expr.findConst(self.ctx, e, &fc, FindCtx.pred);
}

fn getIIndices(self: *TypeChecker, st: *const InductiveCheckState, ind_ty_app: ExprPtr) tc.Reject!struct { usize, std.ArrayList(ExprPtr) } {
    const valid_app_idx = (try whichValidIndApp(self, st, ind_ty_app)).?;
    const unfolded = expr.unfoldAppsStack(self.ctx.bump, ind_ty_app);
    var ctor_args_wo_params = unfolded.args;
    var i: usize = 0;
    while (i < st.local_params.items.len) : (i += 1) {
        _ = ctor_args_wo_params.pop();
    }
    return .{ valid_app_idx, ctor_args_wo_params };
}

fn whichValidIndApp(self: *TypeChecker, st: *const InductiveCheckState, u_i_ty: ExprPtr) tc.Reject!?usize {
    for (st.ind_consts.items, 0..) |ind_const, i| {
        const ind_name = switch (ind_const.asRef().kind) {
            .@"const" => |co| co.name,
            else => return tc.reject("malformed constructor type", .{}),
        };
        if (try isValidIndApp(self, st, ind_name, u_i_ty)) {
            return i;
        }
    }
    return null;
}

pub fn checkCtor(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    parent_ind_name: NamePtr,
    ctor_type_cursor_in: ExprPtr,
) tc.Reject!void {
    var ctor_type_cursor = ctor_type_cursor_in;
    self.tc_cache.clear();
    var i: usize = 0;
    while (i < st.local_params.items.len) : (i += 1) {
        const local_param = st.local_params.items[i];
        const pair = .{ ctor_type_cursor.asRef().kind, local_param.asRef().kind };
        switch (pair[0]) {
            .pi => |pi| switch (pair[1]) {
                .local => |lc| {
                    try tc.assertDefEq(self, pi.binder_type, lc.binder_type);
                    ctor_type_cursor = expr.inst(self.ctx, pi.body, &.{local_param});
                },
                else => return tc.reject("malformed constructor type", .{}),
            },
            else => return tc.reject("malformed constructor type", .{}),
        }
    }
    while (ctor_type_cursor.asRef().kind == .pi) {
        const pi = ctor_type_cursor.asRef().kind.pi;
        const s = try tc.ensureInfersAsSort(self, pi.binder_type);
        if (!(st.is_zero.? or level.leq(self.ctx, s, st.block_codom.?))) {
            return tc.reject("constructor argument too large for its inductive type", .{});
        }

        try checkPositivity1(self, st, pi.binder_type);
        const local = TcCtx.mkUnique(self.ctx, pi.binder_name, pi.binder_style, pi.binder_type);
        ctor_type_cursor = expr.inst(self.ctx, pi.body, &.{local});
    }
    if (!try isValidIndApp(self, st, parent_ind_name, ctor_type_cursor)) {
        return tc.reject("constructor must target its own inductive type", .{});
    }
}

fn largeElimTestAux(self: *TypeChecker, ctor_type_cursor_in: ExprPtr, rem_params_in: usize) tc.Reject!bool {
    var ctor_type_cursor = ctor_type_cursor_in;
    var rem_params = rem_params_in;
    self.tc_cache.clear();
    var non_prop_ctor_telescope_elems = std.ArrayList(ExprPtr).empty;
    loop: while (true) {
        switch (ctor_type_cursor.asRef().kind) {
            .pi => |pi| {
                if (rem_params != 0) {
                    const local = TcCtx.mkUnique(self.ctx, pi.binder_name, pi.binder_style, pi.binder_type);
                    ctor_type_cursor = expr.inst(self.ctx, pi.body, &.{local});
                    rem_params -= 1;
                } else {
                    const local = TcCtx.mkUnique(self.ctx, pi.binder_name, pi.binder_style, pi.binder_type);
                    ctor_type_cursor = expr.inst(self.ctx, pi.body, &.{local});
                    const binder_type_level = try tc.ensureInfersAsSort(self, pi.binder_type);
                    if (!level.isZero(self.ctx, binder_type_level)) {
                        non_prop_ctor_telescope_elems.append(self.ctx.bump, local) catch util.oom();
                    }
                }
            },
            else => break :loop,
        }
    }

    const unfolded = expr.unfoldApps(self.ctx.bump, ctor_type_cursor);
    const ind_ty_params_and_indices = unfolded.args;

    for (non_prop_ctor_telescope_elems.items) |arg| {
        var contained = false;
        for (ind_ty_params_and_indices.items) |x| {
            if (x == arg) {
                contained = true;
                break;
            }
        }
        if (!contained) return false;
    }
    return true;
}

fn largeElimTest(self: *TypeChecker, st: *const InductiveCheckState) tc.Reject!bool {
    if (st.is_nonzero.?) {
        return true;
    }

    const inds = st.all_inductives_incl_specialized.items;
    if (inds.len == 0) {
        return tc.reject("inductive declaration with no types", .{});
    } else if (inds.len == 1) {
        const ind_ty = inds[0];
        const ctors = ind_ty.ctors.items;
        if (ctors.len == 0) {
            return true;
        } else if (ctors.len == 1) {
            return try largeElimTestAux(self, ctors[0].ty, st.local_params.items.len);
        } else {
            return false;
        }
    } else {
        return false;
    }
}

fn genElimLevel(self: *TypeChecker, st: *const InductiveCheckState) NamePtr {
    const p = TcCtx.str1(self.ctx, "u");
    if (!level.containsParam(st.uparams, p)) {
        return p;
    }
    var i: u64 = 1;
    while (true) {
        const candidate = name_mod.appendIndexAfter(self.ctx, p, i);
        if (level.containsParam(st.uparams, candidate)) {
            i += 1;
        } else {
            return candidate;
        }
    }
}

fn mkElimLevel(self: *TypeChecker, st: *InductiveCheckState) tc.Reject!void {
    if (try largeElimTest(self, st)) {
        const elim_level_name = genElimLevel(self, st);
        const elim_level = TcCtx.param(self.ctx, elim_level_name);
        const rec_levels = blk: {
            var base = std.ArrayList(LevelPtr).empty;
            base.append(self.ctx.bump, elim_level) catch util.oom();
            for (st.uparams.asRef()) |l| {
                base.append(self.ctx.bump, l) catch util.oom();
            }
            break :blk TcCtx.allocLevels(self.ctx, base.items);
        };
        st.rec_uparams = rec_levels;
        st.elim_level = elim_level;
    } else {
        st.elim_level = TcCtx.zero(self.ctx);
        st.rec_uparams = st.uparams;
    }
}

fn initKTarget(st: *InductiveCheckState) void {
    const inds = st.all_inductives_incl_specialized.items;
    const ctor_cond = inds.len == 1 and blk: {
        const ctors = inds[0].ctors.items;
        if (ctors.len == 1) {
            break :blk @as(usize, expr.piTelescopeSize(ctors[0].ty)) == st.local_params.items.len;
        } else {
            break :blk false;
        }
    };
    const is_k_target = st.is_zero.? and inds.len == 1 and ctor_cond;
    st.k_target = is_k_target;
}

fn mkMajors(self: *TypeChecker, st: *InductiveCheckState) void {
    for (st.ind_consts.items, 0..) |ind_const, idx| {
        var ty = expr.foldlApps(self.ctx, ind_const, st.local_params.items);
        ty = expr.foldlApps(self.ctx, ty, st.local_indices.items[idx].items);
        const t = TcCtx.str1(self.ctx, "t");
        st.majors.append(self.ctx.bump, TcCtx.mkUnique(self.ctx, t, BinderStyle.default, ty)) catch util.oom();
    }
}

fn mkMotiveDep(self: *TypeChecker, st: *const InductiveCheckState, major: ExprPtr, ind_type_idx: u64) ExprPtr {
    const elim_sort = TcCtx.mkSort(self.ctx, st.elim_level.?);
    const w_major = expr.abstrPi(self.ctx, major, elim_sort);
    const motive_type = expr.abstrPiTelescope(self.ctx, st.local_indices.items[@intCast(ind_type_idx)].items, w_major);
    const motive_name_base = TcCtx.str1(self.ctx, "motive");
    const motive_name = if (st.all_inductives_incl_specialized.items.len > 1)
        name_mod.appendIndexAfter(self.ctx, motive_name_base, ind_type_idx + 1)
    else
        motive_name_base;

    return TcCtx.mkUnique(self.ctx, motive_name, BinderStyle.implicit, motive_type);
}

fn mkMotives(self: *TypeChecker, st: *InductiveCheckState) void {
    std.debug.assert(st.local_indices.items.len == st.ind_consts.items.len);
    std.debug.assert(st.majors.items.len == st.ind_consts.items.len);
    var i: usize = 0;
    while (i < st.ind_consts.items.len) : (i += 1) {
        const major = st.majors.items[i];
        st.motives.append(self.ctx.bump, mkMotiveDep(self, st, major, @as(u64, i))) catch util.oom();
    }
}

fn isRecArgument(self: *TypeChecker, st: *const InductiveCheckState, ctor_btype_cursor_in: ExprPtr) tc.Reject!?usize {
    var ctor_btype_cursor = tc.whnf(self, ctor_btype_cursor_in);
    if (ctor_btype_cursor.asRef().kind == .pi) {
        const pi = ctor_btype_cursor.asRef().kind.pi;
        const local = TcCtx.mkUnique(self.ctx, pi.binder_name, pi.binder_style, pi.binder_type);
        ctor_btype_cursor = expr.inst(self.ctx, pi.body, &.{local});
        return isRecArgument(self, st, ctor_btype_cursor);
    } else {
        return try whichValidIndApp(self, st, ctor_btype_cursor);
    }
}

fn handleRecArgsAux(self: *TypeChecker, rec_arg_cursor_in: ExprPtr) tc.Reject!struct { ExprPtr, std.ArrayList(ExprPtr) } {
    var rec_arg_cursor = rec_arg_cursor_in;
    var xs = std.ArrayList(ExprPtr).empty;
    while (rec_arg_cursor.asRef().kind == .pi) {
        const pi = rec_arg_cursor.asRef().kind.pi;
        const local = TcCtx.mkUnique(self.ctx, pi.binder_name, pi.binder_style, pi.binder_type);
        rec_arg_cursor = expr.inst(self.ctx, pi.body, &.{local});
        rec_arg_cursor = tc.whnf(self, rec_arg_cursor);
        xs.append(self.ctx.bump, local) catch util.oom();
    }
    return .{ rec_arg_cursor, xs };
}

fn sepNonrecRecCtorArgs(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    ctor_type_cursor_in: ExprPtr,
    rem_params: []const ExprPtr,
) tc.Reject!struct { ExprPtr, std.ArrayList(ExprPtr), std.ArrayList(ExprPtr) } {
    var ctor_type_cursor = ctor_type_cursor_in;
    var all_args = std.ArrayList(ExprPtr).empty;
    var rec_args = std.ArrayList(ExprPtr).empty;
    self.tc_cache.clear();
    var i: usize = 0;
    while (i < st.local_params.items.len) : (i += 1) {
        switch (ctor_type_cursor.asRef().kind) {
            .pi => |pi| {
                const local_param = rem_params[i];
                ctor_type_cursor = expr.inst(self.ctx, pi.body, &.{local_param});
            },
            else => return tc.reject("malformed constructor telescope", .{}),
        }
    }
    while (ctor_type_cursor.asRef().kind == .pi) {
        const pi = ctor_type_cursor.asRef().kind.pi;
        const local = TcCtx.mkUnique(self.ctx, pi.binder_name, pi.binder_style, pi.binder_type);
        ctor_type_cursor = expr.inst(self.ctx, pi.body, &.{local});
        all_args.append(self.ctx.bump, local) catch util.oom();
        if ((try isRecArgument(self, st, pi.binder_type)) != null) {
            rec_args.append(self.ctx.bump, local) catch util.oom();
        }
    }
    return .{ ctor_type_cursor, all_args, rec_args };
}

fn handleRecArgsMinor(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    ctor_idx: usize,
    rec_args: []const ExprPtr,
) tc.Reject!std.ArrayList(ExprPtr) {
    var out = std.ArrayList(ExprPtr).empty;
    for (rec_args, 0..) |rec_arg, i| {
        self.tc_cache.clear();
        const u_i_ty = try tc.inferThenWhnf(self, rec_arg, InferFlag.InferOnly);
        const hra = try handleRecArgsAux(self, u_i_ty);
        const arg_ty = hra[0];
        const xs = hra[1];
        const gii = try getIIndices(self, st, arg_ty);
        const ind_ty_idx = gii[0];
        const applied_indices = gii[1];
        const motive = st.motives.items[ind_ty_idx];
        const motive_base = blk: {
            const lhs = expr.foldlApps(self.ctx, motive, revSlice(self.ctx, applied_indices.items));
            const u_app = expr.foldlApps(self.ctx, rec_arg, xs.items);
            break :blk TcCtx.mkApp(self.ctx, lhs, u_app);
        };
        const v_i_ty = expr.abstrPis(self.ctx, xs.items, motive_base);
        var v_name = TcCtx.str1(self.ctx, "v");
        v_name = name_mod.appendIndexAfter(self.ctx, v_name, @as(u64, ctor_idx));
        v_name = name_mod.appendIndexAfter(self.ctx, v_name, @as(u64, i));
        const v_i = TcCtx.mkUnique(self.ctx, v_name, BinderStyle.default, v_i_ty);
        out.append(self.ctx.bump, v_i) catch util.oom();
    }
    return out;
}

fn revSlice(ctx: *TcCtx, s: []const ExprPtr) []const ExprPtr {
    var out = std.ArrayList(ExprPtr).empty;
    var i: usize = s.len;
    while (i > 0) {
        i -= 1;
        out.append(ctx.bump, s[i]) catch util.oom();
    }
    return out.items;
}

fn mkMinors1group(self: *TypeChecker, st: *const InductiveCheckState, ctors: []const CtorHeader) tc.Reject!std.ArrayList(ExprPtr) {
    var out = std.ArrayList(ExprPtr).empty;
    for (ctors, 0..) |ctor, ctor_idx| {
        const sep = try sepNonrecRecCtorArgs(self, st, ctor.ty, st.local_params.items);
        const stripd_instd_ctor_type = sep[0];
        const all_ctor_args = sep[1];
        const rec_ctor_args = sep[2];
        const gii = try getIIndices(self, st, stripd_instd_ctor_type);
        const ind_ty_idx = gii[0];
        const applied_indices = gii[1];
        const motive = st.motives.items[ind_ty_idx];
        const c_app0 = blk: {
            var rhs = TcCtx.mkConst(self.ctx, ctor.name, st.uparams);
            rhs = expr.foldlApps(self.ctx, rhs, st.local_params.items);
            break :blk expr.foldlApps(self.ctx, rhs, all_ctor_args.items);
        };
        var c_app = expr.foldlApps(self.ctx, motive, revSlice(self.ctx, applied_indices.items));
        c_app = TcCtx.mkApp(self.ctx, c_app, c_app0);
        const v = try handleRecArgsMinor(self, st, ctor_idx, rec_ctor_args.items);

        var minor_type = expr.abstrPis(self.ctx, v.items, c_app);
        minor_type = expr.abstrPis(self.ctx, all_ctor_args.items, minor_type);
        const minor_name = switch (ctor.name.asRef().kind) {
            .str => |s| TcCtx.str(self.ctx, TcCtx.anonymous(self.ctx), s.sfx),
            else => blk: {
                const minor_name = TcCtx.str1(self.ctx, "m");
                break :blk name_mod.appendIndexAfter(self.ctx, minor_name, @as(u64, ctor_idx));
            },
        };
        const minor = TcCtx.mkUnique(self.ctx, minor_name, BinderStyle.default, minor_type);
        out.append(self.ctx.bump, minor) catch util.oom();
    }
    return out;
}

fn mkMinors(self: *TypeChecker, st: *InductiveCheckState) tc.Reject!void {
    util.assert(st.all_inductives_incl_specialized.items.len == st.ind_consts.items.len);
    for (st.all_inductives_incl_specialized.items) |ind_ty| {
        st.minors.append(self.ctx.bump, try mkMinors1group(self, st, ind_ty.ctors.items)) catch util.oom();
    }
}

fn flatMapMinors(ctx: *TcCtx, st: *const InductiveCheckState) std.ArrayList(ExprPtr) {
    var out = std.ArrayList(ExprPtr).empty;
    for (st.minors.items) |v| {
        for (v.items) |x| {
            out.append(ctx.bump, x) catch util.oom();
        }
    }
    return out;
}

fn handleRecCtorArgsRecRule(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    rec_ctor_args: []const ExprPtr,
) tc.Reject!std.ArrayList(ExprPtr) {
    var out = std.ArrayList(ExprPtr).empty;
    const rec_str_ptr = TcCtx.allocString(self.ctx, "rec");
    const flat_mapped_minors = flatMapMinors(self.ctx, st);
    for (rec_ctor_args) |rec_ctor_arg| {
        self.tc_cache.clear();
        const u_i_ty0 = try tc.inferThenWhnf(self, rec_ctor_arg, InferFlag.InferOnly);
        const hra = try handleRecArgsAux(self, u_i_ty0);
        const u_i_ty = hra[0];
        const xs = hra[1];
        const gii = try getIIndices(self, st, u_i_ty);
        const it_idx = gii[0];
        const applied_indices = gii[1];
        const it_name = st.all_inductives_incl_specialized.items[it_idx].name;
        const rec_name = TcCtx.str(self.ctx, it_name, rec_str_ptr);
        const rec_app = TcCtx.mkConst(self.ctx, rec_name, st.rec_uparams.?);
        var app = expr.foldlApps(self.ctx, rec_app, st.local_params.items);
        app = expr.foldlApps(self.ctx, app, st.motives.items);
        app = expr.foldlApps(self.ctx, app, flat_mapped_minors.items);
        app = expr.foldlApps(self.ctx, app, revSlice(self.ctx, applied_indices.items));
        const app_rhs = expr.foldlApps(self.ctx, rec_ctor_arg, xs.items);
        app = TcCtx.mkApp(self.ctx, app, app_rhs);
        const v_hd = expr.abstrLambdaTelescope(self.ctx, xs.items, app);
        out.append(self.ctx.bump, v_hd) catch util.oom();
    }
    return out;
}

fn mkRecRule1(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    ctor: CtorHeader,
    flat_mapped_minors: []const ExprPtr,
    this_minor: ExprPtr,
) tc.Reject!RecRule {
    const sep = try sepNonrecRecCtorArgs(self, st, ctor.ty, st.local_params.items);
    const all_ctor_args = sep[1];
    const rec_ctor_args = sep[2];
    const handled_rec_args = try handleRecCtorArgsRecRule(self, st, rec_ctor_args.items);
    var comp_rhs = expr.foldlApps(self.ctx, this_minor, all_ctor_args.items);
    comp_rhs = expr.foldlApps(self.ctx, comp_rhs, handled_rec_args.items);
    comp_rhs = expr.abstrLambdaTelescope(self.ctx, all_ctor_args.items, comp_rhs);
    comp_rhs = expr.abstrLambdaTelescope(self.ctx, flat_mapped_minors, comp_rhs);
    comp_rhs = expr.abstrLambdaTelescope(self.ctx, st.motives.items, comp_rhs);
    comp_rhs = expr.abstrLambdaTelescope(self.ctx, st.local_params.items, comp_rhs);
    const num_fields = @as(usize, expr.piTelescopeSize(ctor.ty)) - st.local_params.items.len;
    return RecRule{
        .ctor_name = ctor.name,
        .ctor_telescope_size_wo_params = u16TryFrom(num_fields),
        .val = comp_rhs,
    };
}

fn mkRecRules(self: *TypeChecker, st: *const InductiveCheckState) tc.Reject!std.ArrayList(std.ArrayList(RecRule)) {
    var rec_rules = std.ArrayList(std.ArrayList(RecRule)).empty;
    const minors = flatMapMinors(self.ctx, st);
    var overall_ctor_idx: usize = 0;
    for (st.all_inductives_incl_specialized.items) |ind_ty| {
        var grp = std.ArrayList(RecRule).empty;
        for (ind_ty.ctors.items) |ctor| {
            const this_minor = minors.items[overall_ctor_idx];
            const rec_rule = try mkRecRule1(self, st, ctor, minors.items, this_minor);
            overall_ctor_idx += 1;
            grp.append(self.ctx.bump, rec_rule) catch util.oom();
        }
        rec_rules.append(self.ctx.bump, grp) catch util.oom();
    }
    return rec_rules;
}

fn assertNonnestedTysDefEq(self: *TypeChecker, base_ind: *const InductiveData, st: *const InductiveCheckState) tc.Reject!void {
    util.assert(!isNested(st));
    for (base_ind.all_ind_names) |nm| {
        const old_d = Env.getOldDeclar(self.env, nm);
        const new_d = Env.getTempDeclar(self.env, nm);
        if (old_d != null and new_d != null and old_d.?.* == .inductive and new_d.?.* == .inductive) {
            const old = old_d.?.inductive;
            const new = new_d.?.inductive;
            std.debug.assert(old_d.? != new_d.?);
            self.tc_cache.clear();
            try tc.assertDefEq(self, old.info.ty, new.info.ty);
        } else {
            return tc.reject("malformed nested inductive", .{});
        }
    }
}

fn assertNonnestedCtorsDefEq(self: *TypeChecker, st: *const InductiveCheckState) tc.Reject!void {
    util.assert(!isNested(st));
    for (st.all_inductives_incl_specialized.items) |inductive| {
        for (inductive.ctors.items) |ctor| {
            const old_d = Env.getOldDeclar(self.env, ctor.name);
            const new_d = Env.getTempDeclar(self.env, ctor.name);
            if (old_d != null and new_d != null and old_d.?.* == .constructor and new_d.?.* == .constructor) {
                const old = old_d.?.constructor;
                const new = new_d.?.constructor;
                std.debug.assert(old_d.? != new_d.?);
                self.tc_cache.clear();
                try tc.assertDefEq(self, old.info.ty, new.info.ty);
            } else {
                return tc.reject("malformed nested constructor", .{});
            }
        }
    }
}

fn assertNonnestedRecRuleDefEq(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    old: LevelsPtr,
    imported_rr: *const RecRule,
    constructed_rr: *const RecRule,
) tc.Reject!void {
    util.assert(imported_rr != constructed_rr);
    util.assert(!std.meta.eql(imported_rr.*, constructed_rr.*));
    util.assert(!isNested(st));
    self.tc_cache.clear();
    util.assert(imported_rr.ctor_name == constructed_rr.ctor_name);
    util.assert(imported_rr.ctor_telescope_size_wo_params == constructed_rr.ctor_telescope_size_wo_params);
    const rr_made_val = expr.substExprLevels(self.ctx, constructed_rr.val, st.rec_uparams.?, old);
    try tc.assertDefEq(self, imported_rr.val, rr_made_val);
}

fn assertNonnestedRecursorsDefEq(self: *TypeChecker, st: *const InductiveCheckState, recursors: *const std.ArrayList(Declar)) tc.Reject!void {
    util.assert(!isNested(st));
    for (recursors.items) |*new_rec| {
        const old_d = Env.getOldDeclar(self.env, Declar.info(new_rec).name);
        if (old_d != null and old_d.?.* == .recursor and new_rec.* == .recursor) {
            const old = old_d.?;
            const new = new_rec;
            const old_rec_rules = old.recursor.rec_rules;
            const new_rec_rules = new.recursor.rec_rules;
            self.tc_cache.clear();
            util.assert(old != new);
            util.assert(!std.meta.eql(old.*, new.*));
            const imported_w_new_uparams = expr.substExprLevels(self.ctx, Declar.info(old).ty, Declar.info(old).uparams, st.rec_uparams.?);
            try tc.assertDefEq(self, imported_w_new_uparams, Declar.info(new).ty);
            util.assert(old_rec_rules.len == new_rec_rules.len);
            var i: usize = 0;
            while (i < old_rec_rules.len) : (i += 1) {
                try assertNonnestedRecRuleDefEq(self, st, Declar.info(old).uparams, &old_rec_rules[i], &new_rec_rules[i]);
            }
        } else {
            return tc.reject("expected a pair of recursors", .{});
        }
    }
}

fn mkRecursorAux(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    ind_name: NamePtr,
    motive: ExprPtr,
    major: ExprPtr,
    local_indices: []const ExprPtr,
    flat_mapped_minors: []const ExprPtr,
    rec_rules: []const RecRule,
) Declar {
    const motive_app_base = expr.foldlApps(self.ctx, motive, local_indices);
    const motive_app = TcCtx.mkApp(self.ctx, motive_app_base, major);

    var rec_ty = expr.abstrPi(self.ctx, major, motive_app);
    rec_ty = expr.abstrPiTelescope(self.ctx, local_indices, rec_ty);
    rec_ty = expr.abstrPiTelescope(self.ctx, flat_mapped_minors, rec_ty);
    rec_ty = expr.abstrPiTelescope(self.ctx, st.motives.items, rec_ty);
    rec_ty = expr.abstrPiTelescope(self.ctx, st.local_params.items, rec_ty);

    var all_inductives = std.ArrayList(NamePtr).empty;
    for (st.all_inductives_incl_specialized.items) |x| {
        all_inductives.append(self.ctx.bump, x.name) catch util.oom();
    }

    const recursor = RecursorData{
        .info = DeclarInfo{
            .name = blk: {
                const rec_str_ptr = TcCtx.allocString(self.ctx, "rec");
                break :blk TcCtx.str(self.ctx, ind_name, rec_str_ptr);
            },
            .uparams = st.rec_uparams.?,
            .ty = rec_ty,
        },
        .all_inductives = all_inductives.items,
        .num_params = u16TryFrom(st.local_params.items.len),
        .num_indices = u16TryFrom(local_indices.len),
        .num_motives = u16TryFrom(st.motives.items.len),
        .num_minors = u16TryFrom(flat_mapped_minors.len),
        .rec_rules = rec_rules,
        .is_k = st.k_target.?,
    };

    return Declar{ .recursor = recursor };
}

pub fn mkRecursors(self: *TypeChecker, st: *const InductiveCheckState) tc.Reject!std.ArrayList(Declar) {
    const rec_rules = try mkRecRules(self, st);
    var recursors = std.ArrayList(Declar).empty;
    for (st.all_inductives_incl_specialized.items, 0..) |ind, i| {
        const motive = st.motives.items[i];
        const major = st.majors.items[i];
        const local_indices = st.local_indices.items[i];
        const minors = flatMapMinors(self.ctx, st);
        const recursor = mkRecursorAux(
            self,
            st,
            ind.name,
            motive,
            major,
            local_indices.items,
            minors.items,
            rec_rules.items[i].items,
        );
        recursors.append(self.ctx.bump, recursor) catch util.oom();
    }
    return recursors;
}

fn mkSpecializedRecToUnspecializedMap(
    self: *TypeChecker,
    base_mutuals: []const IndTyHeader,
) FxIndexMap(NamePtr, NamePtr) {
    const main_ind_ty_name = base_mutuals[0].name;
    var specialized_rec_names_to_unspecialized_rec_names = swiss_map.FxIndexMap(NamePtr, NamePtr).empty;
    const rec_str = TcCtx.allocString(self.ctx, "rec");

    const inductive = Env.getInductive(self.env, main_ind_ty_name).?;
    const all_ind_names = inductive.all_ind_names;
    util.assert(all_ind_names.len > base_mutuals.len);
    for (all_ind_names[base_mutuals.len..]) |ind_name| {
        const specialized_rec_name = TcCtx.str(self.ctx, ind_name, rec_str);
        var unspecialized_rec_name = TcCtx.str(self.ctx, main_ind_ty_name, rec_str);
        unspecialized_rec_name = name_mod.appendIndexAfter(
            self.ctx,
            unspecialized_rec_name,
            @as(u64, specialized_rec_names_to_unspecialized_rec_names.count() + 1),
        );
        specialized_rec_names_to_unspecialized_rec_names.put(self.ctx.bump, specialized_rec_name, unspecialized_rec_name) catch util.oom();
    }
    return specialized_rec_names_to_unspecialized_rec_names;
}

fn getNestedIfAuxCtor(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    c: NamePtr,
) ?struct { ExprPtr, NamePtr } {
    const ctor = Env.getConstructor(self.env, c) orelse return null;
    const inductive_name = ctor.inductive_name;
    const unspecialized_ty = st.nested_to_unspecialized_ty_nofvars.get(inductive_name) orelse return null;
    return .{ unspecialized_ty, inductive_name };
}

fn restoreCtorName(self: *TypeChecker, st: *const InductiveCheckState, ctor_name: NamePtr) NamePtr {
    const got = getNestedIfAuxCtor(self, st, ctor_name).?;
    const unspecialized_ty = got[0];
    const base_ind_name = got[1];
    const unspecialized_f = expr.unfoldAppsFun(unspecialized_ty);
    const tci = expr.tryConstInfo(unspecialized_f).?;
    const unspecialized_ty_name = tci[0];
    return name_mod.replacePfx(self.ctx, ctor_name, base_ind_name, unspecialized_ty_name);
}

fn restoreReplace(
    self: *TypeChecker,
    e: ExprPtr,
    local_params: []const ExprPtr,
    st: *const InductiveCheckState,
    specialized_rec_names_to_unspecialized_rec_names: *const FxIndexMap(NamePtr, NamePtr),
) tc.Reject!ExprPtr {
    if (try replaceF(self, e, local_params, st, specialized_rec_names_to_unspecialized_rec_names)) |out| {
        return out;
    } else {
        switch (e.asRef().kind) {
            .@"var", .sort, .@"const", .local, .string_lit, .nat_lit => return e,
            .lambda => |la| {
                const binder_type = try restoreReplace(self, la.binder_type, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                const body = try restoreReplace(self, la.body, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                return TcCtx.mkLambda(self.ctx, la.binder_name, la.binder_style, binder_type, body);
            },
            .pi => |pi| {
                const binder_type = try restoreReplace(self, pi.binder_type, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                const body = try restoreReplace(self, pi.body, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                return TcCtx.mkPi(self.ctx, pi.binder_name, pi.binder_style, binder_type, body);
            },
            .let => |le| {
                const binder_type = try restoreReplace(self, le.data.binder_type, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                const val = try restoreReplace(self, le.data.val, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                const body = try restoreReplace(self, le.data.body, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                return TcCtx.mkLet(self.ctx, le.data.binder_name, binder_type, val, body, le.data.nondep);
            },
            .proj => |pr| {
                const structure = try restoreReplace(self, pr.structure, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                return TcCtx.mkProj(self.ctx, pr.ty_name, pr.idx, structure);
            },
            .app => |ap| {
                const fun = try restoreReplace(self, ap.fun, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                const arg = try restoreReplace(self, ap.arg, local_params, st, specialized_rec_names_to_unspecialized_rec_names);
                return TcCtx.mkApp(self.ctx, fun, arg);
            },
        }
    }
}

fn replaceF(
    self: *TypeChecker,
    e: ExprPtr,
    local_params: []const ExprPtr,
    st: *const InductiveCheckState,
    specialized_rec_names_to_unspecialized_rec_names: *const FxIndexMap(NamePtr, NamePtr),
) tc.Reject!?ExprPtr {
    if (e.asRef().kind == .@"const") {
        const co = e.asRef().kind.@"const";
        if (specialized_rec_names_to_unspecialized_rec_names.get(co.name)) |rec_name| {
            return TcCtx.mkConst(self.ctx, rec_name, co.levels);
        }
    }
    const unfolded = expr.unfoldConstApps(self.ctx.bump, e) orelse return null;
    const c_name = unfolded.name;
    const e_args = unfolded.args;
    if (st.nested_to_unspecialized_ty_nofvars.get(c_name)) |nested| {
        std.debug.assert(e_args.items.len >= @as(usize, st.num_params));
        const inner = expr.inst(self.ctx, nested, local_params);
        const outer = expr.foldlApps(self.ctx, inner, e_args.items[@as(usize, st.num_params)..]);
        return outer;
    }
    const got = getNestedIfAuxCtor(self, st, c_name) orelse return null;
    const nested_no_inst = got[0];
    const aux_i_name = got[1];

    std.debug.assert(e_args.items.len >= @as(usize, st.num_params));
    const nested_inst = expr.inst(self.ctx, nested_no_inst, local_params);
    const unfolded2 = expr.unfoldApps(self.ctx.bump, nested_inst);
    const nested_f = unfolded2.fun;
    const i_args = unfolded2.args;
    switch (nested_f.asRef().kind) {
        .@"const" => |co| {
            const cprime_name = name_mod.replacePfx(self.ctx, c_name, aux_i_name, co.name);
            const cprime = TcCtx.mkConst(self.ctx, cprime_name, co.levels);
            const inner = expr.foldlApps(self.ctx, cprime, i_args.items);
            const outer = expr.foldlApps(self.ctx, inner, e_args.items[@as(usize, st.num_params)..]);
            return outer;
        },
        else => return tc.reject("expected a const head", .{}),
    }
}

fn restoreE(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    e_in: ExprPtr,
    nested_rec_name_to_rec_name: *const FxIndexMap(NamePtr, NamePtr),
) tc.Reject!ExprPtr {
    var e = e_in;
    const is_pi = e.asRef().kind == .pi;
    var locals = std.ArrayList(ExprPtr).empty;
    var i: usize = 0;
    while (i < st.local_params.items.len) : (i += 1) {
        switch (e.asRef().kind) {
            .pi => |b| {
                const local = TcCtx.mkUnique(self.ctx, b.binder_name, b.binder_style, b.binder_type);
                e = expr.inst(self.ctx, b.body, &.{local});
                locals.append(self.ctx.bump, local) catch util.oom();
            },
            .lambda => |b| {
                const local = TcCtx.mkUnique(self.ctx, b.binder_name, b.binder_style, b.binder_type);
                e = expr.inst(self.ctx, b.body, &.{local});
                locals.append(self.ctx.bump, local) catch util.oom();
            },
            else => return tc.reject("malformed recursor", .{}),
        }
    }
    const e2 = try restoreReplace(self, e, locals.items, st, nested_rec_name_to_rec_name);
    const out = if (is_pi)
        expr.abstrPiTelescope(self.ctx, locals.items, e2)
    else
        expr.abstrLambdaTelescope(self.ctx, locals.items, e2);
    return out;
}

fn restoreRecursor1(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    all_ind_names_no_specialized: []const NamePtr,
    specialized_rec_names_to_unspecialized_rec_names: *const FxIndexMap(NamePtr, NamePtr),
    rec_name: NamePtr,
) tc.Reject!RecursorData {
    const resolved_rec_name = specialized_rec_names_to_unspecialized_rec_names.get(rec_name) orelse rec_name;
    const new_env_rec = Env.getRecursor(self.env, rec_name).?.*;
    const restored_ty = try restoreE(self, st, new_env_rec.info.ty, specialized_rec_names_to_unspecialized_rec_names);
    var rules = std.ArrayList(RecRule).empty;
    for (new_env_rec.rec_rules) |rule| {
        const val = try restoreE(self, st, rule.val, specialized_rec_names_to_unspecialized_rec_names);
        const ctor_name = if (rec_name == resolved_rec_name) rule.ctor_name else restoreCtorName(self, st, rule.ctor_name);
        rules.append(self.ctx.bump, RecRule{ .ctor_name = ctor_name, .ctor_telescope_size_wo_params = rule.ctor_telescope_size_wo_params, .val = val }) catch util.oom();
    }
    var out = new_env_rec;
    out.info = DeclarInfo{ .name = resolved_rec_name, .ty = restored_ty, .uparams = new_env_rec.info.uparams };
    out.all_inductives = all_ind_names_no_specialized;
    out.rec_rules = rules.items;
    return out;
}

fn checkRestoredRecursor1(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    ind_names_no_specialized: []const NamePtr,
    nested_rec_name_to_rec_name: *const FxIndexMap(NamePtr, NamePtr),
    rec_name: NamePtr,
) tc.Reject!void {
    const restored = try restoreRecursor1(self, st, ind_names_no_specialized, nested_rec_name_to_rec_name, rec_name);
    const resolved_rec_name = nested_rec_name_to_rec_name.get(rec_name) orelse rec_name;
    switch (if (Env.getOldDeclar(self.env, resolved_rec_name)) |d| d.* else Declar{ .axiom = undefined }) {
        .recursor => |original| {
            self.tc_cache.clear();
            try tc.assertDefEq(self, original.info.ty, restored.info.ty);
            util.assert(original.rec_rules.len == restored.rec_rules.len);
            var i: usize = 0;
            while (i < original.rec_rules.len) : (i += 1) {
                const old = original.rec_rules[i];
                const new = restored.rec_rules[i];
                util.assert(old.ctor_name == new.ctor_name);
                self.tc_cache.clear();
                try tc.assertDefEq(self, old.val, new.val);
            }
        },
        else => {},
    }
}

fn restoreRecursors(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    specialized_rec_name_to_rec_name: *const FxIndexMap(NamePtr, NamePtr),
    ind_names_no_specialized: []const NamePtr,
) tc.Reject!void {
    for (ind_names_no_specialized) |old_ind_name| {
        const rec_name = blk: {
            const rec_str_ptr = TcCtx.allocString(self.ctx, "rec");
            break :blk TcCtx.str(self.ctx, old_ind_name, rec_str_ptr);
        };
        try checkRestoredRecursor1(self, st, ind_names_no_specialized, specialized_rec_name_to_rec_name, rec_name);
    }

    var it = specialized_rec_name_to_rec_name.iterator();
    while (it.next()) |entry| {
        try checkRestoredRecursor1(self, st, ind_names_no_specialized, specialized_rec_name_to_rec_name, entry.key_ptr.*);
    }
}

fn checkRestoredCtor1(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    rec_name_map: *const FxIndexMap(NamePtr, NamePtr),
    old_ctor: *const ConstructorData,
) tc.Reject!void {
    const new_ctor = Env.getConstructor(self.env, old_ctor.info.name).?;
    const new_ty = try restoreE(self, st, new_ctor.info.ty, rec_name_map);
    self.tc_cache.clear();
    try tc.assertDefEq(self, old_ctor.info.ty, new_ty);
}

fn restoreAndCheck(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    unmodified_mutuals: *const std.ArrayList(IndTyHeader),
    ind_names_no_specialized: []const NamePtr,
) tc.Reject!void {
    const specialized_to_unspecialized_rec_names = mkSpecializedRecToUnspecializedMap(self, unmodified_mutuals.items);
    for (unmodified_mutuals.items) |unmodified_ind_type| {
        const old_d = Env.getOldDeclar(self.env, unmodified_ind_type.name);
        const new_d = Env.getTempDeclar(self.env, unmodified_ind_type.name);
        if (old_d != null and new_d != null and old_d.?.* == .inductive and new_d.?.* == .inductive) {
            const old = old_d.?.inductive;
            const new = new_d.?.inductive;
            std.debug.assert(old_d.? != new_d.?);
            self.tc_cache.clear();
            try tc.assertDefEq(self, old.info.ty, new.info.ty);
        } else {
            return tc.reject("malformed restored recursor", .{});
        }

        for (unmodified_ind_type.ctors.items) |ctor| {
            const ctor_data = switch (if (Env.getOldDeclar(self.env, ctor.name)) |d| d.* else Declar{ .axiom = undefined }) {
                .constructor => |c| c,
                else => return tc.reject("malformed restored recursor", .{}),
            };
            try checkRestoredCtor1(self, st, &specialized_to_unspecialized_rec_names, &ctor_data);
        }
    }
    try restoreRecursors(self, st, &specialized_to_unspecialized_rec_names, ind_names_no_specialized);
}
