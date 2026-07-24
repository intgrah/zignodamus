const std = @import("std");
const name_mod = @import("name.zig");
const conv = @import("conv.zig");
const eval = @import("eval.zig");
const inference = @import("infer.zig");
const level = @import("level.zig");
const env = @import("env.zig");
const expr = @import("expr.zig");
const tc = @import("tc.zig");
const util = @import("util.zig");
const value = @import("value.zig");
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

const TypeChecker = tc.TypeChecker;

const ExportFile = @import("export_file.zig").ExportFile;
const ExprPtr = @import("ptr.zig").ExprPtr;
const swiss_map = @import("swiss_map.zig");
const FxIndexMap = swiss_map.FxIndexMap;
const LevelPtr = @import("ptr.zig").LevelPtr;
const LevelsPtr = @import("ptr.zig").LevelsPtr;
const NamePtr = @import("ptr.zig").NamePtr;
const TcCtx = @import("TcCtx.zig");

const C = value.C;
const E = value.E;
const S = value.S;
const V = value.V;

const VBinder = struct {
    name: NamePtr,
    style: BinderStyle,
    v: V,

    fn ty(self: VBinder) V {
        return self.v.rigid.head.b_var.ty;
    }
};

const Walk = struct {
    e: E,
    c: C,
    depth: u32,

    const empty: Walk = .{ .e = &value.Env.nil, .c = &value.Ctx.nil, .depth = 0 };
};

fn walkPush(self: *TypeChecker, w: Walk, v: V, dom: V) Walk {
    return .{
        .e = value.envExtend(self.arena, w.e, v),
        .c = value.ctxExtend(self.arena, w.c, dom),
        .depth = w.depth + 1,
    };
}

fn walkFresh(self: *TypeChecker, w: Walk, dom: V) struct { Walk, V } {
    const fresh = eval.mkBvarHc(self, w.depth, dom);
    return .{ walkPush(self, w, fresh, dom), fresh };
}

fn sortOfValue(self: *TypeChecker, w: Walk, ty_v: V) tc.Reject!LevelPtr {
    const q = eval.quote(self, w.depth, ty_v);
    const t = try inference.infer(self, w.depth, w.e, w.c, q, .Check);
    return inference.ensureSort(self, w.depth, t);
}

fn piFold(self: *TypeChecker, binders: []const VBinder, domains: []const ExprPtr, body: ExprPtr) ExprPtr {
    var e = body;
    var i = binders.len;
    while (i > 0) {
        i -= 1;
        e = TcCtx.mkPi(self.ctx, binders[i].name, binders[i].style, domains[i], e);
    }
    return e;
}

fn lamFold(self: *TypeChecker, binders: []const VBinder, domains: []const ExprPtr, body: ExprPtr) ExprPtr {
    var e = body;
    var i = binders.len;
    while (i > 0) {
        i -= 1;
        e = TcCtx.mkLambda(self.ctx, binders[i].name, binders[i].style, domains[i], e);
    }
    return e;
}

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
    checkInductiveDeclarChecked(self, d, ind, env_limit) catch tc.failWithName(d);
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
        try inference.checkDeclarInfo(&tcr, d);
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
    var occ = IndOccurs{ .names = st.ind_names.items };
    defer occ.deinit();

    {
        var e = env.Env.initWithTempExt(&self.declars, &ind_ty_ext1, env_limit);
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var tcr = TypeChecker.init(&ctx, &e, &ar, null, &cache);
        defer tcr.deinit();
        for (st.all_inductives_incl_specialized.items, 0..) |*ind_, i| {
            for (ind_.ctors.items) |ctor| {
                try checkCtor(&tcr, &st, &occ, i, ctor.ty);
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
        try mkMotives(&tcr, &st);
        try mkMinors(&tcr, &st, &occ);
        break :blk try mkRecursors(&tcr, &st, &occ);
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
            .num_params = st.num_params,
            .num_indices = st.index_counts.items[idx],
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
            const num_params = nest_st.num_params;
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
    g: Walk,
    params: std.ArrayList(VBinder),
    param_ty_exprs: std.ArrayList(ExprPtr),
    index_counts: std.ArrayList(u16),
    ind_names: std.ArrayList(NamePtr),
    block_codom: ?LevelPtr,
    is_zero: ?bool,
    is_nonzero: ?bool,
    rec_uparams: ?LevelsPtr,
    elim_level: ?LevelPtr,
    k_target: ?bool,
    motives: std.ArrayList(VBinder),
    motive_ty_exprs: std.ArrayList(ExprPtr),
    minors: std.ArrayList(std.ArrayList(VBinder)),
    minor_ty_exprs: std.ArrayList(std.ArrayList(ExprPtr)),
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
        .g = Walk.empty,
        .params = std.ArrayList(VBinder).empty,
        .param_ty_exprs = std.ArrayList(ExprPtr).empty,
        .index_counts = std.ArrayList(u16).empty,
        .ind_names = std.ArrayList(NamePtr).empty,
        .block_codom = null,
        .is_zero = null,
        .is_nonzero = null,
        .rec_uparams = null,
        .elim_level = null,
        .k_target = null,
        .motives = std.ArrayList(VBinder).empty,
        .motive_ty_exprs = std.ArrayList(ExprPtr).empty,
        .minors = std.ArrayList(std.ArrayList(VBinder)).empty,
        .minor_ty_exprs = std.ArrayList(std.ArrayList(ExprPtr)).empty,
    };
}

const IndOccurs = struct {
    names: []const NamePtr,
    memo: swiss_map.FxHashMap(usize, bool) = .empty,

    fn deinit(self: *IndOccurs) void {
        self.memo.deinit(util.smp_allocator);
    }

    fn matches(self: *IndOccurs, n: NamePtr) bool {
        for (self.names) |m| {
            if (m == n) return true;
        }
        return false;
    }

    fn pred(self: *IndOccurs, n: NamePtr) bool {
        return self.matches(n);
    }

    fn inValue(self: *IndOccurs, tcr: *TypeChecker, depth: u32, v0: V) bool {
        const v = eval.forceThunk(tcr, depth, v0);
        if (self.memo.get(@intFromPtr(v))) |b| {
            return b;
        }
        const r = switch (v.*) {
            .sort, .nat_lit, .str_lit => false,
            .rigid => |rg| self.inHead(tcr, depth, rg.head) or self.inSpine(tcr, depth, rg.spine),
            .unfold => |u| self.matches(u.head.name) or self.inSpine(tcr, depth, u.spine),
            .lam => |l| self.inValue(tcr, depth, eval.lamDomain(tcr, depth, v)) or self.inClosure(tcr, depth, l.body),
            .pi => |p| self.inValue(tcr, depth, p.domain) or self.inClosure(tcr, depth, p.body),
            .thunk => @panic("ind occurs: thunk after force"),
        };
        self.memo.put(util.smp_allocator, @intFromPtr(v), r) catch util.oom();
        return r;
    }

    fn inHead(self: *IndOccurs, tcr: *TypeChecker, depth: u32, head: value.RigidHead) bool {
        switch (head) {
            .b_var => |b| return self.inValue(tcr, depth, b.ty),
            .local => |ex| switch (ex.asRef().kind) {
                .local => |lo| return self.inExpr(tcr, lo.binder_type),
                else => @panic("ind occurs: local head without local expr"),
            },
            .axiom, .ctor, .recursor, .quot_const, .inductive => |nl| return self.matches(nl.name),
        }
    }

    fn inSpine(self: *IndOccurs, tcr: *TypeChecker, depth: u32, s: S) bool {
        var cur = s;
        while (!cur.isEmpty()) : (cur = cur.prev) {
            if (cur.elim.isApp() and self.inValue(tcr, depth, cur.elim.appV())) {
                return true;
            }
        }
        return false;
    }

    fn inClosure(self: *IndOccurs, tcr: *TypeChecker, depth: u32, clo: value.Closure) bool {
        return self.inExpr(tcr, clo.body) or self.inEnv(tcr, depth, clo.env, clo.body);
    }

    fn inExpr(self: *IndOccurs, tcr: *TypeChecker, ex: ExprPtr) bool {
        return expr.findConst(tcr.ctx, ex, self, IndOccurs.pred);
    }

    fn inEnv(self: *IndOccurs, tcr: *TypeChecker, depth: u32, e: E, ex: ExprPtr) bool {
        const nlb = ex.numLooseBvars();
        const mask = ex.asRef().fv_mask;
        var idx: u16 = 0;
        while (idx < nlb) : (idx += 1) {
            if (idx < 64 and (mask >> @intCast(idx)) & 1 == 0) continue;
            const slot = e.lookup(idx) orelse continue;
            if (self.inValue(tcr, depth, slot)) return true;
        }
        return false;
    }
};

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

fn applyParams(self: *TypeChecker, st: *const InductiveCheckState, depth: u32, ty_v: V) tc.Reject!V {
    var cur = ty_v;
    for (st.params.items) |pb| {
        const f = eval.forceAll(self, depth, cur);
        if (f.* != .pi) return tc.reject("exhausted telescope early", .{});
        cur = eval.applyClosure(self, depth, &f.pi.body, pb.v, f.pi.domain);
    }
    return cur;
}

const IndexTelescope = struct {
    w: Walk,
    binders: std.ArrayList(VBinder),
    domains: std.ArrayList(ExprPtr),
    codomain: V,
};

fn openIndicesFrom(self: *TypeChecker, w0: Walk, cur0: V) IndexTelescope {
    var w = w0;
    var cur = cur0;
    var binders = std.ArrayList(VBinder).empty;
    var domains = std.ArrayList(ExprPtr).empty;
    while (true) {
        const f = eval.forceAll(self, w.depth, cur);
        if (f.* != .pi) {
            return .{ .w = w, .binders = binders, .domains = domains, .codomain = f };
        }
        const dom = f.pi.domain;
        domains.append(self.ctx.bump, eval.quote(self, w.depth, dom)) catch util.oom();
        const pushed, const fresh = walkFresh(self, w, dom);
        cur = eval.applyClosure(self, w.depth + 1, &f.pi.body, fresh, dom);
        binders.append(self.ctx.bump, VBinder{ .name = f.pi.binder_name, .style = f.pi.binder_style, .v = fresh }) catch util.oom();
        w = pushed;
    }
}

fn openIndices(self: *TypeChecker, st: *const InductiveCheckState, w0: Walk, ind_ty: ExprPtr) tc.Reject!IndexTelescope {
    const cur = try applyParams(self, st, w0.depth, eval.eval(self, w0.depth, value.envEmpty(), ind_ty));
    return openIndicesFrom(self, w0, cur);
}

fn checkInductiveSpecs(self: *TypeChecker, st: *InductiveCheckState) tc.Reject!void {
    for (st.all_inductives_incl_specialized.items, 0..) |ind, i| {
        if (i == 0) {
            var cur = eval.eval(self, 0, value.envEmpty(), ind.ty);
            var j: u16 = 0;
            while (j < st.num_params) : (j += 1) {
                const f = eval.forceAll(self, st.g.depth, cur);
                if (f.* != .pi) return tc.reject("exhausted telescope early", .{});
                const dom = f.pi.domain;
                st.param_ty_exprs.append(self.ctx.bump, eval.quote(self, st.g.depth, dom)) catch util.oom();
                const pushed, const fresh = walkFresh(self, st.g, dom);
                cur = eval.applyClosure(self, st.g.depth + 1, &f.pi.body, fresh, dom);
                st.params.append(self.ctx.bump, VBinder{ .name = f.pi.binder_name, .style = f.pi.binder_style, .v = fresh }) catch util.oom();
                st.g = pushed;
            }
            const it = openIndicesFrom(self, st.g, cur);
            const block_codom = try inference.ensureSort(self, it.w.depth, it.codomain);
            st.block_codom = block_codom;
            st.is_zero = level.isZero(self.ctx, block_codom);
            st.is_nonzero = level.isNonzero(self.ctx, block_codom);
            st.index_counts.append(self.ctx.bump, u16TryFrom(it.binders.items.len)) catch util.oom();
        } else {
            const it = try openIndices(self, st, st.g, ind.ty);
            const codom_level = try inference.ensureSort(self, it.w.depth, it.codomain);
            util.assert(level.eqAntisymm(self.ctx, codom_level, st.block_codom.?));
            st.index_counts.append(self.ctx.bump, u16TryFrom(it.binders.items.len)) catch util.oom();
        }
        st.ind_names.append(self.ctx.bump, ind.name) catch util.oom();
    }
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

const IndApp = struct {
    pos: usize,
    indices: []const V,
};

fn isBvarAt(v: V, lvl: u32) bool {
    return v.* == .rigid and v.rigid.head == .b_var and v.rigid.head.b_var.lvl == lvl and v.rigid.spine.isEmpty();
}

fn validIndApp(self: *TypeChecker, st: *const InductiveCheckState, occ: *IndOccurs, depth: u32, v: V) ?IndApp {
    const f = eval.forceAll(self, depth, v);
    if (f.* != .rigid or f.rigid.head != .inductive) return null;
    const nl = f.rigid.head.inductive;
    var pos: ?usize = null;
    for (st.ind_names.items, 0..) |n, i| {
        if (n == nl.name) {
            pos = i;
            break;
        }
    }
    const p = pos orelse return null;
    const lhs = nl.levels.asRef();
    const rhs = st.uparams.asRef();
    if (lhs.len != rhs.len) return null;
    for (lhs, rhs) |a, b| {
        if (!level.eqAntisymm(self.ctx, a, b)) return null;
    }
    const nidx: u32 = st.index_counts.items[p];
    if (f.rigid.spine.length != @as(u32, st.num_params) + nidx) return null;
    const args = eval.spineApps(self, depth, f.rigid.spine) orelse return null;
    for (st.params.items, 0..) |pb, i| {
        if (!isBvarAt(args[i], pb.v.rigid.head.b_var.lvl)) return null;
    }
    const indices = args[st.num_params..];
    for (indices) |ix| {
        if (occ.inValue(self, depth, ix)) return null;
    }
    return IndApp{ .pos = p, .indices = indices };
}

fn checkPositivity(self: *TypeChecker, st: *const InductiveCheckState, occ: *IndOccurs, w0: Walk, ty_v: V) tc.Reject!void {
    var w = w0;
    var cur = ty_v;
    while (true) {
        const f = eval.forceAll(self, w.depth, cur);
        if (!occ.inValue(self, w.depth, f)) {
            return;
        }
        if (f.* != .pi) {
            if (validIndApp(self, st, occ, w.depth, f) == null) {
                return tc.reject("expected a valid application of an inductive type", .{});
            }
            return;
        }
        const dom = f.pi.domain;
        if (occ.inValue(self, w.depth, dom)) {
            return tc.reject("non-positive occurrence in inductive", .{});
        }
        const pushed, const fresh = walkFresh(self, w, dom);
        cur = eval.applyClosure(self, w.depth + 1, &f.pi.body, fresh, dom);
        w = pushed;
    }
}

pub fn checkCtor(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    occ: *IndOccurs,
    parent_idx: usize,
    ctor_ty: ExprPtr,
) tc.Reject!void {
    var w = Walk.empty;
    var cur = eval.eval(self, 0, value.envEmpty(), ctor_ty);
    for (st.params.items) |pb| {
        const f = eval.forceAll(self, w.depth, cur);
        if (f.* != .pi) return tc.reject("malformed constructor type", .{});
        if (!conv.defEqAt(self, w.depth, f.pi.domain, pb.ty())) {
            return tc.reject("malformed constructor type", .{});
        }
        cur = eval.applyClosure(self, w.depth, &f.pi.body, pb.v, f.pi.domain);
        w = walkPush(self, w, pb.v, pb.ty());
    }
    while (true) {
        const f = eval.forceAll(self, w.depth, cur);
        if (f.* != .pi) {
            cur = f;
            break;
        }
        const dom = f.pi.domain;
        const s = try sortOfValue(self, w, dom);
        if (!(st.is_zero.? or level.leq(self.ctx, s, st.block_codom.?))) {
            return tc.reject("constructor argument too large for its inductive type", .{});
        }
        try checkPositivity(self, st, occ, w, dom);
        const pushed, const fresh = walkFresh(self, w, dom);
        cur = eval.applyClosure(self, w.depth + 1, &f.pi.body, fresh, dom);
        w = pushed;
    }
    const app = validIndApp(self, st, occ, w.depth, cur) orelse
        return tc.reject("expected a valid application of an inductive type", .{});
    if (app.pos != parent_idx) {
        return tc.reject("constructor must target its own inductive type", .{});
    }
}

fn largeElimTestAux(self: *TypeChecker, st: *const InductiveCheckState, ctor_ty: ExprPtr) tc.Reject!bool {
    var w = Walk.empty;
    var cur = eval.eval(self, 0, value.envEmpty(), ctor_ty);
    var rem_params: u16 = st.num_params;
    var non_prop_fields = std.ArrayList(V).empty;
    while (true) {
        const f = eval.forceAll(self, w.depth, cur);
        if (f.* != .pi) {
            cur = f;
            break;
        }
        const dom = f.pi.domain;
        const pushed, const fresh = walkFresh(self, w, dom);
        cur = eval.applyClosure(self, w.depth + 1, &f.pi.body, fresh, dom);
        if (rem_params > 0) {
            rem_params -= 1;
        } else {
            const s = try sortOfValue(self, w, dom);
            if (!level.isZero(self.ctx, s)) {
                non_prop_fields.append(self.ctx.bump, fresh) catch util.oom();
            }
        }
        w = pushed;
    }
    const args: []const V = if (cur.* == .rigid)
        eval.spineApps(self, w.depth, cur.rigid.spine) orelse &.{}
    else
        &.{};
    for (non_prop_fields.items) |field| {
        var contained = false;
        for (args) |a| {
            if (isBvarAt(a, field.rigid.head.b_var.lvl)) {
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
        const ctors = inds[0].ctors.items;
        if (ctors.len == 0) {
            return true;
        } else if (ctors.len == 1) {
            return try largeElimTestAux(self, st, ctors[0].ty);
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
            break :blk expr.piTelescopeSize(ctors[0].ty) == st.num_params;
        } else {
            break :blk false;
        }
    };
    const is_k_target = st.is_zero.? and inds.len == 1 and ctor_cond;
    st.k_target = is_k_target;
}

fn pushGlobal(self: *TypeChecker, st: *InductiveCheckState, binder_name: NamePtr, style: BinderStyle, ty_expr: ExprPtr) VBinder {
    const ty_v = eval.eval(self, st.g.depth, st.g.e, ty_expr);
    const fresh = eval.mkBvarHc(self, st.g.depth, ty_v);
    st.g = walkPush(self, st.g, fresh, ty_v);
    return VBinder{ .name = binder_name, .style = style, .v = fresh };
}

fn indApp(self: *TypeChecker, st: *const InductiveCheckState, depth: u32, pos: usize, indices: []const VBinder) V {
    var v = value.mkRigidHeadWithEmpty(
        self.arena,
        .{ .inductive = .{ .name = st.ind_names.items[pos], .levels = st.uparams } },
        value.spineEmpty(),
    );
    for (st.params.items) |pb| {
        v = eval.apply(self, depth, v, pb.v);
    }
    for (indices) |ib| {
        v = eval.apply(self, depth, v, ib.v);
    }
    return v;
}

fn mkMotives(self: *TypeChecker, st: *InductiveCheckState) tc.Reject!void {
    const multiple = st.all_inductives_incl_specialized.items.len > 1;
    const motive_base_name = TcCtx.str1(self.ctx, "motive");
    const t_name = TcCtx.str1(self.ctx, "t");
    for (st.all_inductives_incl_specialized.items, 0..) |ind, i| {
        const it = try openIndices(self, st, st.g, ind.ty);
        const major_dom = indApp(self, st, it.w.depth, i, it.binders.items);
        var e = TcCtx.mkSort(self.ctx, st.elim_level.?);
        e = TcCtx.mkPi(self.ctx, t_name, .default, eval.quote(self, it.w.depth, major_dom), e);
        e = piFold(self, it.binders.items, it.domains.items, e);
        const motive_name = if (multiple)
            name_mod.appendIndexAfter(self.ctx, motive_base_name, @as(u64, @intCast(i)) + 1)
        else
            motive_base_name;
        const b = pushGlobal(self, st, motive_name, .implicit, e);
        st.motives.append(self.ctx.bump, b) catch util.oom();
        st.motive_ty_exprs.append(self.ctx.bump, e) catch util.oom();
    }
}

fn isRecField(self: *TypeChecker, st: *const InductiveCheckState, occ: *IndOccurs, w0: Walk, dom0: V) bool {
    var w = w0;
    var cur = dom0;
    while (true) {
        const f = eval.forceAll(self, w.depth, cur);
        if (f.* != .pi) {
            return validIndApp(self, st, occ, w.depth, f) != null;
        }
        const dom = f.pi.domain;
        const pushed, const fresh = walkFresh(self, w, dom);
        cur = eval.applyClosure(self, w.depth + 1, &f.pi.body, fresh, dom);
        w = pushed;
    }
}

const CtorTelescope = struct {
    w: Walk,
    fields: std.ArrayList(VBinder),
    domains: std.ArrayList(ExprPtr),
    rec_fields: std.ArrayList(usize),
    app: IndApp,
};

fn openCtorFields(self: *TypeChecker, st: *const InductiveCheckState, occ: *IndOccurs, w0: Walk, ctor_ty: ExprPtr) tc.Reject!CtorTelescope {
    var w = w0;
    var cur = try applyParams(self, st, w.depth, eval.eval(self, w.depth, value.envEmpty(), ctor_ty));
    var fields = std.ArrayList(VBinder).empty;
    var domains = std.ArrayList(ExprPtr).empty;
    var rec_fields = std.ArrayList(usize).empty;
    while (true) {
        const f = eval.forceAll(self, w.depth, cur);
        if (f.* != .pi) {
            cur = f;
            break;
        }
        const dom = f.pi.domain;
        domains.append(self.ctx.bump, eval.quote(self, w.depth, dom)) catch util.oom();
        if (isRecField(self, st, occ, w, dom)) {
            rec_fields.append(self.ctx.bump, fields.items.len) catch util.oom();
        }
        const pushed, const fresh = walkFresh(self, w, dom);
        cur = eval.applyClosure(self, w.depth + 1, &f.pi.body, fresh, dom);
        fields.append(self.ctx.bump, VBinder{ .name = f.pi.binder_name, .style = f.pi.binder_style, .v = fresh }) catch util.oom();
        w = pushed;
    }
    const app = validIndApp(self, st, occ, w.depth, cur).?;
    return .{ .w = w, .fields = fields, .domains = domains, .rec_fields = rec_fields, .app = app };
}

const RecFieldType = struct {
    w: Walk,
    xs: std.ArrayList(VBinder),
    domains: std.ArrayList(ExprPtr),
    app: IndApp,
    applied: V,
};

fn openRecFieldType(self: *TypeChecker, st: *const InductiveCheckState, occ: *IndOccurs, w0: Walk, rf: VBinder) RecFieldType {
    var w = w0;
    var cur = rf.ty();
    var xs = std.ArrayList(VBinder).empty;
    var domains = std.ArrayList(ExprPtr).empty;
    while (true) {
        const f = eval.forceAll(self, w.depth, cur);
        if (f.* != .pi) {
            cur = f;
            break;
        }
        const dom = f.pi.domain;
        domains.append(self.ctx.bump, eval.quote(self, w.depth, dom)) catch util.oom();
        const pushed, const fresh = walkFresh(self, w, dom);
        cur = eval.applyClosure(self, w.depth + 1, &f.pi.body, fresh, dom);
        xs.append(self.ctx.bump, VBinder{ .name = f.pi.binder_name, .style = f.pi.binder_style, .v = fresh }) catch util.oom();
        w = pushed;
    }
    const app = validIndApp(self, st, occ, w.depth, cur).?;
    var rx = rf.v;
    for (xs.items) |xb| {
        rx = eval.apply(self, w.depth, rx, xb.v);
    }
    return .{ .w = w, .xs = xs, .domains = domains, .app = app, .applied = rx };
}

fn mkMinor(self: *TypeChecker, st: *InductiveCheckState, occ: *IndOccurs, ctor: CtorHeader, ctor_idx: usize) tc.Reject!struct { VBinder, ExprPtr } {
    const t = try openCtorFields(self, st, occ, st.g, ctor.ty);
    var c_app = st.motives.items[t.app.pos].v;
    for (t.app.indices) |ix| {
        c_app = eval.apply(self, t.w.depth, c_app, ix);
    }
    var c0 = value.mkRigidHeadWithEmpty(
        self.arena,
        .{ .ctor = .{ .name = ctor.name, .levels = st.uparams } },
        value.spineEmpty(),
    );
    for (st.params.items) |pb| {
        c0 = eval.apply(self, t.w.depth, c0, pb.v);
    }
    for (t.fields.items) |fb| {
        c0 = eval.apply(self, t.w.depth, c0, fb.v);
    }
    c_app = eval.apply(self, t.w.depth, c_app, c0);

    var w = t.w;
    var v_binders = std.ArrayList(VBinder).empty;
    var v_domains = std.ArrayList(ExprPtr).empty;
    const v_base_name = TcCtx.str1(self.ctx, "v");
    for (t.rec_fields.items, 0..) |fidx, ri| {
        const rt = openRecFieldType(self, st, occ, w, t.fields.items[fidx]);
        var m = st.motives.items[rt.app.pos].v;
        for (rt.app.indices) |ix| {
            m = eval.apply(self, rt.w.depth, m, ix);
        }
        m = eval.apply(self, rt.w.depth, m, rt.applied);
        const hyp_expr = piFold(self, rt.xs.items, rt.domains.items, eval.quote(self, rt.w.depth, m));
        var v_name = name_mod.appendIndexAfter(self.ctx, v_base_name, @as(u64, @intCast(ctor_idx)));
        v_name = name_mod.appendIndexAfter(self.ctx, v_name, @as(u64, @intCast(ri)));
        const ty_v = eval.eval(self, w.depth, w.e, hyp_expr);
        const fresh = eval.mkBvarHc(self, w.depth, ty_v);
        w = walkPush(self, w, fresh, ty_v);
        v_binders.append(self.ctx.bump, VBinder{ .name = v_name, .style = .default, .v = fresh }) catch util.oom();
        v_domains.append(self.ctx.bump, hyp_expr) catch util.oom();
    }
    var e = eval.quote(self, w.depth, c_app);
    e = piFold(self, v_binders.items, v_domains.items, e);
    e = piFold(self, t.fields.items, t.domains.items, e);
    const minor_name = switch (ctor.name.asRef().kind) {
        .str => |s| TcCtx.str(self.ctx, TcCtx.anonymous(self.ctx), s.sfx),
        else => blk: {
            const base = TcCtx.str1(self.ctx, "m");
            break :blk name_mod.appendIndexAfter(self.ctx, base, @as(u64, @intCast(ctor_idx)));
        },
    };
    return .{ pushGlobal(self, st, minor_name, .default, e), e };
}

fn mkMinors(self: *TypeChecker, st: *InductiveCheckState, occ: *IndOccurs) tc.Reject!void {
    for (st.all_inductives_incl_specialized.items) |ind| {
        var grp = std.ArrayList(VBinder).empty;
        var grp_exprs = std.ArrayList(ExprPtr).empty;
        for (ind.ctors.items, 0..) |ctor, ctor_idx| {
            const b, const e = try mkMinor(self, st, occ, ctor, ctor_idx);
            grp.append(self.ctx.bump, b) catch util.oom();
            grp_exprs.append(self.ctx.bump, e) catch util.oom();
        }
        st.minors.append(self.ctx.bump, grp) catch util.oom();
        st.minor_ty_exprs.append(self.ctx.bump, grp_exprs) catch util.oom();
    }
}

fn mkRecRule(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    occ: *IndOccurs,
    flat_minors: []const VBinder,
    flat_minor_exprs: []const ExprPtr,
    this_minor: VBinder,
    ctor: CtorHeader,
) tc.Reject!RecRule {
    const rec_str = TcCtx.allocString(self.ctx, "rec");
    const t = try openCtorFields(self, st, occ, st.g, ctor.ty);
    var handled = std.ArrayList(ExprPtr).empty;
    for (t.rec_fields.items) |fidx| {
        const rt = openRecFieldType(self, st, occ, t.w, t.fields.items[fidx]);
        const rec_name = TcCtx.str(self.ctx, st.ind_names.items[rt.app.pos], rec_str);
        var rv = value.mkRigidHeadWithEmpty(
            self.arena,
            .{ .recursor = .{ .name = rec_name, .levels = st.rec_uparams.? } },
            value.spineEmpty(),
        );
        for (st.params.items) |pb| {
            rv = eval.apply(self, rt.w.depth, rv, pb.v);
        }
        for (st.motives.items) |mb| {
            rv = eval.apply(self, rt.w.depth, rv, mb.v);
        }
        for (flat_minors) |nb| {
            rv = eval.apply(self, rt.w.depth, rv, nb.v);
        }
        for (rt.app.indices) |ix| {
            rv = eval.apply(self, rt.w.depth, rv, ix);
        }
        rv = eval.apply(self, rt.w.depth, rv, rt.applied);
        handled.append(self.ctx.bump, lamFold(self, rt.xs.items, rt.domains.items, eval.quote(self, rt.w.depth, rv))) catch util.oom();
    }
    var e = eval.quote(self, t.w.depth, this_minor.v);
    for (t.fields.items) |fb| {
        e = TcCtx.mkApp(self.ctx, e, eval.quote(self, t.w.depth, fb.v));
    }
    for (handled.items) |h| {
        e = TcCtx.mkApp(self.ctx, e, h);
    }
    e = lamFold(self, t.fields.items, t.domains.items, e);
    e = lamFold(self, flat_minors, flat_minor_exprs, e);
    e = lamFold(self, st.motives.items, st.motive_ty_exprs.items, e);
    e = lamFold(self, st.params.items, st.param_ty_exprs.items, e);
    const num_fields = @as(usize, expr.piTelescopeSize(ctor.ty)) - @as(usize, st.num_params);
    return RecRule{
        .ctor_name = ctor.name,
        .ctor_telescope_size_wo_params = u16TryFrom(num_fields),
        .val = e,
    };
}

fn assertClosedDefEq(self: *TypeChecker, x: ExprPtr, y: ExprPtr) tc.Reject!void {
    const vx = eval.eval(self, 0, value.envEmpty(), x);
    const vy = eval.eval(self, 0, value.envEmpty(), y);
    if (!conv.defEqAt(self, 0, vx, vy)) {
        return tc.reject("def_eq failed", .{});
    }
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
            try assertClosedDefEq(self, old.info.ty, new.info.ty);
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
                try assertClosedDefEq(self, old.info.ty, new.info.ty);
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
    util.assert(imported_rr.ctor_name == constructed_rr.ctor_name);
    util.assert(imported_rr.ctor_telescope_size_wo_params == constructed_rr.ctor_telescope_size_wo_params);
    const made = eval.evalInst(self, constructed_rr.val, st.rec_uparams.?, old);
    const imported = eval.eval(self, 0, value.envEmpty(), imported_rr.val);
    if (!conv.defEqAt(self, 0, imported, made)) {
        return tc.reject("def_eq failed", .{});
    }
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
            util.assert(old != new);
            util.assert(!std.meta.eql(old.*, new.*));
            const imported_w_new_uparams = eval.evalInst(self, Declar.info(old).ty, Declar.info(old).uparams, st.rec_uparams.?);
            const made = eval.eval(self, 0, value.envEmpty(), Declar.info(new).ty);
            if (!conv.defEqAt(self, 0, imported_w_new_uparams, made)) {
                return tc.reject("def_eq failed", .{});
            }
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

pub fn mkRecursors(self: *TypeChecker, st: *InductiveCheckState, occ: *IndOccurs) tc.Reject!std.ArrayList(Declar) {
    var flat_minors = std.ArrayList(VBinder).empty;
    var flat_minor_exprs = std.ArrayList(ExprPtr).empty;
    for (st.minors.items, st.minor_ty_exprs.items) |grp, grp_exprs| {
        flat_minors.appendSlice(self.ctx.bump, grp.items) catch util.oom();
        flat_minor_exprs.appendSlice(self.ctx.bump, grp_exprs.items) catch util.oom();
    }

    var rec_rules = std.ArrayList(std.ArrayList(RecRule)).empty;
    var flat_idx: usize = 0;
    for (st.all_inductives_incl_specialized.items) |ind| {
        var grp = std.ArrayList(RecRule).empty;
        for (ind.ctors.items) |ctor| {
            const rule = try mkRecRule(self, st, occ, flat_minors.items, flat_minor_exprs.items, flat_minors.items[flat_idx], ctor);
            flat_idx += 1;
            grp.append(self.ctx.bump, rule) catch util.oom();
        }
        rec_rules.append(self.ctx.bump, grp) catch util.oom();
    }

    const rec_str = TcCtx.allocString(self.ctx, "rec");
    const t_name = TcCtx.str1(self.ctx, "t");
    var recursors = std.ArrayList(Declar).empty;
    for (st.all_inductives_incl_specialized.items, 0..) |ind, i| {
        const it = try openIndices(self, st, st.g, ind.ty);
        const major_dom = indApp(self, st, it.w.depth, i, it.binders.items);
        const w2, const major = walkFresh(self, it.w, major_dom);
        var capp = st.motives.items[i].v;
        for (it.binders.items) |ib| {
            capp = eval.apply(self, w2.depth, capp, ib.v);
        }
        capp = eval.apply(self, w2.depth, capp, major);
        var e = eval.quote(self, w2.depth, capp);
        e = TcCtx.mkPi(self.ctx, t_name, .default, eval.quote(self, it.w.depth, major_dom), e);
        e = piFold(self, it.binders.items, it.domains.items, e);
        e = piFold(self, flat_minors.items, flat_minor_exprs.items, e);
        e = piFold(self, st.motives.items, st.motive_ty_exprs.items, e);
        e = piFold(self, st.params.items, st.param_ty_exprs.items, e);
        const recursor = RecursorData{
            .info = DeclarInfo{
                .name = TcCtx.str(self.ctx, ind.name, rec_str),
                .uparams = st.rec_uparams.?,
                .ty = e,
            },
            .all_inductives = st.ind_names.items,
            .num_params = st.num_params,
            .num_indices = st.index_counts.items[i],
            .num_motives = u16TryFrom(st.motives.items.len),
            .num_minors = u16TryFrom(flat_minors.items.len),
            .rec_rules = rec_rules.items[i].items,
            .is_k = st.k_target.?,
        };
        recursors.append(self.ctx.bump, Declar{ .recursor = recursor }) catch util.oom();
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
