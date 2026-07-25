const std = @import("std");
const name_mod = @import("name.zig");
const conv = @import("conv.zig");
const eval = @import("eval.zig");
const quote = @import("quote.zig");
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
    const q = quote.quote(self, w.depth, ty_v);
    const t = try inference.infer(self, .Check, w.depth, w.e, w.c, q);
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

fn u16TryFrom(x: usize) error{Declined}!u16 {
    return std.math.cast(u16, x) orelse tc.decline("inductive metadata exceeds implementation limit", .{});
}

pub fn checkInductiveDeclar(self: *const ExportFile, d: *const Declar) void {
    const ind: *const InductiveData, const env_limit: EnvLimit = switch (d.*) {
        .inductive => |*i| blk: {
            const start, const size = self.mutual_block_sizes.get(i.info.name).?;
            break :blk .{ i, EnvLimit{ .by_index = start + size } };
        },
        else => @panic("expected inductive"),
    };
    checkInductiveDeclarChecked(self, d, ind, env_limit) catch |err| tc.reportWithName(d, err);
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

    var spec_aux_ext = DeclarMap.empty;
    var st = blk: {
        var e = env.Env.initWithTempExt(&self.declars, &spec_aux_ext, env_limit);
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var tcr = TypeChecker.init(&ctx, &e, &ar, null, &cache);
        defer tcr.deinit();
        break :blk try specializeNested(&tcr, ind, cloneHeaders(&tcr, unmodified_tys_ctors), &spec_aux_ext);
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
    var occ = IndOccurs{ .st = &st };
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

    const ctor_extension = try mkCtorsEnvExt(&ctx, &st, ind_ty_ext1);

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
    const is_nested_ = isNested(st);
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

pub fn mkCtorsEnvExt(ctx: *TcCtx, nest_st: *const InductiveCheckState, env_ext_in: DeclarMap) error{Declined}!DeclarMap {
    var env_ext = env_ext_in;
    for (nest_st.all_inductives_incl_specialized.items) |inductive| {
        for (inductive.ctors.items, 0..) |ctor, idx| {
            const info = DeclarInfo{ .name = ctor.name, .ty = ctor.ty, .uparams = nest_st.uparams };
            const num_params = nest_st.num_params;
            const num_fields = try u16TryFrom(expr.piTelescopeSize(ctor.ty) - num_params);
            const d = Declar{ .constructor = ConstructorData{
                .info = info,
                .inductive_name = inductive.name,
                .ctor_idx = try u16TryFrom(idx),
                .num_params = num_params,
                .num_fields = num_fields,
            } };
            env_ext.put(ctx.bump, ctor.name, d) catch util.oom();
        }
    }
    return env_ext;
}

pub const InductiveCheckState = struct {
    spec_key_to_aux: FxIndexMap(ExprPtr, NamePtr),
    aux_to_container: FxIndexMap(NamePtr, V),
    uparams: LevelsPtr,
    num_params: u16,
    all_inductives_incl_specialized: std.ArrayList(IndTyHeader),
    next_ngen_idx: u64,
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
) InductiveCheckState {
    return InductiveCheckState{
        .spec_key_to_aux = swiss_map.FxIndexMap(ExprPtr, NamePtr).empty,
        .aux_to_container = swiss_map.FxIndexMap(NamePtr, V).empty,
        .uparams = info_uparams,
        .num_params = num_params,
        .all_inductives_incl_specialized = new_tys,
        .next_ngen_idx = 1,
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
    st: *const InductiveCheckState,
    memo: swiss_map.FxHashMap(usize, bool) = .empty,

    fn deinit(self: *IndOccurs) void {
        self.memo.deinit(util.smp_allocator);
    }

    fn matches(self: *IndOccurs, n: NamePtr) bool {
        for (self.st.all_inductives_incl_specialized.items) |h| {
            if (h.name == n) return true;
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
    return self.aux_to_container.count() != 0;
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

const SpecCtx = struct {
    st: *InductiveCheckState,
    occ: *IndOccurs,
    aux_ext: *DeclarMap,
    params: []const VBinder,
    param_ty_exprs: []const ExprPtr,
    memo: quote.QuoteMemo = .empty,

    fn deinit(self: *SpecCtx) void {
        self.memo.deinit(util.smp_allocator);
    }

    pub fn hook(hctx: *SpecCtx, self: *TypeChecker, depth: u32, v: V) tc.Reject!?ExprPtr {
        if (v.* != .rigid or v.rigid.head != .inductive) return null;
        return specTryNested(self, hctx, depth, v);
    }
};

fn specializeNested(
    self: *TypeChecker,
    t_from_file: *const InductiveData,
    unmodified_tys_ctors: std.ArrayList(IndTyHeader),
    aux_ext: *DeclarMap,
) tc.Reject!InductiveCheckState {
    var st = newState(t_from_file.info.uparams, t_from_file.num_params, unmodified_tys_ctors);
    var occ = IndOccurs{ .st = &st };
    defer occ.deinit();

    var w = Walk.empty;
    var params = std.ArrayList(VBinder).empty;
    var param_ty_exprs = std.ArrayList(ExprPtr).empty;
    var cur0 = eval.eval(self, 0, value.envEmpty(), st.all_inductives_incl_specialized.items[0].ty);
    var j: u16 = 0;
    while (j < st.num_params) : (j += 1) {
        const f = eval.forceAll(self, w.depth, cur0);
        if (f.* != .pi) return tc.reject("exhausted telescope early", .{});
        const dom = f.pi.domain;
        param_ty_exprs.append(self.ctx.bump, quote.quote(self, w.depth, dom)) catch util.oom();
        const pushed, const fresh = walkFresh(self, w, dom);
        cur0 = eval.applyClosure(self, w.depth + 1, &f.pi.body, fresh, dom);
        params.append(self.ctx.bump, VBinder{ .name = f.pi.binder_name, .style = f.pi.binder_style, .v = fresh }) catch util.oom();
        w = pushed;
    }

    var sp = SpecCtx{
        .st = &st,
        .occ = &occ,
        .aux_ext = aux_ext,
        .params = params.items,
        .param_ty_exprs = param_ty_exprs.items,
    };
    defer sp.deinit();

    var i: usize = 0;
    while (i < st.all_inductives_incl_specialized.items.len) : (i += 1) {
        var new_ctors = std.ArrayList(CtorHeader).empty;
        for (st.all_inductives_incl_specialized.items[i].ctors.items) |ctor| {
            var cur = eval.eval(self, 0, value.envEmpty(), ctor.ty);
            for (params.items) |pb| {
                const f = eval.forceAll(self, w.depth, cur);
                if (f.* != .pi) return tc.reject("exhausted telescope early", .{});
                cur = eval.applyClosure(self, w.depth, &f.pi.body, pb.v, f.pi.domain);
            }
            const replaced = try quote.quoteWith(self, &sp, w.depth, cur);
            const new_ty = piFold(self, params.items, param_ty_exprs.items, replaced);
            new_ctors.append(self.ctx.bump, CtorHeader{ .name = ctor.name, .ty = new_ty }) catch util.oom();
        }
        st.all_inductives_incl_specialized.items[i].ctors = new_ctors;
    }
    return st;
}

fn indAppValue(self: *TypeChecker, depth: u32, ind_name: NamePtr, levels: LevelsPtr, args: []const V) V {
    var v = value.mkRigidHeadWithEmpty(
        self.arena,
        .{ .inductive = .{ .name = ind_name, .levels = levels } },
        value.spineEmpty(),
    );
    for (args) |a| {
        v = eval.apply(self, depth, v, a);
    }
    return v;
}

fn specTryNested(self: *TypeChecker, sp: *SpecCtx, depth: u32, v: V) tc.Reject!?ExprPtr {
    const head = v.rigid.head.inductive;
    const container = Env.getInductive(self.env, head.name) orelse return null;
    const k: usize = container.num_params;
    if (v.rigid.spine.length < k) return null;
    const args = eval.spineApps(self, depth, v.rigid.spine) orelse return null;
    var mentions = false;
    for (args[0..k]) |a| {
        if (sp.occ.inValue(self, depth, a)) {
            mentions = true;
            break;
        }
    }
    if (!mentions) return null;
    for (args[0..k]) |a| {
        if (occursInnerBvar(self, sp, depth, a)) {
            return tc.reject("nested types cannot contain loose bvars", .{});
        }
    }
    const key = specKey(self, sp, head.name, head.levels, args[0..k]);
    if (sp.st.spec_key_to_aux.get(key)) |aux_name| {
        return specEmit(self, sp, depth, aux_name, args[k..]);
    }
    var result: ?ExprPtr = null;
    const nested_pfx = TcCtx.str1(self.ctx, "_nested");
    for (container.all_ind_names) |cont_name| {
        const cont = Env.getInductive(self.env, cont_name) orelse return null;
        const aux_name = mkUniqueName(self, name_mod.concatName(self.ctx, nested_pfx, cont_name), sp.st);
        const capp = indAppValue(self, sp.st.num_params, cont_name, head.levels, args[0..k]);
        const jkey = specKey(self, sp, cont_name, head.levels, args[0..k]);
        sp.st.spec_key_to_aux.put(self.ctx.bump, jkey, aux_name) catch util.oom();
        sp.st.aux_to_container.put(self.ctx.bump, aux_name, capp) catch util.oom();
        const aux_ty = try specInstantiate(self, sp, cont.info.ty, cont.info.uparams, head.levels, args[0..k]);
        var aux_ctors = std.ArrayList(CtorHeader).empty;
        var aux_ctor_names = std.ArrayList(NamePtr).empty;
        for (cont.all_ctor_names) |cn| {
            const cd = Env.getConstructor(self.env, cn) orelse return null;
            const aux_ctor_name = name_mod.replacePfx(self.ctx, cn, cont_name, aux_name);
            const aux_ctor_ty = try specInstantiate(self, sp, cd.info.ty, cd.info.uparams, head.levels, args[0..k]);
            aux_ctors.append(self.ctx.bump, CtorHeader{ .name = aux_ctor_name, .ty = aux_ctor_ty }) catch util.oom();
            aux_ctor_names.append(self.ctx.bump, aux_ctor_name) catch util.oom();
        }
        sp.st.all_inductives_incl_specialized.append(self.ctx.bump, IndTyHeader{
            .name = aux_name,
            .ty = aux_ty,
            .ctors = aux_ctors,
        }) catch util.oom();
        const self_names = self.ctx.bump.alloc(NamePtr, 1) catch util.oom();
        self_names[0] = aux_name;
        sp.aux_ext.put(self.ctx.bump, aux_name, Declar{ .inductive = InductiveData{
            .info = DeclarInfo{ .name = aux_name, .uparams = sp.st.uparams, .ty = aux_ty },
            .is_nested = true,
            .is_recursive = false,
            .num_params = sp.st.num_params,
            .num_indices = cont.num_indices,
            .all_ind_names = self_names,
            .all_ctor_names = aux_ctor_names.items,
        } }) catch util.oom();
        if (cont_name == head.name) {
            result = specEmit(self, sp, depth, aux_name, args[k..]);
        }
    }
    return result;
}

fn occursInnerBvar(self: *TypeChecker, sp: *SpecCtx, depth: u32, arg: V) bool {
    const p: u32 = sp.st.num_params;
    const q = quote.quote(self, depth, arg);
    const nlb: u32 = q.numLooseBvars();
    if (nlb == 0 or depth == p) return false;
    const inner: u32 = depth - p;
    if (nlb <= 64) {
        const mask = q.asRef().fv_mask;
        const low: u64 = if (inner >= 64) std.math.maxInt(u64) else (@as(u64, 1) << @intCast(inner)) - 1;
        return mask & low != 0;
    }
    var idx: u16 = 0;
    while (idx < inner and idx < nlb) : (idx += 1) {
        if (expr.hasLooseBvar(q, idx)) return true;
    }
    return false;
}

fn specKey(self: *TypeChecker, sp: *SpecCtx, ind_name: NamePtr, levels: LevelsPtr, args: []const V) ExprPtr {
    return quote.quote(self, sp.st.num_params, indAppValue(self, sp.st.num_params, ind_name, levels, args));
}

fn specEmit(self: *TypeChecker, sp: *SpecCtx, depth: u32, aux_name: NamePtr, rest: []const V) ExprPtr {
    var e = TcCtx.mkConst(self.ctx, aux_name, sp.st.uparams);
    for (sp.params) |pb| {
        e = TcCtx.mkApp(self.ctx, e, TcCtx.mkVar(self.ctx, @intCast(depth - 1 - pb.v.rigid.head.b_var.lvl)));
    }
    for (rest) |a| {
        e = TcCtx.mkApp(self.ctx, e, quote.quote(self, depth, a));
    }
    return e;
}

fn specInstantiate(
    self: *TypeChecker,
    sp: *SpecCtx,
    ty: ExprPtr,
    uparams: LevelsPtr,
    levels: LevelsPtr,
    args: []const V,
) tc.Reject!ExprPtr {
    const p: u32 = sp.st.num_params;
    var cur = eval.evalInst(self, ty, uparams, levels);
    for (args) |a| {
        const f = eval.forceAll(self, p, cur);
        if (f.* != .pi) return tc.reject("exhausted telescope early", .{});
        cur = eval.applyClosure(self, p, &f.pi.body, a, f.pi.domain);
    }
    return piFold(self, sp.params, sp.param_ty_exprs, quote.quote(self, p, cur));
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
        domains.append(self.ctx.bump, quote.quote(self, w.depth, dom)) catch util.oom();
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
                st.param_ty_exprs.append(self.ctx.bump, quote.quote(self, st.g.depth, dom)) catch util.oom();
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
            st.index_counts.append(self.ctx.bump, try u16TryFrom(it.binders.items.len)) catch util.oom();
        } else {
            const it = try openIndices(self, st, st.g, ind.ty);
            const codom_level = try inference.ensureSort(self, it.w.depth, it.codomain);
            util.assert(level.eqAntisymm(self.ctx, codom_level, st.block_codom.?));
            st.index_counts.append(self.ctx.bump, try u16TryFrom(it.binders.items.len)) catch util.oom();
        }
        st.ind_names.append(self.ctx.bump, ind.name) catch util.oom();
    }
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
        e = TcCtx.mkPi(self.ctx, t_name, .default, quote.quote(self, it.w.depth, major_dom), e);
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
        domains.append(self.ctx.bump, quote.quote(self, w.depth, dom)) catch util.oom();
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
        domains.append(self.ctx.bump, quote.quote(self, w.depth, dom)) catch util.oom();
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
        const hyp_expr = piFold(self, rt.xs.items, rt.domains.items, quote.quote(self, rt.w.depth, m));
        var v_name = name_mod.appendIndexAfter(self.ctx, v_base_name, @as(u64, @intCast(ctor_idx)));
        v_name = name_mod.appendIndexAfter(self.ctx, v_name, @as(u64, @intCast(ri)));
        const ty_v = eval.eval(self, w.depth, w.e, hyp_expr);
        const fresh = eval.mkBvarHc(self, w.depth, ty_v);
        w = walkPush(self, w, fresh, ty_v);
        v_binders.append(self.ctx.bump, VBinder{ .name = v_name, .style = .default, .v = fresh }) catch util.oom();
        v_domains.append(self.ctx.bump, hyp_expr) catch util.oom();
    }
    var e = quote.quote(self, w.depth, c_app);
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
        handled.append(self.ctx.bump, lamFold(self, rt.xs.items, rt.domains.items, quote.quote(self, rt.w.depth, rv))) catch util.oom();
    }
    var e = quote.quote(self, t.w.depth, this_minor.v);
    for (t.fields.items) |fb| {
        e = TcCtx.mkApp(self.ctx, e, quote.quote(self, t.w.depth, fb.v));
    }
    for (handled.items) |h| {
        e = TcCtx.mkApp(self.ctx, e, h);
    }
    e = lamFold(self, t.fields.items, t.domains.items, e);
    e = lamFold(self, flat_minors, flat_minor_exprs, e);
    e = lamFold(self, st.motives.items, st.motive_ty_exprs.items, e);
    e = lamFold(self, st.params.items, st.param_ty_exprs.items, e);
    const num_fields = expr.piTelescopeSize(ctor.ty) - @as(usize, st.num_params);
    return RecRule{
        .ctor_name = ctor.name,
        .ctor_telescope_size_wo_params = try u16TryFrom(num_fields),
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
        var e = quote.quote(self, w2.depth, capp);
        e = TcCtx.mkPi(self.ctx, t_name, .default, quote.quote(self, it.w.depth, major_dom), e);
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
            .num_motives = try u16TryFrom(st.motives.items.len),
            .num_minors = try u16TryFrom(flat_minors.items.len),
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
) ?struct { V, NamePtr } {
    const ctor = Env.getConstructor(self.env, c) orelse return null;
    const container = st.aux_to_container.get(ctor.inductive_name) orelse return null;
    return .{ container, ctor.inductive_name };
}

fn restoreCtorName(self: *TypeChecker, st: *const InductiveCheckState, ctor_name: NamePtr) NamePtr {
    const got = getNestedIfAuxCtor(self, st, ctor_name).?;
    const container, const aux_ind_name = got;
    return name_mod.replacePfx(self.ctx, ctor_name, aux_ind_name, container.rigid.head.inductive.name);
}

const RestoreCtx = struct {
    st: *const InductiveCheckState,
    rec_map: *const FxIndexMap(NamePtr, NamePtr),
    memo: quote.QuoteMemo = .empty,

    fn deinit(self: *RestoreCtx) void {
        self.memo.deinit(util.smp_allocator);
    }

    pub fn hook(hctx: *RestoreCtx, self: *TypeChecker, depth: u32, v: V) tc.Reject!?ExprPtr {
        if (v.* != .rigid) return null;
        const st = hctx.st;
        switch (v.rigid.head) {
            .recursor => |nl| {
                const renamed = hctx.rec_map.get(nl.name) orelse return null;
                return try quote.quoteSpineWith(self, hctx, depth, TcCtx.mkConst(self.ctx, renamed, nl.levels), v.rigid.spine);
            },
            .inductive => |nl| {
                const container = st.aux_to_container.get(nl.name) orelse return null;
                const args = eval.spineApps(self, depth, v.rigid.spine) orelse return null;
                util.assert(args.len >= st.num_params);
                var e = quote.quote(self, depth, container);
                for (args[st.num_params..]) |a| {
                    e = TcCtx.mkApp(self.ctx, e, try quote.quoteWith(self, hctx, depth, a));
                }
                return e;
            },
            .ctor => |nl| {
                const got = getNestedIfAuxCtor(self, st, nl.name) orelse return null;
                const container, const aux_ind_name = got;
                const args = eval.spineApps(self, depth, v.rigid.spine) orelse return null;
                util.assert(args.len >= st.num_params);
                const cont_head = container.rigid.head.inductive;
                const renamed = name_mod.replacePfx(self.ctx, nl.name, aux_ind_name, cont_head.name);
                var e = TcCtx.mkConst(self.ctx, renamed, cont_head.levels);
                const cont_args = eval.spineApps(self, depth, container.rigid.spine).?;
                for (cont_args) |ca| {
                    e = TcCtx.mkApp(self.ctx, e, quote.quote(self, depth, ca));
                }
                for (args[st.num_params..]) |a| {
                    e = TcCtx.mkApp(self.ctx, e, try quote.quoteWith(self, hctx, depth, a));
                }
                return e;
            },
            else => return null,
        }
    }
};

fn restoreE(
    self: *TypeChecker,
    st: *const InductiveCheckState,
    e_in: ExprPtr,
    nested_rec_name_to_rec_name: *const FxIndexMap(NamePtr, NamePtr),
) tc.Reject!ExprPtr {
    var w = Walk.empty;
    var cur = eval.forceAll(self, 0, eval.eval(self, 0, value.envEmpty(), e_in));
    const is_pi = cur.* == .pi;
    var binders = std.ArrayList(VBinder).empty;
    var domains = std.ArrayList(ExprPtr).empty;
    var i: u16 = 0;
    while (i < st.num_params) : (i += 1) {
        const f = eval.forceAll(self, w.depth, cur);
        const binder_name, const binder_style, const dom, const clo = switch (f.*) {
            .pi => |b| .{ b.binder_name, b.binder_style, b.domain, &f.pi.body },
            .lam => |b| .{ b.binder_name, b.binder_style, eval.lamDomain(self, w.depth, f), &f.lam.body },
            else => return tc.reject("malformed recursor", .{}),
        };
        domains.append(self.ctx.bump, quote.quote(self, w.depth, dom)) catch util.oom();
        const pushed, const fresh = walkFresh(self, w, dom);
        cur = eval.applyClosure(self, w.depth + 1, clo, fresh, dom);
        binders.append(self.ctx.bump, VBinder{ .name = binder_name, .style = binder_style, .v = fresh }) catch util.oom();
        w = pushed;
    }
    var h = RestoreCtx{ .st = st, .rec_map = nested_rec_name_to_rec_name };
    defer h.deinit();
    const body = try quote.quoteWith(self, &h, w.depth, cur);
    return if (is_pi)
        piFold(self, binders.items, domains.items, body)
    else
        lamFold(self, binders.items, domains.items, body);
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
            try assertClosedDefEq(self, original.info.ty, restored.info.ty);
            util.assert(original.rec_rules.len == restored.rec_rules.len);
            var i: usize = 0;
            while (i < original.rec_rules.len) : (i += 1) {
                const old = original.rec_rules[i];
                const new = restored.rec_rules[i];
                util.assert(old.ctor_name == new.ctor_name);
                try assertClosedDefEq(self, old.val, new.val);
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
    try assertClosedDefEq(self, old_ctor.info.ty, new_ty);
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
            try assertClosedDefEq(self, old.info.ty, new.info.ty);
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
