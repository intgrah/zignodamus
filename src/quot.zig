const Arena = @import("Arena.zig");
const conv = @import("conv.zig");
const env = @import("env.zig");
const eval = @import("eval.zig");
const expr = @import("expr.zig");
const tc = @import("tc.zig");
const value = @import("value.zig");
const TcCtx = @import("TcCtx.zig");

const Declar = env.Declar;
const EnvLimit = env.EnvLimit;
const ExprPtr = @import("ptr.zig").ExprPtr;
const TypeChecker = tc.TypeChecker;

fn arrow(ctx: *TcCtx, dom: ExprPtr, cod: ExprPtr) ExprPtr {
    return TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, dom, cod);
}

fn apps(ctx: *TcCtx, fun: ExprPtr, args: []const ExprPtr) ExprPtr {
    var cur = fun;
    for (args) |arg| {
        cur = TcCtx.mkApp(ctx, cur, arg);
    }
    return cur;
}

fn assertDefEq(checker: *TypeChecker, actual: ExprPtr, expected: ExprPtr) tc.Reject!void {
    const va = eval.eval(checker, 0, value.envEmpty(), actual);
    const ve = eval.eval(checker, 0, value.envEmpty(), expected);
    if (!conv.defEqAt(checker, 0, va, ve)) {
        return tc.reject("def_eq failed", .{});
    }
}

pub fn checkEq(ctx: *TcCtx, ar: *Arena, declar: *const Declar) tc.Reject!void {
    const eq_name = TcCtx.str1(ctx, "Eq");
    const refl_name = TcCtx.str2(ctx, "Eq", "refl");
    const prop = expr.prop(ctx);
    const e = ctx.export_file.newEnv(EnvLimit{ .by_name = declar.info().name });
    const ind = env.Env.getInductive(&e, eq_name) orelse return tc.reject("improperly formed Eq type", .{});
    const info = ind.info;
    if (info.uparams.asRef().len != 1) return tc.reject("Eq must have exactly 1 universe parameter", .{});
    if (ind.num_params != 2) return tc.reject("Eq must have exactly 2 parameters", .{});
    if (ind.all_ctor_names.len != 1) return tc.reject("Eq must have exactly one constructor", .{});
    if (ind.all_ctor_names[0] != refl_name) return tc.reject("Eq constructor must be Eq.refl", .{});
    const ctor = env.Env.getConstructor(&e, refl_name) orelse return tc.reject("Eq.refl constructor missing", .{});
    const cinfo = ctor.info;
    if (cinfo.uparams.asRef().len != 1) return tc.reject("malformed Eq universe parameters", .{});

    const alpha_name = TcCtx.str1(ctx, "α");
    const a_name = TcCtx.str1(ctx, "a");
    const v0 = TcCtx.mkVar(ctx, 0);
    const v1 = TcCtx.mkVar(ctx, 1);

    const eq_ty = TcCtx.mkPi(
        ctx,
        alpha_name,
        .implicit,
        TcCtx.mkSort(ctx, info.uparams.asRef()[0]),
        arrow(ctx, v0, arrow(ctx, v1, prop)),
    );
    var cache: tc.TcCache = .empty;
    defer cache.deinit();
    var checker = TypeChecker.init(ctx, &e, ar, info, &cache);
    try assertDefEq(&checker, info.ty, eq_ty);

    const eq_const = TcCtx.mkConst(ctx, eq_name, info.uparams);
    const refl_ty = TcCtx.mkPi(
        ctx,
        alpha_name,
        .implicit,
        TcCtx.mkSort(ctx, cinfo.uparams.asRef()[0]),
        TcCtx.mkPi(ctx, a_name, .default, v0, apps(ctx, eq_const, &.{ v1, v0, v0 })),
    );
    var cache2: tc.TcCache = .empty;
    defer cache2.deinit();
    var checker2 = TypeChecker.init(ctx, &e, ar, cinfo, &cache2);
    try assertDefEq(&checker2, cinfo.ty, refl_ty);
}

pub fn checkQuot(ctx: *TcCtx, ar: *Arena, declar: *const Declar) tc.Reject!void {
    const prop = expr.prop(ctx);
    const u_level = TcCtx.param(ctx, TcCtx.str1(ctx, "u"));
    const v_level = TcCtx.param(ctx, TcCtx.str1(ctx, "v"));
    const sort_u = TcCtx.mkSort(ctx, u_level);
    const sort_v = TcCtx.mkSort(ctx, v_level);
    const levels_u = TcCtx.allocLevels(ctx, &.{u_level});
    const levels_v = TcCtx.allocLevels(ctx, &.{v_level});
    const quot_name = ctx.export_file.name_cache.quot.?;
    const quot_mk_name = ctx.export_file.name_cache.quot_mk.?;
    const quot_const = TcCtx.mkConst(ctx, quot_name, levels_u);

    const A_name = TcCtx.str1(ctx, "A");
    const B_name = TcCtx.str1(ctx, "B");
    const r_name = TcCtx.str1(ctx, "r");
    const f_name = TcCtx.str1(ctx, "f");
    const a_name = TcCtx.str1(ctx, "a");
    const b_name = TcCtx.str1(ctx, "b");
    const q_name = TcCtx.str1(ctx, "q");

    const v0 = TcCtx.mkVar(ctx, 0);
    const v1 = TcCtx.mkVar(ctx, 1);
    const v2 = TcCtx.mkVar(ctx, 2);
    const v3 = TcCtx.mkVar(ctx, 3);
    const v4 = TcCtx.mkVar(ctx, 4);

    const rel = arrow(ctx, v0, arrow(ctx, v1, prop));

    const name = declar.info().name;
    const expected: ExprPtr = blk: {
        if (name == TcCtx.str1(ctx, "Quot")) {
            break :blk TcCtx.mkPi(ctx, A_name, .implicit, sort_u, TcCtx.mkPi(ctx, r_name, .default, rel, sort_u));
        }
        if (name == TcCtx.str2(ctx, "Quot", "mk")) {
            const cod = arrow(ctx, v1, apps(ctx, quot_const, &.{ v2, v1 }));
            break :blk TcCtx.mkPi(ctx, A_name, .implicit, sort_u, TcCtx.mkPi(ctx, r_name, .default, rel, cod));
        }
        if (name == TcCtx.str2(ctx, "Quot", "lift")) {
            try checkEq(ctx, ar, declar);
            const eq_const = TcCtx.mkConst(ctx, TcCtx.str1(ctx, "Eq"), levels_v);
            const rab = apps(ctx, v4, &.{ v1, v0 });
            const eq_app = apps(ctx, eq_const, &.{ v4, TcCtx.mkApp(ctx, v3, v2), TcCtx.mkApp(ctx, v3, v1) });
            const sound = TcCtx.mkPi(ctx, a_name, .default, v3, TcCtx.mkPi(ctx, b_name, .default, v4, arrow(ctx, rab, eq_app)));
            const cod = arrow(ctx, sound, arrow(ctx, apps(ctx, quot_const, &.{ v4, v3 }), v3));
            const w_f = TcCtx.mkPi(ctx, f_name, .default, arrow(ctx, v2, v1), cod);
            const w_B = TcCtx.mkPi(ctx, B_name, .implicit, sort_v, w_f);
            break :blk TcCtx.mkPi(ctx, A_name, .implicit, sort_u, TcCtx.mkPi(ctx, r_name, .default, rel, w_B));
        }
        if (name == TcCtx.str2(ctx, "Quot", "ind")) {
            const quot_mk_const = TcCtx.mkConst(ctx, quot_mk_name, levels_u);
            const motive_ty = arrow(ctx, apps(ctx, quot_const, &.{ v1, v0 }), prop);
            const minor = TcCtx.mkPi(ctx, a_name, .default, v2, TcCtx.mkApp(ctx, v1, apps(ctx, quot_mk_const, &.{ v3, v2, v0 })));
            const major = TcCtx.mkPi(ctx, q_name, .default, apps(ctx, quot_const, &.{ v3, v2 }), TcCtx.mkApp(ctx, v2, v0));
            const w_B = TcCtx.mkPi(ctx, B_name, .implicit, motive_ty, arrow(ctx, minor, major));
            break :blk TcCtx.mkPi(ctx, A_name, .implicit, sort_u, TcCtx.mkPi(ctx, r_name, .default, rel, w_B));
        }
        return tc.reject("invalid quotient declaration", .{});
    };
    const e = ctx.export_file.newEnv(EnvLimit{ .by_name = name });
    var cache: tc.TcCache = .empty;
    defer cache.deinit();
    var checker = TypeChecker.init(ctx, &e, ar, declar.info().*, &cache);
    try assertDefEq(&checker, declar.info().ty, expected);
}
