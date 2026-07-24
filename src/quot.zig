const std = @import("std");
const quot = @import("quot.zig");
const Arena = @import("Arena.zig");
const env = @import("env.zig");
const expr = @import("expr.zig");
const tc = @import("tc.zig");

fn checkerReject(comptime msg: []const u8) tc.Reject {
    std.debug.print("kernel: rejected: " ++ msg ++ "\n", .{});
    return error.CheckFailed;
}

const ConstructorData = env.ConstructorData;
const Declar = env.Declar;
const DeclarInfo = env.DeclarInfo;
const InductiveData = env.InductiveData;
const EnvLimit = env.EnvLimit;
const BinderStyle = expr.BinderStyle;
const TypeChecker = tc.TypeChecker;
const TcCtx = @import("TcCtx.zig");

pub fn checkEq(ctx: *TcCtx, ar: *Arena, declar: *const Declar) tc.Reject!void {
    const name = TcCtx.str1(ctx, "Eq");
    const cname = TcCtx.str2(ctx, "Eq", "refl");
    const alpha_name = TcCtx.str1(ctx, "α");
    const a_name = TcCtx.str1(ctx, "a");
    const prop = expr.prop(ctx);
    const e = ctx.export_file.newEnv(EnvLimit{ .by_name = declar.info().name });
    if (env.Env.getInductive(&e, name)) |ind| {
        const info = ind.info;
        const num_params = ind.num_params;
        const all_ctor_names = ind.all_ctor_names;
        const eq_const = TcCtx.mkConst(ctx, name, info.uparams);
        if (info.uparams.asRef().len != 1) return checkerReject("Eq must have exactly 1 universe parameter");
        if (num_params != 2) return checkerReject("Eq must have exactly 2 parameters");
        const uparam = blk: {
            const ls = info.uparams.asRef();
            if (ls.len == 1) {
                break :blk TcCtx.mkSort(ctx, ls[0]);
            } else {
                return checkerReject("Eq must have exactly 1 universe parameter");
            }
        };
        const alpha = TcCtx.mkUnique(ctx, alpha_name, .implicit, uparam);
        const inner = TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, alpha, TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, alpha, prop));
        const expected = expr.abstrPi(ctx, alpha, inner);
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var checker = tc.TypeChecker.init(ctx, &e, ar, info, &cache);
        try tc.assertDefEq(&checker, info.ty, expected);
        if (all_ctor_names.len == 1) {
            const ctor_name = all_ctor_names[0];
            if (cname != ctor_name) return checkerReject("Eq constructor must be Eq.refl");
            if (env.Env.getConstructor(&e, ctor_name)) |ctor| {
                const cinfo = ctor.info;
                const uparam_sort = blk: {
                    const ls = cinfo.uparams.asRef();
                    if (ls.len == 1) {
                        break :blk TcCtx.mkSort(ctx, ls[0]);
                    } else {
                        return checkerReject("malformed Eq universe parameters");
                    }
                };
                const alpha2 = TcCtx.mkUnique(ctx, alpha_name, .implicit, uparam_sort);
                const a = TcCtx.mkUnique(ctx, a_name, .default, alpha2);

                const app = TcCtx.mkApp(ctx, TcCtx.mkApp(ctx, TcCtx.mkApp(ctx, eq_const, alpha2), a), a);
                const expected2 = expr.abstrPi(ctx, alpha2, expr.abstrPi(ctx, a, app));
                var cache2: tc.TcCache = .empty;
                defer cache2.deinit();
                var checker2 = tc.TypeChecker.init(ctx, &e, ar, cinfo, &cache2);
                try tc.assertDefEq(&checker2, cinfo.ty, expected2);
            } else return checkerReject("Eq.refl constructor missing");
        } else {
            return checkerReject("Eq must have exactly one constructor");
        }
    } else return checkerReject("improperly formed Eq type");
}

pub fn checkQuot(ctx: *TcCtx, ar: *Arena, declar: *const Declar) tc.Reject!void {
    const prop = expr.prop(ctx);
    const u_name = TcCtx.str1(ctx, "u");
    const v_name = TcCtx.str1(ctx, "v");
    const q_name = TcCtx.str1(ctx, "q");
    const u_level = TcCtx.param(ctx, u_name);
    const v_level = TcCtx.param(ctx, v_name);
    const sort_u = TcCtx.mkSort(ctx, u_level);
    const sort_v = TcCtx.mkSort(ctx, v_level);

    const levels_u = TcCtx.allocLevels(ctx, &.{u_level});
    const levels_v = TcCtx.allocLevels(ctx, &.{v_level});
    const levels_uv = TcCtx.allocLevels(ctx, &.{ u_level, v_level });
    const quot_name = ctx.export_file.name_cache.quot.?;
    const quot_mk_name = ctx.export_file.name_cache.quot_mk.?;

    const A_name = TcCtx.str1(ctx, "A");
    const B_name = TcCtx.str1(ctx, "B");
    const r_name = TcCtx.str1(ctx, "r");
    const f_name = TcCtx.str1(ctx, "f");
    const a_name = TcCtx.str1(ctx, "a");
    const b_name = TcCtx.str1(ctx, "b");

    const A = TcCtx.mkUnique(ctx, A_name, .implicit, sort_u);
    const B = TcCtx.mkUnique(ctx, B_name, .implicit, sort_v);
    const A_A_Prop = TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, A, TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, A, prop));
    const A_B = TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, A, B);
    const r = TcCtx.mkUnique(ctx, r_name, .default, A_A_Prop);
    const f = TcCtx.mkUnique(ctx, f_name, .default, A_B);
    const a = TcCtx.mkUnique(ctx, a_name, .default, A);
    const b = TcCtx.mkUnique(ctx, b_name, .default, A);

    const expected_quot = Declar{ .quot = .{
        .info = DeclarInfo{ .name = quot_name, .uparams = levels_u, .ty = expr.abstrPi(ctx, A, expr.abstrPi(ctx, r, sort_u)) },
    } };
    const quot_const = TcCtx.mkConst(ctx, expected_quot.info().name, levels_u);
    const quot_A_r = TcCtx.mkApp(ctx, TcCtx.mkApp(ctx, quot_const, A), r);

    const expected_quot_mk = Declar{ .quot = .{
        .info = DeclarInfo{
            .name = quot_mk_name,
            .uparams = levels_u,
            .ty = expr.abstrPi(ctx, A, expr.abstrPi(ctx, r, TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, A, quot_A_r))),
        },
    } };

    const quot_mk_const = TcCtx.mkConst(ctx, expected_quot_mk.info().name, levels_u);
    const eq_name = TcCtx.str1(ctx, "Eq");
    const eq_const = TcCtx.mkConst(ctx, eq_name, levels_v);

    const fa = TcCtx.mkApp(ctx, f, a);
    const fb = TcCtx.mkApp(ctx, f, b);
    const eq_app = TcCtx.mkApp(ctx, TcCtx.mkApp(ctx, TcCtx.mkApp(ctx, eq_const, B), fa), fb);
    const rab = TcCtx.mkApp(ctx, TcCtx.mkApp(ctx, r, a), b);

    const lift_inner = expr.abstrPi(ctx, a, expr.abstrPi(ctx, b, TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, rab, eq_app)));

    if (declar.info().name == TcCtx.str1(ctx, "Quot")) {
        const e = ctx.export_file.newEnv(EnvLimit{ .by_name = quot_name });
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var checker = tc.TypeChecker.init(ctx, &e, ar, declar.info().*, &cache);
        try tc.assertDefEq(&checker, declar.info().ty, expected_quot.info().ty);
    } else if (declar.info().name == TcCtx.str2(ctx, "Quot", "mk")) {
        const e = ctx.export_file.newEnv(EnvLimit{ .by_name = quot_mk_name });
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var checker = tc.TypeChecker.init(ctx, &e, ar, declar.info().*, &cache);
        try tc.assertDefEq(&checker, declar.info().ty, expected_quot_mk.info().ty);
    } else if (declar.info().name == TcCtx.str2(ctx, "Quot", "lift")) {
        try checkEq(ctx, ar, declar);
        const expected_quot_lift = Declar{ .quot = .{
            .info = DeclarInfo{
                .name = declar.info().name,
                .uparams = levels_uv,
                .ty = expr.abstrPi(ctx, A, expr.abstrPi(ctx, r, expr.abstrPi(ctx, B, expr.abstrPi(ctx, f, TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, lift_inner, TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, quot_A_r, B)))))),
            },
        } };
        const e = ctx.export_file.newEnv(EnvLimit{ .by_name = declar.info().name });
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var checker = tc.TypeChecker.init(ctx, &e, ar, declar.info().*, &cache);
        try tc.assertDefEq(&checker, declar.info().ty, expected_quot_lift.info().ty);
        return;
    } else if (declar.info().name == TcCtx.str2(ctx, "Quot", "ind")) {
        const quot_A_r_prop = TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, quot_A_r, prop);

        const B_local = TcCtx.mkUnique(ctx, B_name, .implicit, quot_A_r_prop);

        const q_local = TcCtx.mkUnique(ctx, q_name, .default, quot_A_r);

        const quot_mk_app = TcCtx.mkApp(ctx, TcCtx.mkApp(ctx, TcCtx.mkApp(ctx, quot_mk_const, A), r), a);

        const lhs = expr.abstrPi(ctx, a, TcCtx.mkApp(ctx, B_local, quot_mk_app));
        const rhs = expr.abstrPi(ctx, q_local, TcCtx.mkApp(ctx, B_local, q_local));

        const expected_quot_ind = Declar{ .quot = .{
            .info = DeclarInfo{
                .name = declar.info().name,
                .uparams = levels_u,
                .ty = expr.abstrPi(ctx, A, expr.abstrPi(ctx, r, expr.abstrPi(ctx, B_local, TcCtx.mkPi(ctx, TcCtx.anonymous(ctx), .default, lhs, rhs)))),
            },
        } };

        const e = ctx.export_file.newEnv(EnvLimit{ .by_name = declar.info().name });
        var cache: tc.TcCache = .empty;
        defer cache.deinit();
        var checker = tc.TypeChecker.init(ctx, &e, ar, declar.info().*, &cache);
        try tc.assertDefEq(&checker, declar.info().ty, expected_quot_ind.info().ty);
        return;
    } else {
        return checkerReject("invalid quotient declaration");
    }
}
