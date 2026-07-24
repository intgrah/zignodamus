const std = @import("std");
const conv = @import("conv.zig");
const eval = @import("eval.zig");
const expr = @import("expr.zig");
const env_mod = @import("env.zig");
const level = @import("level.zig");
const tc = @import("tc.zig");
const util = @import("util.zig");
const value = @import("value.zig");
const TcCtx = @import("TcCtx.zig");
const ptr = @import("ptr.zig");

const Closure = value.Closure;
const Declar = env_mod.Declar;
const InferFlag = tc.InferFlag;
const Reject = tc.Reject;
const RigidHead = value.RigidHead;
const TypeChecker = tc.TypeChecker;
const ExprPtr = ptr.ExprPtr;
const LevelPtr = ptr.LevelPtr;
const NamePtr = ptr.NamePtr;
const C = value.C;
const E = value.E;
const V = value.V;

pub fn checkDeclarInfo(self: *TypeChecker, d: *const Declar) Reject!void {
    const info = d.info();
    if (!level.noDupesAllParams(self.ctx, info.uparams)) {
        return tc.reject("duplicate universe parameters in declaration", .{});
    }
    if (info.ty.hasFvars()) {
        return tc.reject("declaration type contains free variables", .{});
    }
    const ty_ty = try infer(self, 0, value.envEmpty(), value.ctxEmpty(), info.ty, .Check);
    const sort = try ensureSort(self, 0, ty_ty);
    if (d.* == .theorem) {
        if (!level.isZero(self.ctx, sort)) {
            return tc.reject("theorem type must be Prop (sort 0)", .{});
        }
    }
}

pub fn checkDefLike(self: *TypeChecker, d: *const Declar) Reject!void {
    try checkDeclarInfo(self, d);
    const val = switch (d.*) {
        .theorem => |x| x.val,
        .definition => |x| x.val,
        .opaque_ => |x| x.val,
        else => unreachable,
    };
    const val_ty = try infer(self, 0, value.envEmpty(), value.ctxEmpty(), val, .Check);
    const declared = eval.eval(self, 0, value.envEmpty(), d.info().ty);
    if (!conv.defEqAt(self, 0, val_ty, declared)) {
        return tc.reject("def_eq failed", .{});
    }
}

pub fn ensureSort(self: *TypeChecker, depth: u32, v: V) Reject!LevelPtr {
    const f = eval.forceAll(self, depth, v);
    switch (f.*) {
        .sort => |s| return s.level,
        else => return tc.reject("expected a sort", .{}),
    }
}

fn inferSortOf(self: *TypeChecker, depth: u32, e: E, c: C, ex: ExprPtr, comptime flag: InferFlag) Reject!LevelPtr {
    const t = try infer(self, depth, e, c, ex, flag);
    return ensureSort(self, depth, t);
}

fn argValue(self: *TypeChecker, depth: u32, e: E, a: ExprPtr) V {
    return switch (a.asRef().kind) {
        .@"var", .sort, .@"const", .nat_lit, .string_lit, .local => eval.eval(self, depth, e, a),
        else => eval.mkThunkHc(self, e, a),
    };
}

pub const CachedType = struct {
    bits: usize,

    comptime {
        std.debug.assert(@alignOf(value.Value) >= 2);
    }

    pub fn pack(v: V, is_checked: bool) CachedType {
        return .{ .bits = @intFromPtr(v) | @intFromBool(is_checked) };
    }

    pub fn result(self: CachedType) V {
        return @ptrFromInt(self.bits & ~@as(usize, 1));
    }

    pub fn checked(self: CachedType) bool {
        return self.bits & 1 != 0;
    }
};

fn litInductiveType(self: *TypeChecker, n: ?NamePtr) V {
    const name = n orelse @panic("infer: literal type name missing");
    const levels = TcCtx.allocLevels(self.ctx, &.{});
    return value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .inductive = .{ .name = name, .levels = levels } }, value.spineEmpty());
}

pub fn infer(self: *TypeChecker, depth: u32, e: E, c: C, ex: ExprPtr, comptime flag: InferFlag) Reject!V {
    switch (ex.asRef().kind) {
        .@"var" => |x| return c.lookup(x.dbj_idx) orelse tc.reject("loose bvar in infer", .{}),
        .local => |l| return eval.eval(self, depth, value.envEmpty(), l.binder_type),
        .sort => |s| {
            if (flag == .Check) {
                if (self.declar_info) |declar_info| {
                    if (!level.allUparamsDefined(self.ctx, s.level, declar_info.uparams)) {
                        return tc.reject("universe parameter not declared by the current declaration", .{});
                    }
                }
            }
            const sc = TcCtx.succ(self.ctx, s.level);
            return value.mkSort(self.arena, level.simplify(self.ctx, sc));
        },
        .@"const" => |cn| {
            if (self.env.getDeclar(cn.name) == null) {
                return tc.reject("declaration not found in infer_const", .{});
            }
            if (flag == .Check) {
                if (self.declar_info) |declar_info| {
                    for (cn.levels.asRef()) |c_uparam| {
                        util.assert(level.allUparamsDefined(self.ctx, c_uparam, declar_info.uparams));
                    }
                }
            }
            return eval.constHeadType(self, cn.name, cn.levels);
        },
        .nat_lit => {
            util.assert(self.ctx.export_file.config.nat_extension);
            return litInductiveType(self, self.ctx.export_file.name_cache.nat);
        },
        .string_lit => {
            util.assert(self.ctx.export_file.config.string_extension);
            return litInductiveType(self, self.ctx.export_file.name_cache.string);
        },
        .app, .lambda, .pi, .let, .proj => {},
    }
    const key = .{ @intFromPtr(eval.keyEnv(self, e, ex)), ex };
    if (self.tc_cache.type_cache.get(key)) |cached| {
        if (flag == .InferOnly or cached.checked()) {
            return cached.result();
        }
    }
    const r = switch (ex.asRef().kind) {
        .app => try inferApp(self, depth, e, c, ex, flag),
        .lambda => |l| blk: {
            const dom = argValue(self, depth, e, l.binder_type);
            if (flag == .Check) {
                _ = try inferSortOf(self, depth, e, c, l.binder_type, flag);
                const fresh = eval.mkBvarHc(self, depth, dom);
                const e2 = value.envExtend(self.arena, e, fresh);
                const c2 = value.ctxExtend(self.arena, c, dom);
                _ = try infer(self, depth + 1, e2, c2, l.body, flag);
            }
            break :blk value.mkPi(self.arena, l.binder_name, l.binder_style, dom, Closure{
                .env = eval.keyEnv(self, e, ex),
                .body = l.body,
                .kind = .infer,
                .ctx = c,
            });
        },
        .pi => |p| blk: {
            const l1 = try inferSortOf(self, depth, e, c, p.binder_type, flag);
            const dom = argValue(self, depth, e, p.binder_type);
            const fresh = eval.mkBvarHc(self, depth, dom);
            const e2 = value.envExtend(self.arena, e, fresh);
            const c2 = value.ctxExtend(self.arena, c, dom);
            const l2 = try inferSortOf(self, depth + 1, e2, c2, p.body, flag);
            const im = TcCtx.imax(self.ctx, l1, l2);
            break :blk value.mkSort(self.arena, level.simplify(self.ctx, im));
        },
        .let => |l| blk: {
            const d = l.data;
            const dom = argValue(self, depth, e, d.binder_type);
            if (flag == .Check) {
                _ = try inferSortOf(self, depth, e, c, d.binder_type, flag);
                const val_ty = try infer(self, depth, e, c, d.val, flag);
                if (!conv.convTypesAt(self, depth, dom, val_ty)) {
                    return tc.reject("let def_eq failed", .{});
                }
            }
            const slot = argValue(self, depth, e, d.val);
            const e2 = value.envExtend(self.arena, e, slot);
            const c2 = value.ctxExtend(self.arena, c, dom);
            break :blk try infer(self, depth, e2, c2, d.body, flag);
        },
        .proj => |p| try inferProj(self, depth, e, c, p.ty_name, p.idx, p.structure, flag),
        else => unreachable,
    };
    self.tc_cache.type_cache.put(util.smp_allocator, key, CachedType.pack(r, flag == .Check)) catch util.oom();
    return r;
}

fn inferApp(self: *TypeChecker, depth: u32, e: E, c: C, ex: ExprPtr, comptime flag: InferFlag) Reject!V {
    const ua = expr.unfoldAppsStack(self.ctx.bump, ex);
    var args = ua.args;
    defer args.deinit(self.ctx.bump);
    var fty = try infer(self, depth, e, c, ua.fun, flag);
    while (args.pop()) |arg| {
        const fty_f = eval.forceAll(self, depth, fty);
        switch (fty_f.*) {
            .pi => |p| {
                if (flag == .Check) {
                    const arg_ty = try infer(self, depth, e, c, arg, flag);
                    if (!conv.convTypesAt(self, depth, p.domain, arg_ty)) {
                        return tc.reject("app arg def_eq failed", .{});
                    }
                }
                if (p.body.kind == .eval and p.body.body.numLooseBvars() == 0) {
                    fty = eval.eval(self, depth, p.body.env, p.body.body);
                } else {
                    const av = argValue(self, depth, e, arg);
                    fty = eval.applyClosure(self, depth, &fty_f.pi.body, av, p.domain);
                }
            },
            else => return tc.reject("expected a pi type", .{}),
        }
    }
    return fty;
}

fn inferProj(
    self: *TypeChecker,
    depth: u32,
    e: E,
    c: C,
    ty_name: NamePtr,
    idx: usize,
    structure: ExprPtr,
    comptime flag: InferFlag,
) Reject!V {
    _ = ty_name;
    const struct_ty = try infer(self, depth, e, c, structure, flag);
    const struct_ty_f = eval.forceAll(self, depth, struct_ty);
    const struct_ty_is_prop = conv.isPropType(self, depth, struct_ty_f);
    var ind_name: NamePtr = undefined;
    var ind_levels: ptr.LevelsPtr = undefined;
    var params: []const V = undefined;
    switch (struct_ty_f.*) {
        .rigid => |r| switch (r.head) {
            .inductive => |h| {
                ind_name = h.name;
                ind_levels = h.levels;
                params = eval.spineApps(self, depth, r.spine) orelse return tc.reject("projection structure type has a non-applicative spine", .{});
            },
            else => return tc.reject("projection structure type is not an inductive", .{}),
        },
        else => return tc.reject("projection structure type is not an inductive", .{}),
    }
    defer self.ctx.bump.free(params);
    const ind = self.env.getInductive(ind_name) orelse return tc.reject("projection structure type is not an inductive", .{});
    const ctor_name = ind.all_ctor_names[0];
    const struct_v = argValue(self, depth, e, structure);
    var cur = eval.constHeadType(self, ctor_name, ind_levels);
    {
        var i: usize = 0;
        const num_params = @as(usize, ind.num_params);
        while (i < num_params) : (i += 1) {
            const cf = eval.forceAll(self, depth, cur);
            switch (cf.*) {
                .pi => |p| {
                    if (i >= params.len) return tc.reject("ran out of param telescope in projection", .{});
                    cur = eval.applyClosure(self, depth, &cf.pi.body, params[i], p.domain);
                },
                else => return tc.reject("ran out of param telescope in projection", .{}),
            }
        }
    }
    {
        var i: usize = 0;
        while (i < idx) : (i += 1) {
            const cf = eval.forceAll(self, depth, cur);
            switch (cf.*) {
                .pi => |p| {
                    if (expr.hasLooseBvar(p.body.body, 0)) {
                        if (struct_ty_is_prop and !conv.isPropType(self, depth, p.domain)) {
                            return tc.reject("projection of a non-proof field from a Prop structure", .{});
                        }
                    }
                    const prior = eval.doProj(self, depth, ind_name, i, struct_v);
                    cur = eval.applyClosure(self, depth, &cf.pi.body, prior, p.domain);
                },
                else => return tc.reject("ran out of constructor telescope in projection", .{}),
            }
        }
    }
    const cf = eval.forceAll(self, depth, cur);
    switch (cf.*) {
        .pi => |p| {
            if (struct_ty_is_prop and !conv.isPropType(self, depth, p.domain)) {
                return tc.reject("projection of a non-proof field from a Prop structure", .{});
            }
            return p.domain;
        },
        else => return tc.reject("ran out of constructor telescope getting projection field", .{}),
    }
}
