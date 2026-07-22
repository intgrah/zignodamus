const std = @import("std");
const conv = @import("conv.zig");
const level_mod = @import("level.zig");
const env = @import("env.zig");
const expr = @import("expr.zig");
const tc = @import("tc.zig");
const util = @import("util.zig");
const value = @import("value.zig");

const ConstructorData = env.ConstructorData;
const Declar = env.Declar;
const RecursorData = env.RecursorData;
const BinderStyle = expr.BinderStyle;
const Expr = expr.Expr;
const TypeChecker = tc.TypeChecker;
const TcCtx = @import("TcCtx.zig");
const NatRed = @import("Dag.zig").NatRed;
const nat = @import("nat.zig");
const BigUintPtr = @import("ptr.zig").BigUintPtr;
const ExprPtr = @import("ptr.zig").ExprPtr;
const LevelPtr = @import("ptr.zig").LevelPtr;
const LevelsPtr = @import("ptr.zig").LevelsPtr;
const NamePtr = @import("ptr.zig").NamePtr;
const StringPtr = @import("ptr.zig").StringPtr;
const Closure = value.Closure;
const Elim = value.Elim;
const RigidHead = value.RigidHead;
const Spine = value.Spine;
const Value = value.Value;
const BigUint = nat.BigUint;
const OnceCell = util.OnceCell;
const E = value.E;
const S = value.S;
const V = value.V;

const RigidKey = struct { u8, u64, u64 };

fn rigidHeadKey(head: *const RigidHead) RigidKey {
    switch (head.*) {
        .b_var => |b| return .{ 0, @as(u64, b.lvl), @intFromPtr(b.ty) },
        .local => |e| return .{ 1, e.getHash(), 0 },
        .axiom => |a| return .{ 2, a.name.getHash(), a.levels.getHash() },
        .ctor => |c| return .{ 3, c.name.getHash(), c.levels.getHash() },
        .recursor => |r| return .{ 4, r.name.getHash(), r.levels.getHash() },
        .quot_const => |q| return .{ 5, q.name.getHash(), q.levels.getHash() },
        .inductive => |i| return .{ 6, i.name.getHash(), i.levels.getHash() },
    }
}

fn elimKey(elim: *const Elim) RigidKey {
    if (elim.isApp()) return .{ 0, @intFromPtr(elim.appV()), 0 };
    return .{ 1, elim.projTyName().getHash(), @as(u64, elim.projIdx()) };
}

const ForceStep = union(enum) {
    reduced: V,
    descend: struct { major: V, args: []const V },
    done: void,
};

const Waiting = struct { rec_val: V, args: []const V };

pub fn mkBvarHc(self: *TypeChecker, level: u32, ty: V) V {
    const key = .{ level, @intFromPtr(ty) };
    const gop = self.tc_cache.bvar_hc.getOrPut(util.smp_allocator, key) catch util.oom();
    if (gop.found_existing) return gop.value_ptr.*;
    const empty = value.spineEmpty();
    const v = value.mkBvarWithEmpty(self.arena, level, ty, empty);
    gop.value_ptr.* = v;
    return v;
}

fn mkUnfoldHc(self: *TypeChecker, name: NamePtr, levels: LevelsPtr, spine: S, head_value: *OnceCell(V)) V {
    const key = .{ name, levels, @intFromPtr(spine), @intFromPtr(head_value) };
    const gop = self.tc_cache.unfold_hc.getOrPut(util.smp_allocator, key) catch util.oom();
    if (gop.found_existing) return gop.value_ptr.*;
    const u = value.mkUnfold(self.arena, name, levels, spine, head_value);
    gop.value_ptr.* = u;
    return u;
}

fn envExtendHc(self: *TypeChecker, parent: E, v: V) E {
    const key = .{ @intFromPtr(parent), @intFromPtr(v) };
    const gop = self.tc_cache.env_hc.getOrPut(util.smp_allocator, key) catch util.oom();
    if (gop.found_existing) return gop.value_ptr.*;
    const e = value.envExtend(self.arena, parent, v);
    gop.value_ptr.* = e;
    return e;
}

inline fn spineSnocHc(self: *TypeChecker, prev: S, elim: Elim) S {
    const ek = elimKey(&elim);
    const key = .{ @intFromPtr(prev), ek[0], ek[1], ek[2] };
    const gop = self.tc_cache.spine_hc.getOrPut(util.smp_allocator, key) catch util.oom();
    if (gop.found_existing) return gop.value_ptr.*;
    const s = value.spineSnoc(self.arena, prev, elim);
    gop.value_ptr.* = s;
    return s;
}

inline fn mkRigidHc(self: *TypeChecker, head: RigidHead, spine: S) V {
    const hk = rigidHeadKey(&head);
    const key = .{ hk[0], hk[1], hk[2], @intFromPtr(spine) };
    const gop = self.tc_cache.rigid_hc.getOrPut(util.smp_allocator, key) catch util.oom();
    if (gop.found_existing) return gop.value_ptr.*;
    const v = value.mkRigid(self.arena, head, spine);
    gop.value_ptr.* = v;
    return v;
}

inline fn mkLamHc(
    self: *TypeChecker,
    binder_name: NamePtr,
    binder_style: BinderStyle,
    binder_type: ExprPtr,
    e: E,
    body_expr: ExprPtr,
) V {
    const key = .{ binder_type, @intFromPtr(e), body_expr };
    const gop = self.tc_cache.lam_hc.getOrPut(util.smp_allocator, key) catch util.oom();
    if (gop.found_existing) return gop.value_ptr.*;
    const v = value.mkLam(self.arena, binder_name, binder_style, binder_type, Closure{ .env = e, .body = body_expr });
    gop.value_ptr.* = v;
    return v;
}

inline fn canonicalizeForSpine(self: *TypeChecker, v: V) V {
    if (v.* == .thunk) {
        return v;
    }
    const key = @intFromPtr(v);
    if (self.tc_cache.canon_cache.get(key)) |c| {
        return c;
    }
    const c = canonCompute(self, v);
    self.tc_cache.canon_cache.put(util.smp_allocator, key, c) catch util.oom();
    return c;
}

fn canonContent(self: *TypeChecker, disc: u8, content: u64, v: V) V {
    const key = .{ disc, content };
    const gop = self.tc_cache.content_hc.getOrPut(util.smp_allocator, key) catch util.oom();
    if (gop.found_existing) return gop.value_ptr.*;
    gop.value_ptr.* = v;
    return v;
}

fn canonSpine(self: *TypeChecker, spine: S) S {
    if (spine == &Spine.empty) return spine;
    const cprev = canonSpine(self, spine.prev);
    const celim = if (spine.elim.isApp())
        Elim.mkApp(canonicalizeForSpine(self, spine.elim.appV()))
    else
        Elim.mkProj(spine.elim.projTyName(), spine.elim.projIdx());
    return spineSnocHc(self, cprev, celim);
}

fn canonCompute(self: *TypeChecker, v: V) V {
    switch (v.*) {
        .lam => |l| return mkLamHc(self, l.binder_name, l.binder_style, l.binder_type, l.body.env, l.body.body),
        .pi => |p| return mkPiHc(self, p.binder_name, p.binder_style, p.domain, p.body.env, p.body.body),
        .sort => |s| return canonContent(self, 0, s.level.getHash(), v),
        .nat_lit => |n| return canonContent(self, 1, n.ptr.getHash(), v),
        .str_lit => |s| return canonContent(self, 2, s.ptr.getHash(), v),
        .rigid => |r| {
            const cspine = canonSpine(self, r.spine);
            return mkRigidHc(self, r.head, cspine);
        },
        .unfold => |u| {
            const hn = u.head.name;
            const hl = u.head.levels;
            const hv = u.head_value;
            const sp = u.spine;
            const cspine = canonSpine(self, sp);
            return mkUnfoldHc(self, hn, hl, cspine, hv);
        },
        .thunk => return v,
    }
}

inline fn mkPiHc(
    self: *TypeChecker,
    binder_name: NamePtr,
    binder_style: BinderStyle,
    domain: V,
    e: E,
    body_expr: ExprPtr,
) V {
    const key = .{ @intFromPtr(domain), @intFromPtr(e), body_expr };
    const gop = self.tc_cache.pi_hc.getOrPut(util.smp_allocator, key) catch util.oom();
    if (gop.found_existing) return gop.value_ptr.*;
    const v = value.mkPi(self.arena, binder_name, binder_style, domain, Closure{ .env = e, .body = body_expr });
    gop.value_ptr.* = v;
    return v;
}

pub fn eval(self: *TypeChecker, depth: u32, e: E, ex: ExprPtr) V {
    const first = ex.asRef();
    const bvars = switch (first.kind) {
        .app => |a| a.num_loose_bvars,
        .pi => |p| p.num_loose_bvars,
        .lambda => |l| l.num_loose_bvars,
        .let => |le| le.data.num_loose_bvars,
        .proj => |pr| pr.num_loose_bvars,
        else => return evalNoCache(self, depth, e, ex),
    };
    if (bvars == 0) {
        return evalClosed(self, depth, e, ex);
    }
    const key = .{ @intFromPtr(e), ex };
    if (self.tc_cache.open_eval_cache.get(key)) |v| {
        return v;
    }
    const v = evalNoCache(self, depth, e, ex);
    const newly = (self.tc_cache.open_eval_seen.fetchPut(util.smp_allocator, ex, {}) catch util.oom()) == null;
    if (!newly) {
        self.tc_cache.open_eval_cache.put(util.smp_allocator, key, v) catch util.oom();
    }
    return v;
}

fn evalClosed(self: *TypeChecker, depth: u32, e: E, ex: ExprPtr) V {
    if (self.tc_cache.closed_eval_cache.get(ex)) |v| {
        return v;
    }
    const v = evalNoCache(self, depth, e, ex);
    self.tc_cache.closed_eval_cache.put(util.smp_allocator, ex, v) catch util.oom();
    return v;
}

fn evalNoCache(self: *TypeChecker, depth: u32, e: E, ex: ExprPtr) V {
    const first = ex.asRef().kind;
    if (first == .app) {
        const fun = first.app.fun;
        const arg = first.app.arg;
        const arg_e = arg.asRef().kind;
        if (arg_e == .app) {
            const f2 = arg_e.app.fun;
            const a2 = arg_e.app.arg;
            const first_fun = fun;
            var all_same = fun == f2;
            var count: u32 = 2;
            var cur = a2;
            var leaf_expr: ExprPtr = undefined;
            while (true) {
                const ce = cur.asRef().kind;
                if (ce == .app) {
                    count += 1;
                    if (all_same and ce.app.fun != first_fun) {
                        all_same = false;
                    }
                    cur = ce.app.arg;
                } else {
                    leaf_expr = cur;
                    break;
                }
            }
            var result = eval(self, depth, e, leaf_expr);
            const nat_ext = self.nat_extension;

            if (all_same) {
                const f_val = blk: {
                    const ff = first_fun.asRef().kind;
                    if (ff == .@"var") {
                        const v = e.lookup(ff.@"var".dbj_idx) orelse @panic("eval: loose bvar");
                        break :blk forceThunk(self, depth, v);
                    } else {
                        break :blk eval(self, depth, e, first_fun);
                    }
                };
                if (f_val.* == .rigid) {
                    const head_copy = f_val.rigid.head;
                    const head_spine = f_val.rigid.spine;
                    const is_nat_ctor = nat_ext and head_copy == .ctor;
                    if (!is_nat_ctor) {
                        var i: u32 = 0;
                        while (i < count) : (i += 1) {
                            const a = canonicalizeForSpine(self, result);
                            const ns = spineSnocHc(self, head_spine, Elim.mkApp(a));
                            result = mkRigidHc(self, head_copy, ns);
                        }
                        return result;
                    }
                }
                var i: u32 = 0;
                while (i < count) : (i += 1) {
                    result = apply(self, depth, f_val, result);
                }
                return result;
            }

            var funs = std.ArrayList(ExprPtr).empty;
            defer funs.deinit(self.ctx.bump);
            funs.ensureTotalCapacity(self.ctx.bump, count) catch util.oom();
            funs.append(self.ctx.bump, fun) catch util.oom();
            funs.append(self.ctx.bump, f2) catch util.oom();
            var cur2 = a2;
            while (true) {
                const ce = cur2.asRef().kind;
                if (ce == .app) {
                    funs.append(self.ctx.bump, ce.app.fun) catch util.oom();
                    cur2 = ce.app.arg;
                } else {
                    break;
                }
            }
            var last_f_expr: ?ExprPtr = null;
            var last_f_val: ?V = null;
            while (funs.pop()) |f_expr| {
                const f_val = blk: {
                    if (last_f_expr != null and last_f_expr.? == f_expr) {
                        break :blk last_f_val.?;
                    } else {
                        const fe = f_expr.asRef().kind;
                        const v = if (fe == .@"var") v_blk: {
                            const lv = e.lookup(fe.@"var".dbj_idx) orelse @panic("eval: loose bvar");
                            break :v_blk forceThunk(self, depth, lv);
                        } else eval(self, depth, e, f_expr);
                        last_f_expr = f_expr;
                        last_f_val = v;
                        break :blk v;
                    }
                };
                if (f_val.* == .rigid) {
                    const head_copy = f_val.rigid.head;
                    const is_nat_ctor = nat_ext and head_copy == .ctor;
                    if (!is_nat_ctor) {
                        const sp = f_val.rigid.spine;
                        const a = canonicalizeForSpine(self, result);
                        const ns = spineSnocHc(self, sp, Elim.mkApp(a));
                        result = mkRigidHc(self, head_copy, ns);
                        continue;
                    }
                }
                result = apply(self, depth, f_val, result);
            }
            return result;
        }
        const f = eval(self, depth, e, fun);
        const trivial = switch (arg.asRef().kind) {
            .@"var", .sort, .@"const", .nat_lit, .string_lit, .local => true,
            else => false,
        };
        if (f.* == .lam) {
            const clo = f.lam.body;
            const a = if (trivial) eval(self, depth, e, arg) else value.mkThunk(self.arena, e, arg);
            const clo_env = clo.env;
            const clo_body = clo.body;
            const new_env = envExtendHc(self, clo_env, a);
            return eval(self, depth, new_env, clo_body);
        }
        const a = if (trivial) eval(self, depth, e, arg) else value.mkThunk(self.arena, e, arg);
        return apply(self, depth, f, a);
    }
    switch (first) {
        .@"var" => |vr| {
            const v = e.lookup(vr.dbj_idx) orelse @panic("eval: loose bvar");
            return forceThunk(self, depth, v);
        },
        .sort => |s| return value.mkSort(self.arena, level_mod.simplify(self.ctx, s.level)),
        .@"const" => |c| return evalConst(self, c.name, c.levels),
        .app => unreachable,
        .lambda => |l| return value.mkLam(self.arena, l.binder_name, l.binder_style, l.binder_type, Closure{ .env = e, .body = l.body }),
        .pi => |p| {
            const dom = switch (p.binder_type.asRef().kind) {
                .@"var", .sort, .@"const", .nat_lit, .string_lit, .local => eval(self, depth, e, p.binder_type),
                else => value.mkThunk(self.arena, e, p.binder_type),
            };
            return value.mkPi(self.arena, p.binder_name, p.binder_style, dom, Closure{ .env = e, .body = p.body });
        },
        .let => {
            var cur_env = e;
            var cursor = ex;
            while (true) {
                const ce = cursor.asRef().kind;
                if (ce == .let) {
                    const vv = eval(self, depth, cur_env, ce.let.data.val);
                    cur_env = envExtendHc(self, cur_env, vv);
                    cursor = ce.let.data.body;
                } else {
                    break;
                }
            }
            return eval(self, depth, cur_env, cursor);
        },
        .local => {
            if (self.local_v_cache.get(ex)) |v| {
                return v;
            }
            const empty = value.spineEmpty();
            const v = value.mkLocalWithEmpty(self.arena, ex, empty);
            self.local_v_cache.put(util.smp_allocator, ex, v) catch util.oom();
            return v;
        },
        .proj => |pr| {
            const vs = eval(self, depth, e, pr.structure);
            return doProj(self, depth, pr.ty_name, pr.idx, vs);
        },
        .nat_lit => |n| return value.mkNatlit(self.arena, n.ptr),
        .string_lit => |s| return value.mkStrlit(self.arena, s.ptr),
    }
}

pub fn evalConst(self: *TypeChecker, name: NamePtr, levels: LevelsPtr) V {
    if (self.tc_cache.const_head_value_cache.get(.{ name, levels })) |cached| {
        return cached;
    }
    const empty = value.spineEmpty();
    const v = if (self.env.getDeclar(name)) |dptr| switch (dptr.*) {
        .definition, .theorem => blk: {
            const cell = self.arena.create(OnceCell(V));
            cell.* = OnceCell(V).empty;
            break :blk value.mkUnfoldHeadWithEmpty(self.arena, name, levels, cell, empty);
        },
        .constructor => value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .ctor = .{ .name = name, .levels = levels } }, empty),
        .recursor => value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .recursor = .{ .name = name, .levels = levels } }, empty),
        .quot => value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .quot_const = .{ .name = name, .levels = levels } }, empty),
        .inductive => value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .inductive = .{ .name = name, .levels = levels } }, empty),
        .axiom, .opaque_ => value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .axiom = .{ .name = name, .levels = levels } }, empty),
    } else value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .axiom = .{ .name = name, .levels = levels } }, empty);
    self.tc_cache.const_head_value_cache.put(util.smp_allocator, .{ name, levels }, v) catch util.oom();
    return v;
}

pub fn constResultLevel(self: *TypeChecker, name: NamePtr, levels: LevelsPtr) ?LevelPtr {
    if (self.tc_cache.const_result_level_cache.get(.{ name, levels })) |cached| {
        return cached;
    }
    const head_ty = constHeadType(self, name, levels);
    var cur = head_ty;
    var binder_depth: u32 = 0;
    while (true) {
        const cur_f = forceAll(self, binder_depth, cur);
        switch (cur_f.*) {
            .pi => |p| {
                const fresh = mkBvarHc(self, binder_depth, p.domain);
                cur = applyClosure(self, binder_depth + 1, &cur_f.pi.body, fresh);
                binder_depth += 1;
            },
            .sort => |s| {
                const l = level_mod.simplify(self.ctx, s.level);
                self.tc_cache.const_result_level_cache.put(util.smp_allocator, .{ name, levels }, l) catch util.oom();
                return l;
            },
            else => return null,
        }
    }
}

pub fn constHeadType(self: *TypeChecker, name: NamePtr, levels: LevelsPtr) V {
    if (self.tc_cache.const_head_type_cache.get(.{ name, levels })) |cached| {
        return cached;
    }
    const info = (self.env.getDeclar(name) orelse @panic("const_head_type: unknown const")).info().*;
    const ty_e = expr.substExprLevels(self.ctx, info.ty, info.uparams, levels);
    const empty = value.envEmpty();
    const v = eval(self, 0, empty, ty_e);
    self.tc_cache.const_head_type_cache.put(util.smp_allocator, .{ name, levels }, v) catch util.oom();
    return v;
}

pub inline fn forceThunk(self: *TypeChecker, depth: u32, v: V) V {
    if (v.* == .thunk) {
        const t = v.thunk;
        if (t.forced.get()) |r| {
            return r;
        }
        const r = eval(self, depth, t.env, t.expr);
        v.thunk.forced.set(r);
        return r;
    }
    return v;
}

pub fn lamDomain(self: *TypeChecker, depth: u32, v: V) V {
    switch (v.*) {
        .lam => |l| {
            if (l.domain.get()) |d| {
                return d;
            }
            const e = l.body.env;
            const bt = l.binder_type;
            const d = eval(self, depth, e, bt);
            v.lam.domain.set(d);
            return d;
        },
        .pi => |p| return p.domain,
        else => @panic("lam_domain: not a Lam/Pi"),
    }
}

pub inline fn apply(self: *TypeChecker, depth: u32, f: V, a: V) V {
    switch (f.*) {
        .lam => |l| {
            const clo_env = l.body.env;
            const clo_body = l.body.body;
            const e = envExtendHc(self, clo_env, a);
            return eval(self, depth, e, clo_body);
        },
        .rigid => |r| {
            const head_copy = r.head;
            if (self.nat_extension) {
                if (head_copy == .ctor) {
                    const name = head_copy.ctor.name;
                    if (eqOpt(self.ctx.export_file.name_cache.nat_succ, name)) {
                        const new_spine = value.spineSnoc(self.arena, r.spine, Elim.mkApp(a));
                        return tryFireRigid(self, depth, head_copy, new_spine);
                    }
                }
            }
            const ca = canonicalizeForSpine(self, a);
            const new_spine = spineSnocHc(self, r.spine, Elim.mkApp(ca));
            return mkRigidHc(self, head_copy, new_spine);
        },
        .unfold => |u| {
            const head = u.head;
            const head_value = u.head_value;
            const spine = u.spine;
            if (self.nat_extension and isNatRedName(self, head.name)) {
                const new_spine = spineSnocHc(self, spine, Elim.mkApp(a));
                if (spineApps(self, depth, new_spine)) |args| {
                    if (doNatRedShallow(self, depth, head.name, args)) |r| {
                        return r;
                    }
                }
                return mkUnfoldHc(self, head.name, head.levels, new_spine, head_value);
            }
            const ca = canonicalizeForSpine(self, a);
            const new_spine = spineSnocHc(self, spine, Elim.mkApp(ca));
            return mkUnfoldHc(self, head.name, head.levels, new_spine, head_value);
        },
        else => @panic("apply: ill-typed application"),
    }
}

pub fn applyClosure(self: *TypeChecker, depth: u32, clo: *const Closure, v: V) V {
    const clo_env = clo.env;
    const clo_body = clo.body;
    const e = envExtendHc(self, clo_env, v);
    return eval(self, depth, e, clo_body);
}

fn tryFireRigid(self: *TypeChecker, depth: u32, head: RigidHead, spine: S) V {
    if (self.ctx.export_file.config.nat_extension) {
        if (head == .ctor) {
            const name = head.ctor.name;
            if (eqOpt(self.ctx.export_file.name_cache.nat_succ, name)) {
                if (spine != &Spine.empty and spine.prev == &Spine.empty and spine.elim.isApp()) {
                    const arg = spine.elim.appV();
                    if (valueToBignumAt(self, depth, arg, false)) |n| {
                        defer nat.free(n);
                        const succ_lit = nat.succ(n);
                        if (TcCtx.allocBignum(self.ctx, succ_lit)) |p| {
                            return value.mkNatlit(self.arena, p);
                        }
                    }
                }
            }
        }
    }
    return mkRigidHc(self, head, spine);
}

fn isNatRedName(self: *TypeChecker, name: NamePtr) bool {
    return self.ctx.export_file.name_cache.nat_red.contains(name);
}

fn natRedDefer(self: *TypeChecker, depth: u32, name: NamePtr, args: []const V) bool {
    const structural_on_second = switch (self.ctx.export_file.name_cache.nat_red.get(name) orelse return false) {
        .add, .sub, .mul, .pow => true,
        else => false,
    };
    if (!structural_on_second or args.len != 2) {
        return false;
    }
    const f = forceThunk(self, depth, args[1]);
    if (f.* == .nat_lit) {
        return f.nat_lit.ptr.asRef().bitCountAbs() > 8;
    } else {
        return false;
    }
}

pub fn valueType(self: *TypeChecker, depth: u32, v0: V) V {
    const v = forceThunk(self, depth, v0);
    switch (v.*) {
        .sort => |s| {
            const sc = TcCtx.succ(self.ctx, s.level);
            return value.mkSort(self.arena, level_mod.simplify(self.ctx, sc));
        },
        .nat_lit => {
            const n = self.ctx.export_file.name_cache.nat orelse @panic("value_type: Nat name missing");
            const levels = TcCtx.allocLevels(self.ctx, &.{});
            return value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .inductive = .{ .name = n, .levels = levels } }, value.spineEmpty());
        },
        .str_lit => {
            const n = self.ctx.export_file.name_cache.string orelse @panic("value_type: String name missing");
            const levels = TcCtx.allocLevels(self.ctx, &.{});
            return value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .inductive = .{ .name = n, .levels = levels } }, value.spineEmpty());
        },
        .rigid => |r| {
            const head_ty = rigidHeadType(self, depth, r.head);
            return spineType(self, depth, head_ty, r.head, r.spine);
        },
        .unfold => |u| {
            const head_ty = constHeadType(self, u.head.name, u.head.levels);
            const cell = self.arena.create(OnceCell(V));
            cell.* = OnceCell(V).empty;
            _ = cell.set(head_ty);
            const prev = value.mkUnfoldHeadWithEmpty(self.arena, u.head.name, u.head.levels, cell, value.spineEmpty());
            return spineTypeWithValue(self, depth, head_ty, prev, u.spine);
        },
        .pi, .lam => @panic("value_type: Pi/Lam not supported"),
        .thunk => @panic("value_type: Thunk after force"),
    }
}

fn rigidHeadType(self: *TypeChecker, depth: u32, head: RigidHead) V {
    switch (head) {
        .b_var => |b| return b.ty,
        .local => |e| {
            const bt = switch (e.asRef().kind) {
                .local => |l| l.binder_type,
                else => @panic("value_type: Local Expr"),
            };
            const empty = value.envEmpty();
            return eval(self, depth, empty, bt);
        },
        .axiom => |h| return constHeadType(self, h.name, h.levels),
        .ctor => |h| return constHeadType(self, h.name, h.levels),
        .recursor => |h| return constHeadType(self, h.name, h.levels),
        .quot_const => |h| return constHeadType(self, h.name, h.levels),
        .inductive => |h| return constHeadType(self, h.name, h.levels),
    }
}

fn spineType(self: *TypeChecker, depth: u32, ty0: V, head: RigidHead, spine: S) V {
    var ty = ty0;
    var prefix = value.spineEmpty();
    const elems = spine.toVec(util.smp_allocator);
    defer util.smp_allocator.free(elems);
    for (elems) |elim| {
        if (elim.isApp()) {
            const a = elim.appV();
            const ty_f = forceAll(self, depth, ty);
            switch (ty_f.*) {
                .pi => ty = applyClosure(self, depth, &ty_f.pi.body, a),
                else => @panic("spine_type: expected Pi"),
            }
            prefix = value.spineSnoc(self.arena, prefix, Elim.mkApp(a));
        } else {
            const prev = value.mkRigid(self.arena, head, prefix);
            ty = projFieldTypeWith(self, depth, prev, ty, elim.projTyName(), elim.projIdx()) orelse @panic("spine_type: bad proj");
            prefix = value.spineSnoc(self.arena, prefix, Elim.mkProj(elim.projTyName(), elim.projIdx()));
        }
    }
    return ty;
}

fn spineTypeWithValue(self: *TypeChecker, depth: u32, ty0: V, prev_head: V, spine: S) V {
    var ty = ty0;
    var prev = prev_head;
    const elems = spine.toVec(util.smp_allocator);
    defer util.smp_allocator.free(elems);
    for (elems) |elim| {
        if (elim.isApp()) {
            const a = elim.appV();
            const ty_f = forceAll(self, depth, ty);
            switch (ty_f.*) {
                .pi => ty = applyClosure(self, depth, &ty_f.pi.body, a),
                else => @panic("spine_type_with_value: expected Pi"),
            }
            prev = apply(self, depth, prev, a);
        } else {
            ty = projFieldTypeWith(self, depth, prev, ty, elim.projTyName(), elim.projIdx()) orelse @panic("spine_type_with_value: bad proj");
            prev = doProj(self, depth, elim.projTyName(), elim.projIdx(), prev);
        }
    }
    return ty;
}

pub fn whnfHead(self: *TypeChecker, depth: u32, v: V) V {
    var cur = v;
    while (true) {
        cur = forceThunk(self, depth, cur);
        switch (cur.*) {
            .unfold => {
                const next = unfoldValue(self, depth, cur);
                if (next == cur) {
                    return cur;
                }
                cur = next;
            },
            .rigid => |r| switch (r.head) {
                .recursor, .quot_const => {
                    if (iotaValue(self, depth, cur)) |next| {
                        cur = next;
                    } else {
                        return cur;
                    }
                },
                else => return cur,
            },
            else => return cur,
        }
    }
}

pub fn doProj(self: *TypeChecker, depth: u32, ty_name: NamePtr, idx: usize, v0: V) V {
    const v = whnfHead(self, depth, v0);
    switch (v.*) {
        .rigid => |r| switch (r.head) {
            .ctor => |ct| {
                if (self.env.getConstructor(ct.name)) |cd| {
                    if (cd.inductive_name == ty_name) {
                        const np = @as(usize, cd.num_params);
                        if (r.spine.get(np + idx)) |elim| {
                            if (elim.isApp()) {
                                return forceThunk(self, depth, elim.appV());
                            }
                        }
                    }
                }
                return projExtendSpine(self, ty_name, idx, v);
            },
            else => return projExtendSpine(self, ty_name, idx, v),
        },
        .nat_lit => |n| {
            const ctor = natLitToCtorVal(self, depth, n.ptr) orelse @panic("do_proj: nat_lit_to_ctor_val failed");
            return doProj(self, depth, ty_name, idx, ctor);
        },
        .str_lit => |s| {
            const ctor = strLitToCtorVal(self, depth, s.ptr) orelse @panic("do_proj: str_lit_to_ctor_val failed");
            return doProj(self, depth, ty_name, idx, ctor);
        },
        .unfold => return projExtendSpine(self, ty_name, idx, v),
        .thunk => @panic("do_proj: Thunk after force_all"),
        else => @panic("do_proj: not a neutral"),
    }
}

fn projExtendSpine(self: *TypeChecker, ty_name: NamePtr, idx: usize, v: V) V {
    switch (v.*) {
        .rigid => |r| {
            const h = r.head;
            const sp = r.spine;
            const ns = spineSnocHc(self, sp, Elim.mkProj(ty_name, idx));
            return mkRigidHc(self, h, ns);
        },
        .unfold => |u| {
            const hn = u.head.name;
            const hl = u.head.levels;
            const hv = u.head_value;
            const sp = u.spine;
            const ns = spineSnocHc(self, sp, Elim.mkProj(ty_name, idx));
            return mkUnfoldHc(self, hn, hl, ns, hv);
        },
        else => unreachable,
    }
}

pub fn projFieldTypeWith(
    self: *TypeChecker,
    depth: u32,
    struct_value: V,
    struct_ty0: V,
    ty_name: NamePtr,
    idx: usize,
) ?V {
    const struct_ty = forceAll(self, depth, struct_ty0);
    var ind_name: NamePtr = undefined;
    var ind_levels: LevelsPtr = undefined;
    var args: []const V = undefined;
    switch (struct_ty.*) {
        .rigid => |r| switch (r.head) {
            .inductive => |h| {
                const aa = spineApps(self, depth, r.spine) orelse return null;
                ind_name = h.name;
                ind_levels = h.levels;
                args = aa;
            },
            else => return null,
        },
        else => return null,
    }
    defer self.ctx.bump.free(args);
    if (ind_name != ty_name) {
        return null;
    }
    const ind = self.env.getInductive(ind_name) orelse return null;
    const ctor_name = ind.all_ctor_names[0];
    const ctor_info = switch ((self.env.getDeclar(ctor_name) orelse return null).*) {
        .constructor => |c| c.info,
        else => return null,
    };
    const ctor_ty_e = expr.substExprLevels(self.ctx, ctor_info.ty, ctor_info.uparams, ind_levels);
    var cur = blk: {
        const empty = value.envEmpty();
        break :blk eval(self, depth, empty, ctor_ty_e);
    };
    const num_params = @as(usize, ind.num_params);
    var i: usize = 0;
    while (i < num_params) : (i += 1) {
        const cf = forceAll(self, depth, cur);
        switch (cf.*) {
            .pi => {
                if (i >= args.len) return null;
                const arg = args[i];
                cur = applyClosure(self, depth, &cf.pi.body, arg);
            },
            else => return null,
        }
    }
    i = 0;
    while (i < idx) : (i += 1) {
        const cf = forceAll(self, depth, cur);
        switch (cf.*) {
            .pi => {
                const prior = doProj(self, depth, ty_name, i, struct_value);
                cur = applyClosure(self, depth, &cf.pi.body, prior);
            },
            else => return null,
        }
    }
    const cf = forceAll(self, depth, cur);
    switch (cf.*) {
        .pi => |p| return p.domain,
        else => return null,
    }
}

pub fn forceAll(self: *TypeChecker, depth: u32, v: V) V {
    var cur = v;
    var waiting = std.ArrayList(Waiting).empty;
    defer waiting.deinit(self.ctx.bump);
    while (true) {
        while (true) {
            switch (cur.*) {
                .thunk => cur = forceThunk(self, depth, cur),
                .unfold => {
                    const next = unfoldValue(self, depth, cur);
                    if (next == cur) {
                        break;
                    }
                    cur = next;
                },
                else => break,
            }
        }
        const step = switch (cur.*) {
            .rigid => |r| switch (r.head) {
                .recursor, .quot_const => iotaStep(self, depth, cur),
                else => ForceStep.done,
            },
            else => ForceStep.done,
        };
        switch (step) {
            .reduced => |next| {
                cur = next;
                continue;
            },
            .descend => |d| {
                waiting.append(self.ctx.bump, .{ .rec_val = cur, .args = d.args }) catch util.oom();
                cur = d.major;
                continue;
            },
            .done => {},
        }
        while (true) {
            if (waiting.pop()) |w| {
                const rec_val = w.rec_val;
                const key = @intFromPtr(rec_val);
                if (fireValue(self, depth, rec_val, w.args, cur)) |res| {
                    self.ctx.bump.free(w.args);
                    self.tc_cache.iota_cache.put(util.smp_allocator, key, res) catch util.oom();
                    cur = res;
                    break;
                } else {
                    self.ctx.bump.free(w.args);
                    _ = self.tc_cache.iota_stuck.fetchPut(util.smp_allocator, key, {}) catch util.oom();
                    cur = rec_val;
                }
            } else {
                return cur;
            }
        }
    }
}

fn iotaStep(self: *TypeChecker, depth: u32, v: V) ForceStep {
    const key = @intFromPtr(v);
    if (self.tc_cache.iota_stuck.contains(key)) {
        return ForceStep.done;
    }
    if (self.tc_cache.iota_cache.get(key)) |c| {
        return ForceStep{ .reduced = c };
    }
    switch (v.*) {
        .rigid => |r| switch (r.head) {
            .recursor => |h| {
                const e = self.env;
                const rec = e.getRecursor(h.name) orelse return ForceStep.done;
                const args = spineApps(self, depth, r.spine) orelse return ForceStep.done;
                if (args.len <= rec.majorIdx()) {
                    self.ctx.bump.free(args);
                    return ForceStep.done;
                }
                if (kPreReduce(self, depth, rec, h.levels, args)) |res| {
                    self.ctx.bump.free(args);
                    self.tc_cache.iota_cache.put(util.smp_allocator, key, res) catch util.oom();
                    return ForceStep{ .reduced = res };
                }
                const major_h = stripHead(self, depth, args[rec.majorIdx()]);
                if (isIotaReducible(self, major_h)) {
                    return ForceStep{ .descend = .{ .major = major_h, .args = args } };
                }
                defer self.ctx.bump.free(args);
                if (fireRecursor(self, depth, rec, h.levels, args, major_h)) |res| {
                    self.tc_cache.iota_cache.put(util.smp_allocator, key, res) catch util.oom();
                    return ForceStep{ .reduced = res };
                } else {
                    _ = self.tc_cache.iota_stuck.fetchPut(util.smp_allocator, key, {}) catch util.oom();
                    return ForceStep.done;
                }
            },
            .quot_const => |h| {
                const cache = self.ctx.export_file.name_cache;
                const qmk_pos: usize = if (eqOpt(cache.quot_lift, h.name))
                    5
                else if (eqOpt(cache.quot_ind, h.name))
                    4
                else
                    return ForceStep.done;
                const name = h.name;
                const args = spineApps(self, depth, r.spine) orelse return ForceStep.done;
                if (qmk_pos >= args.len) {
                    self.ctx.bump.free(args);
                    return ForceStep.done;
                }
                const major = args[qmk_pos];
                const major_h = stripHead(self, depth, major);
                if (isIotaReducible(self, major_h)) {
                    return ForceStep{ .descend = .{ .major = major_h, .args = args } };
                }
                defer self.ctx.bump.free(args);
                if (fireQuot(self, depth, name, args, major_h)) |res| {
                    self.tc_cache.iota_cache.put(util.smp_allocator, key, res) catch util.oom();
                    return ForceStep{ .reduced = res };
                } else {
                    _ = self.tc_cache.iota_stuck.fetchPut(util.smp_allocator, key, {}) catch util.oom();
                    return ForceStep.done;
                }
            },
            else => return ForceStep.done,
        },
        else => return ForceStep.done,
    }
}

fn stripHead(self: *TypeChecker, depth: u32, v: V) V {
    var cur = v;
    while (true) {
        switch (cur.*) {
            .thunk => cur = forceThunk(self, depth, cur),
            .unfold => {
                const next = unfoldValue(self, depth, cur);
                if (next == cur) {
                    return cur;
                }
                cur = next;
            },
            else => return cur,
        }
    }
}

fn isIotaReducible(self: *TypeChecker, v: V) bool {
    switch (v.*) {
        .rigid => |r| switch (r.head) {
            .recursor => return true,
            .quot_const => |h| {
                const cache = self.ctx.export_file.name_cache;
                return eqOpt(cache.quot_lift, h.name) or eqOpt(cache.quot_ind, h.name);
            },
            else => return false,
        },
        else => return false,
    }
}

fn fireValue(self: *TypeChecker, depth: u32, rec_val: V, args: []const V, major: V) ?V {
    switch (rec_val.*) {
        .rigid => |r| switch (r.head) {
            .recursor => |h| {
                const rec = self.env.getRecursor(h.name) orelse return null;
                if (args.len <= rec.majorIdx()) {
                    return null;
                }
                return fireRecursor(self, depth, rec, h.levels, args, major);
            },
            .quot_const => |h| {
                return fireQuot(self, depth, h.name, args, major);
            },
            else => return null,
        },
        else => return null,
    }
}

pub fn unfoldValue(self: *TypeChecker, depth: u32, v: V) V {
    return unfoldValueGo(self, depth, v, false);
}

pub fn unfoldValueDemand(self: *TypeChecker, depth: u32, v: V) V {
    return unfoldValueGo(self, depth, v, self.tc_cache.probe_depth == 0);
}

fn unfoldValueGo(self: *TypeChecker, depth: u32, v: V, force: bool) V {
    if (v.* == .unfold) {
        const u = v.unfold;
        if (u.forced.get()) |f| {
            return f;
        }
        if (self.nat_extension and isNatRedName(self, u.head.name)) {
            if (spineApps(self, depth, u.spine)) |args| {
                defer self.ctx.bump.free(args);
                if (doNatRed(self, depth, u.head.name, args)) |r| {
                    v.unfold.forced.set(r);
                    return r;
                }
                if (!force and natRedDefer(self, depth, u.head.name, args)) {
                    return v;
                }
            }
        }
        const head_value = if (u.head_value.get()) |hv|
            hv
        else if (unfoldConst(self, u.head.name, u.head.levels)) |hv| blk: {
            _ = v.unfold.head_value.set(hv);
            break :blk hv;
        } else {
            v.unfold.forced.set(v);
            return v;
        };
        const spine = u.spine;
        var cur = head_value;
        const elems = spine.toVec(util.smp_allocator);
        defer util.smp_allocator.free(elems);
        for (elems) |elim| {
            cur = if (elim.isApp())
                apply(self, depth, cur, elim.appV())
            else
                doProj(self, depth, elim.projTyName(), elim.projIdx(), cur);
        }
        v.unfold.forced.set(cur);
        return cur;
    }
    return v;
}

pub fn iotaValue(self: *TypeChecker, depth: u32, v: V) ?V {
    const v_key = @intFromPtr(v);
    if (self.tc_cache.iota_stuck.contains(v_key)) {
        return null;
    }
    if (self.tc_cache.iota_cache.get(v_key)) |cached| {
        return cached;
    }
    const result = switch (v.*) {
        .rigid => |r| switch (r.head) {
            .recursor => |h| res: {
                const args = spineApps(self, depth, r.spine) orelse break :res @as(?V, null);
                defer self.ctx.bump.free(args);
                break :res doRecursorIota(self, depth, h.name, h.levels, args);
            },
            .quot_const => |h| res: {
                const args = spineApps(self, depth, r.spine) orelse break :res @as(?V, null);
                defer self.ctx.bump.free(args);
                break :res doQuotIota(self, depth, h.name, args);
            },
            else => @as(?V, null),
        },
        else => @as(?V, null),
    };
    if (result) |rr| {
        self.tc_cache.iota_cache.put(util.smp_allocator, v_key, rr) catch util.oom();
    } else {
        _ = self.tc_cache.iota_stuck.fetchPut(util.smp_allocator, v_key, {}) catch util.oom();
    }
    return result;
}

pub fn unfoldConst(self: *TypeChecker, name: NamePtr, levels: LevelsPtr) ?V {
    if (self.tc_cache.unfold_const_cache.get(.{ name, levels })) |cached| {
        return cached;
    }
    const dv = self.env.getDeclarVal(name) orelse return null;
    const def_uparams = dv[0];
    const def_value = dv[1];
    if (levels.asRef().len != def_uparams.asRef().len) {
        return null;
    }
    const body = expr.substExprLevels(self.ctx, def_value, def_uparams, levels);
    const empty = value.envEmpty();
    const v = eval(self, 0, empty, body);
    self.tc_cache.unfold_const_cache.put(util.smp_allocator, .{ name, levels }, v) catch util.oom();
    return v;
}

pub fn spineApps(self: *TypeChecker, depth: u32, spine: S) ?[]const V {
    const n: usize = @intCast(spine.length);
    const slice = self.ctx.bump.alloc(V, n) catch util.oom();
    var i: usize = n;
    var cur: S = spine;
    while (cur != &Spine.empty) {
        if (cur.elim.isApp()) {
            i -= 1;
            slice[i] = forceThunk(self, depth, cur.elim.appV());
        } else {
            self.ctx.bump.free(slice);
            return null;
        }
        cur = cur.prev;
    }
    return slice;
}

fn doRecursorIota(self: *TypeChecker, depth: u32, name: NamePtr, levels: LevelsPtr, args: []const V) ?V {
    const e = self.env;
    const rec = e.getRecursor(name) orelse return null;
    if (args.len <= rec.majorIdx()) {
        return null;
    }
    if (kPreReduce(self, depth, rec, levels, args)) |r| {
        return r;
    }
    const major = whnfHead(self, depth, args[rec.majorIdx()]);
    return fireRecursor(self, depth, rec, levels, args, major);
}

fn kPreReduce(self: *TypeChecker, depth: u32, rec: *const RecursorData, levels: LevelsPtr, args: []const V) ?V {
    if (!rec.is_k) {
        return null;
    }
    const raw = forceThunk(self, depth, args[rec.majorIdx()]);
    const kctor = tryKReduce(self, depth, raw, rec) orelse return null;
    return fireRecursor(self, depth, rec, levels, args, kctor);
}

fn fireRecursor(
    self: *TypeChecker,
    depth: u32,
    rec: *const RecursorData,
    levels: LevelsPtr,
    args: []const V,
    major0: V,
) ?V {
    if (self.ctx.export_file.config.nat_extension and
        firstInductiveEqNat(self, rec))
    {
        if (major0.* == .nat_lit) {
            return natRecNatlit(self, depth, args, major0.nat_lit.ptr, rec, levels);
        }
    }
    const major = blk: {
        if (majorToCtor(self, depth, major0)) |m| break :blk m;
        if (tryKReduce(self, depth, major0, rec)) |m| break :blk m;
        if (tryStructEtaReduce(self, depth, major0, rec)) |m| break :blk m;
        break :blk major0;
    };
    const uc = unwrapCtorApp(self, depth, major) orelse return null;
    const ctor_name = uc[0];
    const ctor_args = uc[1];
    defer self.ctx.bump.free(ctor_args);
    var rec_rule_opt: ?env.RecRule = null;
    for (rec.rec_rules) |r| {
        if (r.ctor_name == ctor_name) {
            rec_rule_opt = r;
            break;
        }
    }
    const rec_rule = rec_rule_opt orelse return null;
    if (ctor_args.len < @as(usize, rec_rule.ctor_telescope_size_wo_params)) {
        return null;
    }
    const num_extra = ctor_args.len - @as(usize, rec_rule.ctor_telescope_size_wo_params);
    const cache_key = .{ rec_rule.val, levels };
    var result = if (self.tc_cache.rec_rule_cache.get(cache_key)) |v|
        v
    else blk: {
        const body = expr.substExprLevels(self.ctx, rec_rule.val, rec.info.uparams, levels);
        const empty = value.envEmpty();
        const v = eval(self, 0, empty, body);
        self.tc_cache.rec_rule_cache.put(util.smp_allocator, cache_key, v) catch util.oom();
        break :blk v;
    };
    const nprefix = @as(usize, rec.num_params + rec.num_motives + rec.num_minors);
    for (args[0..nprefix]) |a| {
        result = apply(self, depth, result, a);
    }
    for (ctor_args[num_extra..]) |a| {
        result = apply(self, depth, result, a);
    }
    for (args[rec.majorIdx() + 1 ..]) |a| {
        result = apply(self, depth, result, a);
    }
    return result;
}

fn firstInductiveEqNat(self: *TypeChecker, rec: *const RecursorData) bool {
    if (rec.all_inductives.len == 0) return false;
    return eqOpt(self.ctx.export_file.name_cache.nat, rec.all_inductives[0]);
}

fn natRecNatlit(
    self: *TypeChecker,
    depth: u32,
    args: []const V,
    n_ptr: BigUintPtr,
    rec: *const RecursorData,
    levels: LevelsPtr,
) V {
    const n = nat.clone(n_ptr.asRef());
    defer nat.free(n);
    const nparams = @as(usize, rec.num_params);
    const nmotives = @as(usize, rec.num_motives);
    const major_idx = rec.majorIdx();
    const zero_case = args[nparams + nmotives];
    const succ_case = forceThunk(self, depth, args[nparams + nmotives + 1]);
    var result = if (n.eqlZero())
        zero_case
    else blk: {
        const pred = nat.pred(n);
        const pred_ptr = TcCtx.allocBignum(self.ctx, pred) orelse @panic("nat_rec_natlit: alloc pred");
        const pred_val = value.mkNatlit(self.arena, pred_ptr);
        const empty = value.spineEmpty();
        var ih = value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .recursor = .{ .name = rec.info.name, .levels = levels } }, empty);
        for (args[0..major_idx]) |a| {
            ih = apply(self, depth, ih, a);
        }
        ih = apply(self, depth, ih, pred_val);
        const stepped = apply(self, depth, succ_case, pred_val);
        break :blk apply(self, depth, stepped, ih);
    };
    for (args[major_idx + 1 ..]) |a| {
        result = apply(self, depth, result, a);
    }
    return result;
}

fn tryStructEtaReduce(self: *TypeChecker, depth: u32, major: V, rec: *const RecursorData) ?V {
    switch (major.*) {
        .rigid, .unfold => {},
        else => return null,
    }
    const rec_induct = expr.getMajorInduct(rec) orelse return null;
    if (!self.env.canBeStruct(rec_induct)) {
        return null;
    }
    const key = .{ @intFromPtr(major), rec_induct };
    if (self.tc_cache.struct_eta_cache.get(key)) |cached| {
        return cached;
    }
    const result = tryStructEtaReduceUncached(self, depth, major, rec, rec_induct);
    self.tc_cache.struct_eta_cache.put(util.smp_allocator, key, result) catch util.oom();
    return result;
}

fn tryStructEtaReduceUncached(
    self: *TypeChecker,
    depth: u32,
    major: V,
    rec: *const RecursorData,
    rec_induct: NamePtr,
) ?V {
    const major_ty = valueType(self, depth, major);
    const major_ty_f = forceAll(self, depth, major_ty);
    const ua = unwrapInductiveApp(self, depth, major_ty_f) orelse return null;
    const ty_name = ua[0];
    const ty_levels = ua[1];
    const ty_args = ua[2];
    defer self.ctx.bump.free(ty_args);
    if (ty_name != rec_induct) {
        return null;
    }
    const ind = self.env.getInductive(ty_name) orelse return null;
    const ctor_name = ind.all_ctor_names[0];
    const ctor_data = self.env.getConstructor(ctor_name) orelse return null;
    const num_fields = @as(usize, ctor_data.num_fields);
    const np = @as(usize, rec.num_params);
    var new_ctor = value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .ctor = .{ .name = ctor_name, .levels = ty_levels } }, value.spineEmpty());
    {
        var i: usize = 0;
        const take = @min(np, ty_args.len);
        while (i < take) : (i += 1) {
            new_ctor = apply(self, depth, new_ctor, ty_args[i]);
        }
    }
    var i: usize = 0;
    while (i < num_fields) : (i += 1) {
        const proj = doProj(self, depth, ty_name, i, major);
        new_ctor = apply(self, depth, new_ctor, proj);
    }
    return new_ctor;
}

fn tryKReduce(self: *TypeChecker, depth: u32, major: V, rec: *const RecursorData) ?V {
    if (!rec.is_k) {
        return null;
    }
    switch (major.*) {
        .rigid, .unfold => {},
        else => return null,
    }
    const major_ty = valueType(self, depth, major);
    const major_ty_f = forceAll(self, depth, major_ty);
    const ua = unwrapInductiveApp(self, depth, major_ty_f) orelse return null;
    const ty_name = ua[0];
    const ty_levels = ua[1];
    const ty_args = ua[2];
    defer self.ctx.bump.free(ty_args);
    const rec_induct = expr.getMajorInduct(rec) orelse return null;
    if (ty_name != rec_induct) {
        return null;
    }
    const ind = self.env.getInductive(ty_name) orelse return null;
    const ctor_name = ind.all_ctor_names[0];
    const np = @as(usize, rec.num_params);
    var ctor_self: usize = 0;
    for (rec.rec_rules) |r| {
        if (r.ctor_name == ctor_name) {
            ctor_self = @as(usize, r.ctor_telescope_size_wo_params);
            break;
        }
    }
    const take = @min(np + ctor_self, ty_args.len);
    var new_ctor = value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .ctor = .{ .name = ctor_name, .levels = ty_levels } }, value.spineEmpty());
    {
        var i: usize = 0;
        while (i < take) : (i += 1) {
            new_ctor = apply(self, depth, new_ctor, ty_args[i]);
        }
    }
    const new_ty = valueType(self, depth, new_ctor);
    if (!conv.convTypesAt(self, depth, major_ty_f, new_ty)) {
        return null;
    }
    return new_ctor;
}

const IndApp = struct { NamePtr, LevelsPtr, []const V };

fn unwrapInductiveApp(self: *TypeChecker, depth: u32, v: V) ?IndApp {
    switch (v.*) {
        .rigid => |r| switch (r.head) {
            .inductive => |h| {
                const args = spineApps(self, depth, r.spine) orelse return null;
                return IndApp{ h.name, h.levels, args };
            },
            else => return null,
        },
        else => return null,
    }
}

fn majorToCtor(self: *TypeChecker, depth: u32, major: V) ?V {
    switch (major.*) {
        .nat_lit => |n| return natLitToCtorVal(self, depth, n.ptr),
        .str_lit => |s| return strLitToCtorVal(self, depth, s.ptr),
        else => return null,
    }
}

pub fn strLitToCtorVal(self: *TypeChecker, depth: u32, s: StringPtr) ?V {
    const ctor_expr = expr.strLitToConstructor(self.ctx, s) orelse return null;
    const empty = value.envEmpty();
    const v = eval(self, depth, empty, ctor_expr);
    return whnfHead(self, depth, v);
}

fn natLitToCtorVal(self: *TypeChecker, depth: u32, n: BigUintPtr) ?V {
    if (!self.ctx.export_file.config.nat_extension) {
        return null;
    }
    const nv = nat.clone(n.asRef());
    defer nat.free(nv);
    const levels = TcCtx.allocLevels(self.ctx, &.{});
    const empty = value.spineEmpty();
    if (nv.eqlZero()) {
        const zero_name = self.ctx.export_file.name_cache.nat_zero orelse return null;
        return value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .ctor = .{ .name = zero_name, .levels = levels } }, empty);
    } else {
        const pred = TcCtx.allocBignum(self.ctx, nat.pred(nv)) orelse return null;
        const pred_v = value.mkNatlit(self.arena, pred);
        const succ_name = self.ctx.export_file.name_cache.nat_succ orelse return null;
        const succ_v = value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .ctor = .{ .name = succ_name, .levels = levels } }, empty);
        return apply(self, depth, succ_v, pred_v);
    }
}

const CtorApp = struct { NamePtr, []const V };

fn unwrapCtorApp(self: *TypeChecker, depth: u32, v: V) ?CtorApp {
    switch (v.*) {
        .rigid => |r| switch (r.head) {
            .ctor => |h| {
                const args = spineApps(self, depth, r.spine) orelse return null;
                return CtorApp{ h.name, args };
            },
            else => return null,
        },
        else => return null,
    }
}

fn doQuotIota(self: *TypeChecker, depth: u32, c_name: NamePtr, args: []const V) ?V {
    const cache = self.ctx.export_file.name_cache;
    const qmk_pos: usize = if (eqOpt(cache.quot_lift, c_name))
        5
    else if (eqOpt(cache.quot_ind, c_name))
        4
    else
        return null;
    if (qmk_pos >= args.len) return null;
    const qmk = forceAll(self, depth, args[qmk_pos]);
    return fireQuot(self, depth, c_name, args, qmk);
}

fn fireQuot(self: *TypeChecker, depth: u32, c_name: NamePtr, args: []const V, qmk: V) ?V {
    const cache = self.ctx.export_file.name_cache;
    const rest_idx: usize = if (eqOpt(cache.quot_lift, c_name))
        6
    else if (eqOpt(cache.quot_ind, c_name))
        5
    else
        return null;
    var qmk_head: NamePtr = undefined;
    var qmk_spine: S = undefined;
    switch (qmk.*) {
        .rigid => |r| switch (r.head) {
            .quot_const => |h| {
                qmk_head = h.name;
                qmk_spine = r.spine;
            },
            else => return null,
        },
        else => return null,
    }
    if (!eqOpt(cache.quot_mk, qmk_head)) {
        return null;
    }
    const qmk_args = spineApps(self, depth, qmk_spine) orelse return null;
    defer self.ctx.bump.free(qmk_args);
    if (qmk_args.len != 3) {
        return null;
    }
    if (3 >= args.len) return null;
    const f = args[3];
    const last = qmk_args[2];
    var result = apply(self, depth, f, last);
    for (args[rest_idx..]) |a| {
        result = apply(self, depth, result, a);
    }
    return result;
}

fn doNatRed(self: *TypeChecker, depth: u32, name: NamePtr, args: []const V) ?V {
    return doNatRedAt(self, depth, name, args, true);
}

fn doNatRedShallow(self: *TypeChecker, depth: u32, name: NamePtr, args: []const V) ?V {
    return doNatRedAt(self, depth, name, args, false);
}

fn doNatRedAt(self: *TypeChecker, depth: u32, name: NamePtr, args: []const V, deep: bool) ?V {
    const kind = self.ctx.export_file.name_cache.nat_red.get(name) orelse return null;
    switch (kind) {
        .succ => {
            if (args.len != 1) return null;
            const n = valueToBignumAt(self, depth, args[0], deep) orelse return null;
            defer nat.free(n);
            return mkNatlitVal(self, nat.succ(n));
        },
        .div_go, .mod_core_go => {
            if (args.len != 5) return null;
            const y = valueToBignumAt(self, depth, args[0], deep) orelse return null;
            const x = valueToBignumAt(self, depth, args[3], deep) orelse return null;
            return doNatBinVal(self, x, y, if (kind == .div_go) .div else .mod);
        },
        else => {
            if (args.len != 2) return null;
            const xn = valueToBignumAt(self, depth, args[0], deep) orelse return null;
            const yn = valueToBignumAt(self, depth, args[1], deep) orelse return null;
            return doNatBinVal(self, xn, yn, kind);
        },
    }
}

fn doNatBinVal(self: *TypeChecker, x: BigUint, y: BigUint, op: NatRed) ?V {
    defer {
        nat.free(x);
        nat.free(y);
    }
    switch (op) {
        .succ, .div_go, .mod_core_go => unreachable,
        .add => return mkNatlitVal(self, nat.add(x, y)),
        .sub => return mkNatlitVal(self, nat.sub(x, y)),
        .mul => return mkNatlitVal(self, nat.mul(x, y)),
        .pow => return mkNatlitVal(self, nat.pow(x, y) orelse return null),
        .div => return mkNatlitVal(self, nat.div(x, y)),
        .mod => return mkNatlitVal(self, nat.mod(x, y)),
        .gcd => return mkNatlitVal(self, nat.gcd(x, y)),
        .land => return mkNatlitVal(self, nat.land(x, y)),
        .lor => return mkNatlitVal(self, nat.lor(x, y)),
        .xor => return mkNatlitVal(self, nat.xor(x, y)),
        .shl => return mkNatlitVal(self, nat.shiftLeft(x, y) orelse return null),
        .shr => return mkNatlitVal(self, nat.shiftRight(x, y)),
        .beq => return boolVal(self, nat.beq(x, y)),
        .ble => return boolVal(self, nat.ble(x, y)),
    }
}

fn mkNatlitVal(self: *TypeChecker, n: BigUint) ?V {
    const p = TcCtx.allocBignum(self.ctx, n) orelse return null;
    return value.mkNatlit(self.arena, p);
}

fn boolVal(self: *TypeChecker, b: bool) ?V {
    const cache = self.ctx.export_file.name_cache;
    const n = if (b) (cache.bool_true orelse return null) else (cache.bool_false orelse return null);
    const levels = TcCtx.allocLevels(self.ctx, &.{});
    return value.mkRigidHeadWithEmpty(self.arena, RigidHead{ .ctor = .{ .name = n, .levels = levels } }, value.spineEmpty());
}

pub fn valueHasFreeBvar(self: *TypeChecker, depth: u32, v0: V) bool {
    const v = forceThunk(self, depth, v0);
    const key = @intFromPtr(v);
    if (self.tc_cache.fvar_cache.get(key)) |b| {
        return b;
    }
    const r = switch (v.*) {
        .sort, .nat_lit, .str_lit => false,
        .rigid => |rg| switch (rg.head) {
            .b_var, .local => true,
            else => spineHasFreeBvar(self, depth, rg.spine),
        },
        .unfold => |u| spineHasFreeBvar(self, depth, u.spine),
        .lam, .pi => false,
        .thunk => @panic("force_thunk left a Thunk"),
    };
    self.tc_cache.fvar_cache.put(util.smp_allocator, key, r) catch util.oom();
    return r;
}

fn spineHasFreeBvar(self: *TypeChecker, depth: u32, spine: S) bool {
    var found = false;
    var s = spine;
    while (s != &Spine.empty) {
        if (s.elim.isApp()) {
            if (valueHasFreeBvar(self, depth, s.elim.appV())) {
                found = true;
                break;
            }
        }
        s = s.prev;
    }
    return found;
}

pub fn valueToBignum(self: *TypeChecker, depth: u32, v: V) ?BigUint {
    return valueToBignumAt(self, depth, v, true);
}

fn valueToBignumAt(self: *TypeChecker, depth: u32, v: V, deep: bool) ?BigUint {
    var succs: u64 = 0;
    var cur = forceThunk(self, depth, v);
    while (true) {
        switch (cur.*) {
            .nat_lit => |n| {
                const bn = n.ptr.asRef();
                if (succs == 0) return nat.clone(bn);
                const c = nat.clone(bn);
                defer nat.free(c);
                return nat.addUsize(c, succs);
            },
            .rigid => |r| switch (r.head) {
                .ctor => |ct| {
                    if (eqOpt(self.ctx.export_file.name_cache.nat_zero, ct.name) and r.spine.isEmpty()) {
                        return nat.fromUsize(succs);
                    }
                    if (eqOpt(self.ctx.export_file.name_cache.nat_succ, ct.name)) {
                        if (r.spine != &Spine.empty and r.spine.prev == &Spine.empty and r.spine.elim.isApp()) {
                            succs += 1;
                            cur = forceThunk(self, depth, r.spine.elim.appV());
                            continue;
                        }
                    }
                    return null;
                },
                .recursor, .quot_const => {
                    if (!deep) {
                        return null;
                    }
                    const bn = bignumViaForce(self, depth, cur) orelse return null;
                    if (succs == 0) return bn;
                    defer nat.free(bn);
                    return nat.addUsize(bn, succs);
                },
                else => return null,
            },
            .unfold => |u| {
                if (u.head_value.get()) |hv| {
                    if (hv.* == .nat_lit) {
                        const bn = hv.nat_lit.ptr.asRef();
                        if (succs == 0) return nat.clone(bn);
                        const c = nat.clone(bn);
                        defer nat.free(c);
                        return nat.addUsize(c, succs);
                    }
                }
                if (!deep) {
                    return null;
                }
                const bn = bignumViaForce(self, depth, cur) orelse return null;
                if (succs == 0) return bn;
                defer nat.free(bn);
                return nat.addUsize(bn, succs);
            },
            else => return null,
        }
    }
}

fn bignumViaForce(self: *TypeChecker, depth: u32, v: V) ?BigUint {
    if (valueHasFreeBvar(self, depth, v)) {
        return null;
    }
    const f = forceAll(self, depth, v);
    switch (f.*) {
        .nat_lit => |n| {
            return nat.clone(n.ptr.asRef());
        },
        .rigid => |r| switch (r.head) {
            .ctor => |ct| {
                if (eqOpt(self.ctx.export_file.name_cache.nat_zero, ct.name) or
                    eqOpt(self.ctx.export_file.name_cache.nat_succ, ct.name))
                {
                    if (f == v) {
                        return null;
                    }
                    return valueToBignum(self, depth, f);
                }
                return null;
            },
            else => return null,
        },
        else => return null,
    }
}

inline fn eqOpt(opt: ?NamePtr, name: NamePtr) bool {
    return if (opt) |o| o == name else false;
}
