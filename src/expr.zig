const std = @import("std");
const util = @import("util.zig");
const level = @import("level.zig");
const name = @import("name.zig");
const env = @import("env.zig");
const value = @import("value.zig");
const nat = @import("nat.zig");
const TcCtx = @import("TcCtx.zig");
const swiss_map = @import("swiss_map.zig");
const ptr = @import("ptr.zig");

const expr = @This();
const ExprPtr = ptr.ExprPtr;
const LevelPtr = ptr.LevelPtr;
const LevelsPtr = ptr.LevelsPtr;
const NamePtr = ptr.NamePtr;
const StringPtr = ptr.StringPtr;
const BigUintPtr = ptr.BigUintPtr;
const FxHashMap = swiss_map.FxHashMap;

const kindHash = @import("hash.zig").kindHash;

pub const FVarId = union(enum) {
    dbj_level: u16,
    unique: u32,

    pub fn getHash(self: FVarId) u64 {
        return switch (self) {
            .dbj_level => |v| v,
            .unique => |v| (@as(u64, 1) << 32) | v,
        };
    }
};

pub const BinderStyle = enum {
    default,
    implicit,
    strict_implicit,
    instance_implicit,
};

pub const LetData = struct {
    binder_name: NamePtr,
    binder_type: ExprPtr,
    val: ExprPtr,
    body: ExprPtr,
    nondep: bool,
};

pub const Expr = struct {
    hash: u64,
    fv_mask: u64,
    kind: Kind,

    pub const Kind = union(enum) {
        string_lit: struct {
            ptr: StringPtr,
        },
        nat_lit: struct {
            ptr: BigUintPtr,
        },
        proj: struct {
            ty_name: NamePtr,
            idx: usize,
            structure: ExprPtr,
        },
        @"var": struct {
            dbj_idx: u16,
        },
        sort: struct {
            level: LevelPtr,
        },
        @"const": struct {
            name: NamePtr,
            levels: LevelsPtr,
        },
        app: struct {
            fun: ExprPtr,
            arg: ExprPtr,
        },
        pi: struct {
            binder_name: NamePtr,
            binder_style: BinderStyle,
            binder_type: ExprPtr,
            body: ExprPtr,
        },
        lambda: struct {
            binder_name: NamePtr,
            binder_style: BinderStyle,
            binder_type: ExprPtr,
            body: ExprPtr,
        },
        let: struct {
            data: *const LetData,
        },
        local: struct {
            binder_name: NamePtr,
            binder_style: BinderStyle,
            binder_type: ExprPtr,
            id: FVarId,
        },
    };

    pub inline fn mk(kind: Kind) Expr {
        return .{ .hash = kindHash(kind), .fv_mask = maskOf(kind), .kind = kind };
    }

    pub fn getHash(self: *const Expr) u64 {
        return self.hash;
    }
};

pub fn instForallParams(self: *TcCtx, e_in: ExprPtr, n: usize, all_args: []const ExprPtr) ExprPtr {
    var e = e_in;
    var i: usize = 0;
    while (i < n) : (i += 1) {
        switch (e.asRef().kind) {
            .pi => |x| e = x.body,
            else => @panic("inst_forall_params"),
        }
    }
    return inst(self, e, all_args[0..n]);
}

pub fn inst(self: *TcCtx, e: ExprPtr, substs: []const ExprPtr) ExprPtr {
    self.expr_cache.inst_cache.clearRetainingCapacity();
    return instAux(self, e, substs, 0);
}

fn instAux(self: *TcCtx, e: ExprPtr, substs: []const ExprPtr, offset: u16) ExprPtr {
    if (e.numLooseBvars() <= offset) {
        return e;
    } else if (self.expr_cache.inst_cache.get(.{ e, offset })) |cached| {
        return cached;
    } else {
        const calcd = switch (e.asRef().kind) {
            .sort, .@"const", .local, .string_lit, .nat_lit => @panic("inst_aux unreachable"),
            .@"var" => |x| blk: {
                std.debug.assert(x.dbj_idx >= offset);
                const idx: usize = @as(usize, x.dbj_idx - offset);
                if (idx < substs.len) {
                    break :blk substs[substs.len - 1 - idx];
                } else {
                    break :blk e;
                }
            },
            .app => |x| blk: {
                const fun = instAux(self, x.fun, substs, offset);
                const arg = instAux(self, x.arg, substs, offset);
                break :blk TcCtx.mkApp(self, fun, arg);
            },
            .pi => |x| blk: {
                const binder_type = instAux(self, x.binder_type, substs, offset);
                const body = instAux(self, x.body, substs, offset + 1);
                break :blk TcCtx.mkPi(self, x.binder_name, x.binder_style, binder_type, body);
            },
            .lambda => |x| blk: {
                const binder_type = instAux(self, x.binder_type, substs, offset);
                const body = instAux(self, x.body, substs, offset + 1);
                break :blk TcCtx.mkLambda(self, x.binder_name, x.binder_style, binder_type, body);
            },
            .let => |x| blk: {
                const binder_type = instAux(self, x.data.binder_type, substs, offset);
                const val = instAux(self, x.data.val, substs, offset);
                const body = instAux(self, x.data.body, substs, offset + 1);
                break :blk TcCtx.mkLet(self, x.data.binder_name, binder_type, val, body, x.data.nondep);
            },
            .proj => |x| blk: {
                const structure = instAux(self, x.structure, substs, offset);
                break :blk TcCtx.mkProj(self, x.ty_name, x.idx, structure);
            },
        };
        self.expr_cache.inst_cache.put(util.smp_allocator, .{ e, offset }, calcd) catch util.oom();
        return calcd;
    }
}

pub fn replaceParams(self: *TcCtx, e_in: ExprPtr, ingoing: []const ExprPtr, outgoing: []const ExprPtr) ExprPtr {
    const e = abstr(self, e_in, outgoing);
    return inst(self, e, ingoing);
}

fn abstrAuxLevels(self: *TcCtx, e: ExprPtr, start_pos: u16, num_open_binders: u16) ExprPtr {
    if (!e.hasFvars()) {
        return e;
    } else if (self.expr_cache.abstr_cache_levels.get(.{ e, start_pos, num_open_binders })) |cached| {
        return cached;
    } else {
        const calcd = switch (e.asRef().kind) {
            .local => |x| switch (x.id) {
                .dbj_level => |serial| if (serial < start_pos)
                    e
                else
                    TcCtx.fvarToBvar(self, num_open_binders, serial),
                .unique => e,
            },
            .app => |x| blk: {
                const fun = abstrAuxLevels(self, x.fun, start_pos, num_open_binders);
                const arg = abstrAuxLevels(self, x.arg, start_pos, num_open_binders);
                break :blk TcCtx.mkApp(self, fun, arg);
            },
            .pi => |x| blk: {
                const binder_type = abstrAuxLevels(self, x.binder_type, start_pos, num_open_binders);
                const body = abstrAuxLevels(self, x.body, start_pos, num_open_binders + 1);
                break :blk TcCtx.mkPi(self, x.binder_name, x.binder_style, binder_type, body);
            },
            .lambda => |x| blk: {
                const binder_type = abstrAuxLevels(self, x.binder_type, start_pos, num_open_binders);
                const body = abstrAuxLevels(self, x.body, start_pos, num_open_binders + 1);
                break :blk TcCtx.mkLambda(self, x.binder_name, x.binder_style, binder_type, body);
            },
            .let => |x| blk: {
                const binder_type = abstrAuxLevels(self, x.data.binder_type, start_pos, num_open_binders);
                const val = abstrAuxLevels(self, x.data.val, start_pos, num_open_binders);
                const body = abstrAuxLevels(self, x.data.body, start_pos, num_open_binders + 1);
                break :blk TcCtx.mkLet(self, x.data.binder_name, binder_type, val, body, x.data.nondep);
            },
            .string_lit, .nat_lit => @panic("abstr_aux_levels"),
            .proj => |x| blk: {
                const structure = abstrAuxLevels(self, x.structure, start_pos, num_open_binders);
                break :blk TcCtx.mkProj(self, x.ty_name, x.idx, structure);
            },
            .@"var", .sort, .@"const" => @panic("should flag as no locals"),
        };
        self.expr_cache.abstr_cache_levels.put(util.smp_allocator, .{ e, start_pos, num_open_binders }, calcd) catch util.oom();
        return calcd;
    }
}

pub fn abstrLevels(self: *TcCtx, e: ExprPtr, start_pos: u16) ExprPtr {
    self.expr_cache.abstr_cache_levels.clearRetainingCapacity();
    return abstrAuxLevels(self, e, start_pos, self.dbj_level_counter);
}

fn abstrAux(self: *TcCtx, e: ExprPtr, locals: []const ExprPtr, offset: u16) ExprPtr {
    if (!e.hasFvars()) {
        return e;
    } else if (self.expr_cache.abstr_cache.get(.{ e, offset })) |cached| {
        return cached;
    } else {
        const calcd = switch (e.asRef().kind) {
            .local => blk: {
                var pos: usize = 0;
                while (pos < locals.len) : (pos += 1) {
                    if (locals[locals.len - 1 - pos] == e) {
                        break :blk TcCtx.mkVar(self, std.math.cast(u16, pos).? + offset);
                    }
                }
                break :blk e;
            },
            .app => |x| blk: {
                const fun = abstrAux(self, x.fun, locals, offset);
                const arg = abstrAux(self, x.arg, locals, offset);
                break :blk TcCtx.mkApp(self, fun, arg);
            },
            .pi => |x| blk: {
                const binder_type = abstrAux(self, x.binder_type, locals, offset);
                const body = abstrAux(self, x.body, locals, offset + 1);
                break :blk TcCtx.mkPi(self, x.binder_name, x.binder_style, binder_type, body);
            },
            .lambda => |x| blk: {
                const binder_type = abstrAux(self, x.binder_type, locals, offset);
                const body = abstrAux(self, x.body, locals, offset + 1);
                break :blk TcCtx.mkLambda(self, x.binder_name, x.binder_style, binder_type, body);
            },
            .let => |x| blk: {
                const binder_type = abstrAux(self, x.data.binder_type, locals, offset);
                const val = abstrAux(self, x.data.val, locals, offset);
                const body = abstrAux(self, x.data.body, locals, offset + 1);
                break :blk TcCtx.mkLet(self, x.data.binder_name, binder_type, val, body, x.data.nondep);
            },
            .string_lit, .nat_lit => @panic("abstr_aux"),
            .proj => |x| blk: {
                const structure = abstrAux(self, x.structure, locals, offset);
                break :blk TcCtx.mkProj(self, x.ty_name, x.idx, structure);
            },
            .@"var", .sort, .@"const" => @panic("should flag as no locals"),
        };
        self.expr_cache.abstr_cache.put(util.smp_allocator, .{ e, offset }, calcd) catch util.oom();
        return calcd;
    }
}

pub fn abstr(self: *TcCtx, e: ExprPtr, locals: []const ExprPtr) ExprPtr {
    self.expr_cache.abstr_cache.clearRetainingCapacity();
    return abstrAux(self, e, locals, 0);
}

fn substAux(self: *TcCtx, e: ExprPtr, ks: LevelsPtr, vs: LevelsPtr) ExprPtr {
    if (self.expr_cache.subst_cache.get(.{ e, ks, vs })) |cached| {
        return cached;
    } else {
        const r = switch (e.asRef().kind) {
            .@"var", .nat_lit, .string_lit => e,
            .sort => |x| blk: {
                const lvl = level.substLevel(self, x.level, ks, vs);
                break :blk TcCtx.mkSort(self, lvl);
            },
            .@"const" => |x| blk: {
                const levels = level.substLevels(self, x.levels, ks, vs);
                break :blk TcCtx.mkConst(self, x.name, levels);
            },
            .app => |x| blk: {
                const fun = substAux(self, x.fun, ks, vs);
                const arg = substAux(self, x.arg, ks, vs);
                break :blk TcCtx.mkApp(self, fun, arg);
            },
            .pi => |x| blk: {
                const binder_type = substAux(self, x.binder_type, ks, vs);
                const body = substAux(self, x.body, ks, vs);
                break :blk TcCtx.mkPi(self, x.binder_name, x.binder_style, binder_type, body);
            },
            .lambda => |x| blk: {
                const binder_type = substAux(self, x.binder_type, ks, vs);
                const body = substAux(self, x.body, ks, vs);
                break :blk TcCtx.mkLambda(self, x.binder_name, x.binder_style, binder_type, body);
            },
            .let => |x| blk: {
                const binder_type = substAux(self, x.data.binder_type, ks, vs);
                const val = substAux(self, x.data.val, ks, vs);
                const body = substAux(self, x.data.body, ks, vs);
                break :blk TcCtx.mkLet(self, x.data.binder_name, binder_type, val, body, x.data.nondep);
            },
            .local => @panic("level substitution should not find locals"),
            .proj => |x| blk: {
                const structure = substAux(self, x.structure, ks, vs);
                break :blk TcCtx.mkProj(self, x.ty_name, x.idx, structure);
            },
        };
        self.expr_cache.subst_cache.put(util.smp_allocator, .{ e, ks, vs }, r) catch util.oom();
        return r;
    }
}

pub fn substExprLevels(self: *TcCtx, e: ExprPtr, ks: LevelsPtr, vs: LevelsPtr) ExprPtr {
    if (ks.eql(vs) or ks.asRef().len == 0) {
        util.assert(ks.asRef().len == vs.asRef().len);
        return e;
    }
    if (self.expr_cache.dsubst_cache.get(.{ e, ks, vs })) |cached| {
        return cached;
    }
    self.expr_cache.subst_cache.clearRetainingCapacity();
    util.assert(ks.asRef().len == vs.asRef().len);
    const out = substAux(self, e, ks, vs);
    self.expr_cache.dsubst_cache.put(util.smp_allocator, .{ e, ks, vs }, out) catch util.oom();
    return out;
}

pub fn substDeclarInfoLevels(self: *TcCtx, info: env.DeclarInfo, in_vals: LevelsPtr) ExprPtr {
    return substExprLevels(self, info.ty, info.uparams, in_vals);
}

pub fn numArgs(e: ExprPtr) usize {
    var cursor = e;
    var n: usize = 0;
    while (true) {
        switch (cursor.asRef().kind) {
            .app => |x| {
                cursor = x.fun;
                n += 1;
            },
            else => break,
        }
    }
    return n;
}

pub fn unfoldAppsFun(e_in: ExprPtr) ExprPtr {
    var e = e_in;
    while (true) {
        switch (e.asRef().kind) {
            .app => |x| e = x.fun,
            else => break,
        }
    }
    return e;
}

pub fn unfoldApps(a: std.mem.Allocator, e_in: ExprPtr) struct { fun: ExprPtr, args: std.ArrayList(ExprPtr) } {
    var e = e_in;
    var args: std.ArrayList(ExprPtr) = .empty;
    while (true) {
        switch (e.asRef().kind) {
            .app => |x| {
                e = x.fun;
                args.append(a, x.arg) catch util.oom();
            },
            else => break,
        }
    }
    std.mem.reverse(ExprPtr, args.items);
    return .{ .fun = e, .args = args };
}

pub fn unfoldConstApps(a: std.mem.Allocator, e: ExprPtr) ?struct { fun: ExprPtr, name: NamePtr, levels: LevelsPtr, args: std.ArrayList(ExprPtr) } {
    const r = unfoldApps(a, e);
    switch (r.fun.asRef().kind) {
        .@"const" => |x| return .{ .fun = r.fun, .name = x.name, .levels = x.levels, .args = r.args },
        else => return null,
    }
}

pub fn tryConstInfo(e: ExprPtr) ?struct { NamePtr, LevelsPtr } {
    switch (e.asRef().kind) {
        .@"const" => |x| return .{ x.name, x.levels },
        else => return null,
    }
}

pub fn unfoldAppsStack(a: std.mem.Allocator, e_in: ExprPtr) struct { fun: ExprPtr, args: std.ArrayList(ExprPtr) } {
    var e = e_in;
    var args: std.ArrayList(ExprPtr) = .empty;
    while (true) {
        switch (e.asRef().kind) {
            .app => |x| {
                args.append(a, x.arg) catch util.oom();
                e = x.fun;
            },
            else => break,
        }
    }
    return .{ .fun = e, .args = args };
}

pub fn foldlApps(self: *TcCtx, fun_in: ExprPtr, args: []const ExprPtr) ExprPtr {
    var fun = fun_in;
    for (args) |arg| {
        fun = TcCtx.mkApp(self, fun, arg);
    }
    return fun;
}

pub fn abstrPis(self: *TcCtx, binders: []const ExprPtr, body_in: ExprPtr) ExprPtr {
    var body = body_in;
    var i: usize = binders.len;
    while (i > 0) {
        i -= 1;
        body = abstrPi(self, binders[i], body);
    }
    return body;
}

pub fn abstrPi(self: *TcCtx, binder: ExprPtr, body_in: ExprPtr) ExprPtr {
    switch (binder.asRef().kind) {
        .local => |x| {
            const body = abstr(self, body_in, &[_]ExprPtr{binder});
            return TcCtx.mkPi(self, x.binder_name, x.binder_style, x.binder_type, body);
        },
        else => @panic("Cannot apply pi with non-local domain type"),
    }
}

pub fn applyLambda(self: *TcCtx, binder: ExprPtr, body_in: ExprPtr) ExprPtr {
    switch (binder.asRef().kind) {
        .local => |x| {
            const body = abstr(self, body_in, &[_]ExprPtr{binder});
            return TcCtx.mkLambda(self, x.binder_name, x.binder_style, x.binder_type, body);
        },
        else => @panic("Cannot apply lambda with non-local domain type"),
    }
}

pub fn natLitToConstructor(self: *TcCtx, n_ptr: BigUintPtr) ?ExprPtr {
    util.assert(self.export_file.config.nat_extension);
    const n = n_ptr.asRef();
    if (n.eqlZero()) {
        return expr.cNatZero(self);
    } else {
        const pred_num = nat.pred(n.*);
        const pred_ptr = TcCtx.allocBignum(self, pred_num).?;
        const pred = TcCtx.mkNatLit(self, pred_ptr).?;
        const succ_c = expr.cNatSucc(self) orelse return null;
        return TcCtx.mkApp(self, succ_c, pred);
    }
}

pub fn strLitToConstructor(self: *TcCtx, s: StringPtr) ?ExprPtr {
    if ((!self.export_file.config.string_extension) or (!self.export_file.config.nat_extension)) {
        return null;
    }
    const zero = TcCtx.zero(self);
    const empty_levels = TcCtx.allocLevels(self, &[_]LevelPtr{});
    const tyzero_levels = TcCtx.allocLevels(self, &[_]LevelPtr{zero});
    const c_char_ = TcCtx.mkConst(self, self.export_file.name_cache.char orelse return null, empty_levels);
    const c_char_of_nat = TcCtx.mkConst(self, self.export_file.name_cache.char_of_nat orelse return null, empty_levels);
    const c_list_nil_char = blk: {
        const f = TcCtx.mkConst(self, self.export_file.name_cache.list_nil orelse return null, tyzero_levels);
        break :blk TcCtx.mkApp(self, f, c_char_);
    };
    const c_list_cons_char = blk: {
        const f = TcCtx.mkConst(self, self.export_file.name_cache.list_cons orelse return null, tyzero_levels);
        break :blk TcCtx.mkApp(self, f, c_char_);
    };
    var out = c_list_nil_char;
    const str = s.asRef().*;
    var iter = std.unicode.Utf8View.initUnchecked(str).iterator();
    var codepoints: std.ArrayList(u21) = .empty;
    defer codepoints.deinit(self.bump);
    while (iter.nextCodepoint()) |c| {
        codepoints.append(self.bump, c) catch util.oom();
    }
    var i: usize = codepoints.items.len;
    while (i > 0) {
        i -= 1;
        const c = codepoints.items[i];
        const bignum_ptr = TcCtx.allocBignum(self, nat.fromU32(@as(u32, c))).?;
        const bignum = TcCtx.mkNatLit(self, bignum_ptr).?;
        const x = TcCtx.mkApp(self, c_char_of_nat, bignum);
        const y = TcCtx.mkApp(self, c_list_cons_char, x);
        out = TcCtx.mkApp(self, y, out);
    }
    const string_of_list_const = TcCtx.mkConst(self, self.export_file.name_cache.string_of_list orelse return null, empty_levels);
    return TcCtx.mkApp(self, string_of_list_const, out);
}

pub fn getBignumFromExpr(self: *TcCtx, e: ExprPtr) ?nat.BigUint {
    switch (e.asRef().kind) {
        .nat_lit => |x| {
            return nat.clone(x.ptr.asRef());
        },
        else => {
            if (eqOpt(expr.cNatZero(self), e)) {
                return nat.zero();
            } else {
                return null;
            }
        },
    }
}

pub fn getBignumSuccFromExpr(self: *TcCtx, e: ExprPtr) ?ExprPtr {
    switch (e.asRef().kind) {
        .nat_lit => |x| {
            return TcCtx.mkNatLitQuick(self, nat.succ(x.ptr.asRef().*));
        },
        else => {
            if (eqOpt(expr.cNatZero(self), e)) {
                return TcCtx.mkNatLitQuick(self, nat.fromUsize(1));
            } else {
                return null;
            }
        },
    }
}

fn eqOpt(a: ?ExprPtr, b: ExprPtr) bool {
    return if (a) |aa| aa == b else false;
}

pub fn boolToExpr(self: *TcCtx, b: bool) ?ExprPtr {
    if (b) {
        return expr.cBoolTrue(self);
    } else {
        return expr.cBoolFalse(self);
    }
}

pub fn cBoolTrue(self: *TcCtx) ?ExprPtr {
    const n = self.export_file.name_cache.bool_true orelse return null;
    const levels = TcCtx.allocLevels(self, &[_]LevelPtr{});
    return TcCtx.mkConst(self, n, levels);
}

pub fn cBoolFalse(self: *TcCtx) ?ExprPtr {
    const n = self.export_file.name_cache.bool_false orelse return null;
    const levels = TcCtx.allocLevels(self, &[_]LevelPtr{});
    return TcCtx.mkConst(self, n, levels);
}

pub fn cNatZero(self: *TcCtx) ?ExprPtr {
    const n = self.export_file.name_cache.nat_zero orelse return null;
    const levels = TcCtx.allocLevels(self, &[_]LevelPtr{});
    return TcCtx.mkConst(self, n, levels);
}

pub fn cNatSucc(self: *TcCtx) ?ExprPtr {
    const n = self.export_file.name_cache.nat_succ orelse return null;
    const levels = TcCtx.allocLevels(self, &[_]LevelPtr{});
    return TcCtx.mkConst(self, n, levels);
}

pub fn natType(self: *TcCtx) ?ExprPtr {
    const n = self.export_file.name_cache.nat orelse return null;
    const levels = TcCtx.allocLevels(self, &[_]LevelPtr{});
    return TcCtx.mkConst(self, n, levels);
}

pub fn stringType(self: *TcCtx) ?ExprPtr {
    const n = self.export_file.name_cache.string orelse return null;
    const levels = TcCtx.allocLevels(self, &[_]LevelPtr{});
    return TcCtx.mkConst(self, n, levels);
}

pub fn abstrLambdaTelescope(self: *TcCtx, binders_in: []const ExprPtr, e_in: ExprPtr) ExprPtr {
    var binders = binders_in;
    var e = e_in;
    while (binders.len > 0) {
        const binder = binders[binders.len - 1];
        e = applyLambda(self, binder, e);
        binders = binders[0 .. binders.len - 1];
    }
    return e;
}

pub fn abstrPiTelescope(self: *TcCtx, binders_in: []const ExprPtr, e_in: ExprPtr) ExprPtr {
    var binders = binders_in;
    var e = e_in;
    while (binders.len > 0) {
        const binder = binders[binders.len - 1];
        e = abstrPi(self, binder, e);
        binders = binders[0 .. binders.len - 1];
    }
    return e;
}

pub fn findConst(self: *const TcCtx, e: ExprPtr, cl: anytype, pred: anytype) bool {
    var cache = FxHashMap(ExprPtr, bool).empty;
    defer cache.deinit(util.smp_allocator);
    return findConstAux(self, e, cl, pred, &cache);
}

fn findConstAux(self: *const TcCtx, e: ExprPtr, cl: anytype, pred: anytype, cache: *FxHashMap(ExprPtr, bool)) bool {
    if (cache.get(e)) |cached| {
        return cached;
    } else {
        const r = switch (e.asRef().kind) {
            .@"var", .sort, .nat_lit, .string_lit => false,
            .@"const" => |x| pred(cl, x.name),
            .app => |x| findConstAux(self, x.fun, cl, pred, cache) or findConstAux(self, x.arg, cl, pred, cache),
            .pi => |x| findConstAux(self, x.binder_type, cl, pred, cache) or findConstAux(self, x.body, cl, pred, cache),
            .lambda => |x| findConstAux(self, x.binder_type, cl, pred, cache) or findConstAux(self, x.body, cl, pred, cache),
            .let => |x| findConstAux(self, x.data.binder_type, cl, pred, cache) or findConstAux(self, x.data.val, cl, pred, cache) or findConstAux(self, x.data.body, cl, pred, cache),
            .local => |x| findConstAux(self, x.binder_type, cl, pred, cache),
            .proj => |x| findConstAux(self, x.structure, cl, pred, cache),
        };
        cache.put(util.smp_allocator, e, r) catch util.oom();
        return r;
    }
}

pub fn piTelescopeSize(e_in: ExprPtr) u16 {
    var e = e_in;
    var size: u16 = 0;
    while (true) {
        switch (e.asRef().kind) {
            .pi => |x| {
                size += 1;
                e = x.body;
            },
            else => break,
        }
    }
    return size;
}

pub fn prop(self: *TcCtx) ExprPtr {
    return TcCtx.mkSort(self, TcCtx.zero(self));
}

pub fn getNthPiBinder(e_in: ExprPtr, n: usize) ?ExprPtr {
    var e = e_in;
    var i: usize = 0;
    while (i < n) : (i += 1) {
        switch (e.asRef().kind) {
            .pi => |x| e = x.body,
            else => return null,
        }
    }
    switch (e.asRef().kind) {
        .pi => |x| return x.binder_type,
        else => return null,
    }
}

pub fn getMajorInduct(rec: *const env.RecursorData) ?NamePtr {
    if (getNthPiBinder(rec.info.ty, rec.majorIdx())) |x| {
        switch (unfoldAppsFun(x).asRef().kind) {
            .@"const" => |c| return c.name,
            else => return null,
        }
    } else {
        return null;
    }
}

fn childMask(e: ExprPtr) u64 {
    const k = e.numLooseBvars();
    if (k == 0) return 0;
    if (k <= 64) return e.asRef().fv_mask;
    return 0;
}

fn bodyMask(body: ExprPtr) u64 {
    const k = body.numLooseBvars();
    if (k == 0) return 0;
    if (k <= 64) return body.asRef().fv_mask >> 1;
    return std.math.maxInt(u64);
}

fn maskOf(kind: Expr.Kind) u64 {
    return switch (kind) {
        .@"var" => |x| if (x.dbj_idx < 64) @as(u64, 1) << @intCast(x.dbj_idx) else 0,
        .app => |x| childMask(x.fun) | childMask(x.arg),
        .pi => |x| childMask(x.binder_type) | bodyMask(x.body),
        .lambda => |x| childMask(x.binder_type) | bodyMask(x.body),
        .let => |x| childMask(x.data.binder_type) | childMask(x.data.val) | bodyMask(x.data.body),
        .proj => |x| childMask(x.structure),
        .sort, .@"const", .local, .string_lit, .nat_lit => 0,
    };
}

pub fn hasLooseBvar(e: ExprPtr, idx: u16) bool {
    if (e.numLooseBvars() <= idx) {
        return false;
    }
    return switch (e.asRef().kind) {
        .@"var" => |x| x.dbj_idx == idx,
        .app => |x| hasLooseBvar(x.fun, idx) or hasLooseBvar(x.arg, idx),
        .pi => |x| hasLooseBvar(x.binder_type, idx) or hasLooseBvar(x.body, idx + 1),
        .lambda => |x| hasLooseBvar(x.binder_type, idx) or hasLooseBvar(x.body, idx + 1),
        .let => |x| hasLooseBvar(x.data.binder_type, idx) or hasLooseBvar(x.data.val, idx) or hasLooseBvar(x.data.body, idx + 1),
        .proj => |x| hasLooseBvar(x.structure, idx),
        .sort, .@"const", .local, .string_lit, .nat_lit => false,
    };
}
