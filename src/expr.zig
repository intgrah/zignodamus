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
    };

    pub inline fn mk(kind: Kind) Expr {
        return .{ .hash = kindHash(kind), .fv_mask = maskOf(kind), .kind = kind };
    }

    pub fn getHash(self: *const Expr) u64 {
        return self.hash;
    }
};

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
        .sort, .@"const", .string_lit, .nat_lit => 0,
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
        .sort, .@"const", .string_lit, .nat_lit => false,
    };
}
