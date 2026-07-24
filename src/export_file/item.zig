const std = @import("std");
const util = @import("../util.zig");
const name = @import("../name.zig");
const level = @import("../level.zig");
const expr = @import("../expr.zig");
const nat = @import("../nat.zig");
const parser = @import("parser.zig");
const ptr = @import("../ptr.zig");

const NamePtr = ptr.NamePtr;
const LevelPtr = ptr.LevelPtr;
const LevelsPtr = ptr.LevelsPtr;
const ExprPtr = ptr.ExprPtr;
const StringPtr = ptr.StringPtr;
const BigUintPtr = ptr.BigUintPtr;

const Name = name.Name;
const Level = level.Level;
const Expr = expr.Expr;
const BinderStyle = expr.BinderStyle;

const Parser = parser.Parser;
const BackRef = parser.BackRef;
const ParseError = parser.ParseError;
const fail = parser.fail;

fn resizeOpt(comptime T: type, list: *std.ArrayList(T), new_len: usize, nil: T) void {
    const old_len = list.items.len;
    list.resize(util.smp_allocator, new_len) catch util.oom();
    @memset(list.items[old_len..], nil);
}

fn pushName(self: *Parser, expected: BackRef, n: Name) void {
    const i = @as(usize, expected.index());
    if (i >= self.names_by_idx.items.len) {
        resizeOpt(NamePtr, &self.names_by_idx, i + 1, NamePtr.nil);
    }
    self.names_by_idx.items[i] = NamePtr.global(self.dag.names.insertUnique(self.arena, n));
}

fn pushLevel(self: *Parser, expected: BackRef, l: Level) void {
    const i = @as(usize, expected.index());
    if (i >= self.levels_by_idx.items.len) {
        resizeOpt(LevelPtr, &self.levels_by_idx, i + 1, LevelPtr.nil);
    }
    self.levels_by_idx.items[i] = LevelPtr.global(self.dag.levels.insertUnique(self.arena, l));
}

fn pushExpr(self: *Parser, expected: BackRef, e: Expr) void {
    const r = self.arena.create(Expr);
    r.* = e;
    self.pending_exprs.append(util.smp_allocator, .{ .hash = e.hash, .ref = r }) catch util.oom();
    const i = @as(usize, expected.index());
    if (i >= self.exprs_by_idx.items.len) {
        resizeOpt(ExprPtr, &self.exprs_by_idx, i + 1, ExprPtr.nil);
    }
    self.exprs_by_idx.items[i] = ExprPtr.global(r);
}

pub fn getNamePtr(self: *const Parser, idx: u32) ParseError!NamePtr {
    if (idx < self.names_by_idx.items.len) {
        const p = self.names_by_idx.items[idx];
        if (p != NamePtr.nil) return p;
    }
    return fail("export references name index before it is defined");
}

pub fn getLevelPtr(self: *const Parser, idx: u32) ParseError!LevelPtr {
    if (idx < self.levels_by_idx.items.len) {
        const p = self.levels_by_idx.items[idx];
        if (p != LevelPtr.nil) return p;
    }
    return fail("export references level index before it is defined");
}

pub fn getExprPtr(self: *const Parser, idx: u32) ParseError!ExprPtr {
    if (idx < self.exprs_by_idx.items.len) {
        const p = self.exprs_by_idx.items[idx];
        if (p != ExprPtr.nil) return p;
    }
    return fail("export references expression index before it is defined");
}

pub fn getNames(self: *const Parser, ta: std.mem.Allocator, idxs: []const u32) ParseError![]const NamePtr {
    var out = ta.alloc(NamePtr, idxs.len) catch util.oom();
    for (idxs, 0..) |idx, i| {
        out[i] = try getNamePtr(self, idx);
    }
    return out;
}

pub fn getUparamsPtr(self: *Parser, ta: std.mem.Allocator, name_idxs: []const u32) ParseError!LevelsPtr {
    var levels = ta.alloc(LevelPtr, name_idxs.len) catch util.oom();
    for (name_idxs, 0..) |name_idx, i| {
        const name_ptr = try getNamePtr(self, name_idx);
        const probe: Level = .mk(.{ .param = name_ptr });
        const r = self.dag.levels.get(&probe) orelse return fail("levelParams entry is not a declared universe parameter");
        levels[i] = LevelPtr.global(r);
    }
    return LevelsPtr.global(self.dag.uparams.intern(self.arena, levels));
}

fn getLevelsPtr(self: *Parser, ta: std.mem.Allocator, idxs: []const u32) ParseError!LevelsPtr {
    var levels = ta.alloc(LevelPtr, idxs.len) catch util.oom();
    for (idxs, 0..) |idx, i| {
        levels[i] = try getLevelPtr(self, idx);
    }
    return LevelsPtr.global(self.dag.uparams.intern(self.arena, levels));
}

pub fn binderStyleOf(s: []const u8) ?BinderStyle {
    switch (s.len) {
        7 => if (std.mem.eql(u8, s, "default")) return .default,
        8 => if (std.mem.eql(u8, s, "implicit")) return .implicit,
        14 => if (std.mem.eql(u8, s, "strictImplicit")) return .strict_implicit,
        12 => if (std.mem.eql(u8, s, "instImplicit")) return .instance_implicit,
        else => {},
    }
    return null;
}

pub fn doStr(self: *Parser, idx: BackRef, pre: u32, s: []const u8) ParseError!void {
    const pfx = try getNamePtr(self, pre);
    const owned = self.arena.dupe(u8, s);
    const sfx = StringPtr.global(self.dag.strings.intern(self.arena, owned));
    pushName(self, idx, .mk(.{ .str = .{ .pfx = pfx, .sfx = sfx } }));
}

pub fn doNum(self: *Parser, idx: BackRef, pre: u32, i: u32) ParseError!void {
    const pfx = try getNamePtr(self, pre);
    const sfx = @as(u64, i);
    pushName(self, idx, .mk(.{ .num = .{ .pfx = pfx, .n = sfx } }));
}

pub fn doNatVal(self: *Parser, idx: BackRef, s: []const u8) ParseError!void {
    if (!self.config.nat_extension) {
        return fail("Nat lit extension disallowed by checker execution config, but export file contains a nat literal");
    }
    const big = nat.fromDecimal(s) orelse return fail("invalid BigUint decimal string");
    const num_ptr = BigUintPtr.global(self.dag.bignums.?.intern(self.arena, big));
    pushExpr(self, idx, .mk(.{ .nat_lit = .{ .ptr = num_ptr } }));
}

pub fn doStrVal(self: *Parser, idx: BackRef, s: []const u8) ParseError!void {
    if (!self.config.string_extension) {
        return fail("String lit extension disallowed by checker execution config, but export file contains a string literal");
    }
    const owned = self.arena.dupe(u8, s);
    const string_ptr = StringPtr.global(self.dag.strings.intern(self.arena, owned));
    pushExpr(self, idx, .mk(.{ .string_lit = .{ .ptr = string_ptr } }));
}

pub fn doSucc(self: *Parser, idx: BackRef, prev: u32) ParseError!void {
    const l = try getLevelPtr(self, prev);
    pushLevel(self, idx, .mk(.{ .succ = l }));
}

pub fn doMax(self: *Parser, idx: BackRef, a: u32, b: u32) ParseError!void {
    const l = try getLevelPtr(self, a);
    const r = try getLevelPtr(self, b);
    pushLevel(self, idx, .mk(.{ .max = .{ .l = l, .r = r } }));
}

pub fn doImax(self: *Parser, idx: BackRef, a: u32, b: u32) ParseError!void {
    const l = try getLevelPtr(self, a);
    const r = try getLevelPtr(self, b);
    pushLevel(self, idx, .mk(.{ .imax = .{ .l = l, .r = r } }));
}

pub fn doLevelParam(self: *Parser, idx: BackRef, name_idx: u32) ParseError!void {
    const n = try getNamePtr(self, name_idx);
    pushLevel(self, idx, .mk(.{ .param = n }));
}

pub fn doSort(self: *Parser, idx: BackRef, level_idx: u32) ParseError!void {
    const lvl = try getLevelPtr(self, level_idx);
    pushExpr(self, idx, .mk(.{ .sort = .{ .level = lvl } }));
}

pub fn doConst(self: *Parser, ta: std.mem.Allocator, idx: BackRef, name_idx: u32, us: []const u32) ParseError!void {
    const cname = try getNamePtr(self, name_idx);
    const levels = try getLevelsPtr(self, ta, us);
    pushExpr(self, idx, .mk(.{ .@"const" = .{ .name = cname, .levels = levels } }));
}

pub fn doApp(self: *Parser, idx: BackRef, fn_idx: u32, arg_idx: u32) ParseError!void {
    const fun = try getExprPtr(self, fn_idx);
    const arg = try getExprPtr(self, arg_idx);
    pushExpr(self, idx, .mk(.{ .app = .{
        .fun = fun,
        .arg = arg,
    } }));
}

pub fn doBvar(self: *Parser, idx: BackRef, dbj_idx: u16) ParseError!void {
    if (dbj_idx == std.math.maxInt(u16)) return fail("bvar index too large");
    pushExpr(self, idx, .mk(.{ .@"var" = .{ .dbj_idx = dbj_idx } }));
}

pub fn doLam(self: *Parser, idx: BackRef, name_idx: u32, type_idx: u32, body_idx: u32, style: BinderStyle) ParseError!void {
    const binder_name = try getNamePtr(self, name_idx);
    const binder_type = try getExprPtr(self, type_idx);
    const body = try getExprPtr(self, body_idx);
    pushExpr(self, idx, .mk(.{ .lambda = .{
        .binder_name = binder_name,
        .binder_style = style,
        .binder_type = binder_type,
        .body = body,
    } }));
}

pub fn doPi(self: *Parser, idx: BackRef, name_idx: u32, type_idx: u32, body_idx: u32, style: BinderStyle) ParseError!void {
    const binder_name = try getNamePtr(self, name_idx);
    const binder_type = try getExprPtr(self, type_idx);
    const body = try getExprPtr(self, body_idx);
    pushExpr(self, idx, .mk(.{ .pi = .{
        .binder_name = binder_name,
        .binder_style = style,
        .binder_type = binder_type,
        .body = body,
    } }));
}

pub fn doLet(self: *Parser, idx: BackRef, name_idx: u32, type_idx: u32, value_idx: u32, body_idx: u32, nondep: bool) ParseError!void {
    const binder_name = try getNamePtr(self, name_idx);
    const binder_type = try getExprPtr(self, type_idx);
    const val = try getExprPtr(self, value_idx);
    const body = try getExprPtr(self, body_idx);
    const d = self.arena.create(expr.LetData);
    d.* = .{
        .binder_name = binder_name,
        .binder_type = binder_type,
        .val = val,
        .body = body,
        .nondep = nondep,
    };
    pushExpr(self, idx, .mk(.{ .let = .{ .data = d } }));
}

pub fn doProj(self: *Parser, idx: BackRef, ty_name_idx: u32, proj_idx: usize, struct_idx: u32) ParseError!void {
    if (proj_idx > std.math.maxInt(u16)) return fail("proj index too large");
    const ty_name = try getNamePtr(self, ty_name_idx);
    const structure = try getExprPtr(self, struct_idx);
    pushExpr(self, idx, .mk(.{ .proj = .{
        .ty_name = ty_name,
        .idx = proj_idx,
        .structure = structure,
    } }));
}
