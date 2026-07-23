const std = @import("std");
const util = @import("../util.zig");
const env = @import("../env.zig");
const parser = @import("parser.zig");
const json = @import("json.zig");
const item = @import("item.zig");

const NamePtr = @import("../ptr.zig").NamePtr;

const Declar = env.Declar;
const DeclarInfo = env.DeclarInfo;
const ReducibilityHint = env.ReducibilityHint;
const InductiveData = env.InductiveData;
const ConstructorData = env.ConstructorData;
const RecursorData = env.RecursorData;
const RecRule = env.RecRule;

const Parser = parser.Parser;
const ParseError = parser.ParseError;
const fail = parser.fail;
const Value = json.Value;

const DefinitionSafety = enum { unsafe_, safe, partial };

fn parseSafety(v: Value) ParseError!DefinitionSafety {
    const s = try json.asStr(v);
    if (std.mem.eql(u8, s, "unsafe")) return .unsafe_;
    if (std.mem.eql(u8, s, "safe")) return .safe;
    if (std.mem.eql(u8, s, "partial")) return .partial;
    return fail("unknown safety");
}

fn parseReducibilityHint(v: Value) ParseError!ReducibilityHint {
    switch (v) {
        .string => |s| {
            if (std.mem.eql(u8, s, "opaque")) return .opaque_;
            if (std.mem.eql(u8, s, "abbrev")) return .abbrev;
            return fail("unknown hint");
        },
        .object => {
            if (v.get("regular")) |r| {
                return ReducibilityHint{ .regular = try json.asU16(r) };
            }
            if (v.get("opaque") != null) return .opaque_;
            if (v.get("abbrev") != null) return .abbrev;
            if (v.get("kind")) |k| {
                const s = try json.asStr(k);
                if (std.mem.eql(u8, s, "opaque")) return .opaque_;
                if (std.mem.eql(u8, s, "abbrev")) return .abbrev;
                if (std.mem.eql(u8, s, "regular")) {
                    if (v.get("depth")) |d| return ReducibilityHint{ .regular = try json.asU16(d) };
                    return ReducibilityHint{ .regular = 0 };
                }
            }
            return fail("unknown hint");
        },
        else => return fail("unknown hint"),
    }
}

fn nameToString(self: *const Parser, n: NamePtr) []const u8 {
    switch (n.asRef().kind) {
        .anon => return util.smp_allocator.alloc(u8, 0) catch util.oom(),
        .str => |s| {
            const pfx = nameToString(self, s.pfx);
            defer util.smp_allocator.free(pfx);
            const sfx = s.sfx.asRef().*;
            return joinName(pfx, sfx);
        },
        .num => |n2| {
            const pfx = nameToString(self, n2.pfx);
            defer util.smp_allocator.free(pfx);
            var buf: [32]u8 = undefined;
            const sfx = std.fmt.bufPrint(&buf, "{d}", .{n2.n}) catch @panic("name fmt");
            return joinName(pfx, sfx);
        },
    }
}

fn joinName(pfx: []const u8, sfx: []const u8) []const u8 {
    if (pfx.len == 0) {
        return util.smp_allocator.dupe(u8, sfx) catch util.oom();
    }
    var out = util.smp_allocator.alloc(u8, pfx.len + 1 + sfx.len) catch util.oom();
    @memcpy(out[0..pfx.len], pfx);
    out[pfx.len] = '.';
    @memcpy(out[pfx.len + 1 ..], sfx);
    return out;
}

const AxiomDecision = enum { permit, skip, reject };

fn axiomDecision(self: *const Parser, n: NamePtr) AxiomDecision {
    switch (self.config.axiom_policy) {
        .unsafe_permit_all => return .permit,
        .permitted => |p| {
            const s = nameToString(self, n);
            defer util.smp_allocator.free(s);
            for (p.axioms) |a| {
                if (std.mem.eql(u8, a, s)) {
                    return .permit;
                }
            }
            return switch (p.on_unpermitted) {
                .hard_error => .reject,
                .skip => .skip,
            };
        },
    }
}

fn insertDeclar(self: *Parser, n: NamePtr, d: Declar) ParseError!void {
    if (self.declars.get(n) != null) return fail("duplicate declaration in export file");
    self.declars.put(util.smp_allocator, n, d) catch util.oom();
}

pub fn parseAxiom(self: *Parser, ta: std.mem.Allocator, v: Value) ParseError!void {
    const o = try json.asObject(v);
    const is_unsafe = try json.asBool(o.get("isUnsafe") orelse return fail("missing isUnsafe"));
    if (is_unsafe) return fail("unsafe declarations are not supported");
    const aname = try item.getNamePtr(self, try json.asU32(o.get("name") orelse return fail("missing name")));
    const uparams = try item.getUparamsPtr(self, ta, try json.asU32Array(ta, o.get("levelParams") orelse return fail("missing levelParams")));
    const ty = try item.getExprPtr(self, try json.asU32(o.get("type") orelse return fail("missing type")));
    const info = DeclarInfo{ .name = aname, .ty = ty, .uparams = uparams };
    const axiom = Declar{ .axiom = .{ .info = info } };
    switch (axiomDecision(self, aname)) {
        .permit => try insertDeclar(self, aname, axiom),
        .reject => return fail("export file declares unpermitted axiom"),
        .skip => self.skipped.append(util.smp_allocator, nameToString(self, aname)) catch util.oom(),
    }
}

pub fn parseDef(self: *Parser, ta: std.mem.Allocator, v: Value) ParseError!void {
    const o = try json.asObject(v);
    const safety = try parseSafety(o.get("safety") orelse return fail("missing safety"));
    if (safety != .safe) return fail("unsafe and partial definitions are not supported");
    const dname = try item.getNamePtr(self, try json.asU32(o.get("name") orelse return fail("missing name")));
    const ty = try item.getExprPtr(self, try json.asU32(o.get("type") orelse return fail("missing type")));
    const val = try item.getExprPtr(self, try json.asU32(o.get("value") orelse return fail("missing value")));
    const uparams = try item.getUparamsPtr(self, ta, try json.asU32Array(ta, o.get("levelParams") orelse return fail("missing levelParams")));
    const hint = try parseReducibilityHint(o.get("hints") orelse return fail("missing hints"));
    const info = DeclarInfo{ .name = dname, .ty = ty, .uparams = uparams };
    const definition = Declar{ .definition = .{ .info = info, .val = val, .hint = hint } };
    try insertDeclar(self, dname, definition);
}

pub fn parseThm(self: *Parser, ta: std.mem.Allocator, v: Value) ParseError!void {
    const o = try json.asObject(v);
    const tname = try item.getNamePtr(self, try json.asU32(o.get("name") orelse return fail("missing name")));
    const ty = try item.getExprPtr(self, try json.asU32(o.get("type") orelse return fail("missing type")));
    const val = try item.getExprPtr(self, try json.asU32(o.get("value") orelse return fail("missing value")));
    const uparams = try item.getUparamsPtr(self, ta, try json.asU32Array(ta, o.get("levelParams") orelse return fail("missing levelParams")));
    const info = DeclarInfo{ .name = tname, .ty = ty, .uparams = uparams };
    const theorem = Declar{ .theorem = .{ .info = info, .val = val } };
    try insertDeclar(self, tname, theorem);
}

pub fn parseOpaque(self: *Parser, ta: std.mem.Allocator, v: Value) ParseError!void {
    const o = try json.asObject(v);
    const is_unsafe = try json.asBool(o.get("isUnsafe") orelse return fail("missing isUnsafe"));
    if (is_unsafe) return fail("unsafe declarations are not supported");
    const oname = try item.getNamePtr(self, try json.asU32(o.get("name") orelse return fail("missing name")));
    const ty = try item.getExprPtr(self, try json.asU32(o.get("type") orelse return fail("missing type")));
    const val = try item.getExprPtr(self, try json.asU32(o.get("value") orelse return fail("missing value")));
    const uparams = try item.getUparamsPtr(self, ta, try json.asU32Array(ta, o.get("levelParams") orelse return fail("missing levelParams")));
    const info = DeclarInfo{ .name = oname, .ty = ty, .uparams = uparams };
    const definition = Declar{ .opaque_ = .{ .info = info, .val = val } };
    try insertDeclar(self, oname, definition);
}

pub fn parseQuot(self: *Parser, ta: std.mem.Allocator, v: Value) ParseError!void {
    const o = try json.asObject(v);
    const qname = try item.getNamePtr(self, try json.asU32(o.get("name") orelse return fail("missing name")));
    const ty = try item.getExprPtr(self, try json.asU32(o.get("type") orelse return fail("missing type")));
    const uparams = try item.getUparamsPtr(self, ta, try json.asU32Array(ta, o.get("levelParams") orelse return fail("missing levelParams")));
    const info = DeclarInfo{ .name = qname, .ty = ty, .uparams = uparams };
    const quot = Declar{ .quot = .{ .info = info } };
    try insertDeclar(self, qname, quot);
}

pub fn parseInductive(self: *Parser, ta: std.mem.Allocator, v: Value) ParseError!void {
    const o = try json.asObject(v);
    const ind_vals = try json.asArray(o.get("types") orelse return fail("missing types"));
    const ctor_vals = try json.asArray(o.get("ctors") orelse return fail("missing ctors"));
    const rec_vals = try json.asArray(o.get("recs") orelse return fail("missing recs"));
    const block_start = self.declars.count();
    const block_size = ind_vals.len + ctor_vals.len + rec_vals.len;
    for (ind_vals) |ind_v| {
        const io = try json.asObject(ind_v);
        const is_unsafe = try json.asBool(io.get("isUnsafe") orelse return fail("missing isUnsafe"));
        if (is_unsafe) return fail("unsafe declarations are not supported");
        const iname = try item.getNamePtr(self, try json.asU32(io.get("name") orelse return fail("missing name")));
        self.mutual_block_sizes.put(util.smp_allocator, iname, .{ block_start, block_size }) catch util.oom();
        const uparams = try item.getUparamsPtr(self, ta, try json.asU32Array(ta, io.get("levelParams") orelse return fail("missing levelParams")));
        const ty = try item.getExprPtr(self, try json.asU32(io.get("type") orelse return fail("missing type")));
        const all_ind_names = self.arena.dupe(NamePtr, try item.getNames(self, ta, try json.asU32Array(ta, io.get("all") orelse return fail("missing all"))));
        const all_ctor_names = self.arena.dupe(NamePtr, try item.getNames(self, ta, try json.asU32Array(ta, io.get("ctors") orelse return fail("missing ctors"))));
        const is_rec = try json.asBool(io.get("isRec") orelse return fail("missing isRec"));
        const num_nested = try json.asU16(io.get("numNested") orelse return fail("missing numNested"));
        const num_params = try json.asU16(io.get("numParams") orelse return fail("missing numParams"));
        const num_indices = try json.asU16(io.get("numIndices") orelse return fail("missing numIndices"));
        const inductive = Declar{ .inductive = InductiveData{
            .info = DeclarInfo{ .name = iname, .uparams = uparams, .ty = ty },
            .is_recursive = is_rec,
            .is_nested = num_nested > 0,
            .num_params = num_params,
            .num_indices = num_indices,
            .all_ind_names = all_ind_names,
            .all_ctor_names = all_ctor_names,
        } };
        try insertDeclar(self, iname, inductive);
    }
    for (ctor_vals) |ctor_v| {
        const co = try json.asObject(ctor_v);
        const is_unsafe = try json.asBool(co.get("isUnsafe") orelse return fail("missing isUnsafe"));
        if (is_unsafe) return fail("unsafe declarations are not supported");
        const cname = try item.getNamePtr(self, try json.asU32(co.get("name") orelse return fail("missing name")));
        const ty = try item.getExprPtr(self, try json.asU32(co.get("type") orelse return fail("missing type")));
        const uparams = try item.getUparamsPtr(self, ta, try json.asU32Array(ta, co.get("levelParams") orelse return fail("missing levelParams")));
        const info = DeclarInfo{ .name = cname, .ty = ty, .uparams = uparams };
        const parent_inductive = try item.getNamePtr(self, try json.asU32(co.get("induct") orelse return fail("missing induct")));
        const ctor_idx = try json.asU16(co.get("cidx") orelse return fail("missing cidx"));
        const num_params = try json.asU16(co.get("numParams") orelse return fail("missing numParams"));
        const num_fields = try json.asU16(co.get("numFields") orelse return fail("missing numFields"));
        const ctor = Declar{ .constructor = ConstructorData{
            .info = info,
            .inductive_name = parent_inductive,
            .ctor_idx = ctor_idx,
            .num_params = num_params,
            .num_fields = num_fields,
        } };
        try insertDeclar(self, cname, ctor);
    }
    for (rec_vals) |rec_v| {
        const ro = try json.asObject(rec_v);
        const is_unsafe = try json.asBool(ro.get("isUnsafe") orelse return fail("missing isUnsafe"));
        if (is_unsafe) return fail("unsafe declarations are not supported");
        const rname = try item.getNamePtr(self, try json.asU32(ro.get("name") orelse return fail("missing name")));
        const ty = try item.getExprPtr(self, try json.asU32(ro.get("type") orelse return fail("missing type")));
        const uparams = try item.getUparamsPtr(self, ta, try json.asU32Array(ta, ro.get("levelParams") orelse return fail("missing levelParams")));
        const info = DeclarInfo{ .name = rname, .ty = ty, .uparams = uparams };
        const rules_arr = try json.asArray(ro.get("rules") orelse return fail("missing rules"));
        var rules = ta.alloc(RecRule, rules_arr.len) catch util.oom();
        for (rules_arr, 0..) |rule_v, i| {
            const rr = try json.asObject(rule_v);
            rules[i] = RecRule{
                .val = try item.getExprPtr(self, try json.asU32(rr.get("rhs") orelse return fail("missing rhs"))),
                .ctor_name = try item.getNamePtr(self, try json.asU32(rr.get("ctor") orelse return fail("missing ctor"))),
                .ctor_telescope_size_wo_params = try json.asU16(rr.get("nfields") orelse return fail("missing nfields")),
            };
        }
        const num_params = try json.asU16(ro.get("numParams") orelse return fail("missing numParams"));
        const num_indices = try json.asU16(ro.get("numIndices") orelse return fail("missing numIndices"));
        const num_motives = try json.asU16(ro.get("numMotives") orelse return fail("missing numMotives"));
        const num_minors = try json.asU16(ro.get("numMinors") orelse return fail("missing numMinors"));
        const k = try json.asBool(ro.get("k") orelse return fail("missing k"));
        const all_inductives = try item.getNames(self, ta, try json.asU32Array(ta, ro.get("all") orelse return fail("missing all")));
        const recursor = Declar{ .recursor = RecursorData{
            .info = info,
            .all_inductives = self.arena.dupe(NamePtr, all_inductives),
            .num_params = num_params,
            .num_indices = num_indices,
            .num_motives = num_motives,
            .num_minors = num_minors,
            .rec_rules = self.arena.dupe(RecRule, rules),
            .is_k = k,
        } };
        try insertDeclar(self, rname, recursor);
    }
}
