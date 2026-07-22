const std = @import("std");
const util = @import("util.zig");
const Arena = @import("Arena.zig");
const hash64 = @import("hash.zig").hash64;
const interner = @import("interner.zig");
const swiss_map = @import("swiss_map.zig");
const env = @import("env.zig");
const expr = @import("expr.zig");
const level = @import("level.zig");
const name = @import("name.zig");

const Config = @import("export_file.zig").Config;
const Dag = @import("Dag.zig");
const nat = @import("nat.zig");
const ExportFile = @import("export_file.zig").ExportFile;

const NamePtr = @import("ptr.zig").NamePtr;
const LevelPtr = @import("ptr.zig").LevelPtr;
const LevelsPtr = @import("ptr.zig").LevelsPtr;
const ExprPtr = @import("ptr.zig").ExprPtr;
const StringPtr = @import("ptr.zig").StringPtr;
const BigUintPtr = @import("ptr.zig").BigUintPtr;

const name_nil: NamePtr = @enumFromInt(0);
const level_nil: LevelPtr = @enumFromInt(0);
const expr_nil: ExprPtr = @enumFromInt(0);

const Name = name.Name;
const Level = level.Level;
const Expr = expr.Expr;
const BinderStyle = expr.BinderStyle;

const Declar = env.Declar;
const DeclarInfo = env.DeclarInfo;
const ReducibilityHint = env.ReducibilityHint;
const InductiveData = env.InductiveData;
const ConstructorData = env.ConstructorData;
const RecursorData = env.RecursorData;
const RecRule = env.RecRule;

const min_semver = std.SemanticVersion{ .major = 3, .minor = 1, .patch = 0 };
const max_semver = std.SemanticVersion{ .major = 3, .minor = 2, .patch = 0 };

fn checkSemver(version: []const u8) ParseError!void {
    const export_file_semver = std.SemanticVersion.parse(version) catch {
        return fail("export format version could not be parsed as semver");
    };
    if (export_file_semver.order(min_semver) == .lt) {
        return fail("export format version is less than the minimum supported version");
    }
    if (export_file_semver.order(max_semver) != .lt) {
        return fail("export format version is greater than the maximum supported version");
    }
}

pub const ParseError = error{ParseFailed};

fn fail(msg: []const u8) ParseError {
    std.debug.print("{s}\n", .{msg});
    return error.ParseFailed;
}

const BackRefKind = enum { in_, il, ie };

const BackRef = struct {
    kind: BackRefKind,
    i: u32,

    fn index(self: BackRef) u32 {
        return self.i;
    }
};

pub const Parser = struct {
    line_num: usize,
    arena: *Arena,
    dag: Dag,
    anon: NamePtr,
    zero: LevelPtr,
    names_by_idx: std.ArrayList(NamePtr),
    levels_by_idx: std.ArrayList(LevelPtr),
    exprs_by_idx: std.ArrayList(ExprPtr),
    pending_exprs: std.ArrayList(interner.ExprInterner.BuildEntry),
    declars: env.DeclarMap,
    config: Config,
    skipped: std.ArrayList([]const u8),
    mutual_block_sizes: swiss_map.FxHashMap(NamePtr, struct { usize, usize }),

    pub fn init(ar: *Arena, config: Config) Parser {
        var dag = Dag.init(&config);
        const anon = NamePtr.global(dag.names.intern(ar, Name.anon));
        const zero = LevelPtr.global(dag.levels.intern(ar, Level.zero));
        var names_by_idx: std.ArrayList(NamePtr) = .empty;
        names_by_idx.append(util.smp_allocator, anon) catch util.oom();
        var levels_by_idx: std.ArrayList(LevelPtr) = .empty;
        levels_by_idx.append(util.smp_allocator, zero) catch util.oom();
        return .{
            .line_num = 0,
            .arena = ar,
            .dag = dag,
            .anon = anon,
            .zero = zero,
            .names_by_idx = names_by_idx,
            .levels_by_idx = levels_by_idx,
            .exprs_by_idx = .empty,
            .pending_exprs = .empty,
            .declars = swiss_map.FxIndexMap(NamePtr, Declar).empty,
            .config = config,
            .skipped = .empty,
            .mutual_block_sizes = swiss_map.FxHashMap(NamePtr, struct { usize, usize }).empty,
        };
    }
};

const RECLAIM_WINDOW: usize = 64 << 20;

fn reclaimConsumed(input: []const u8, dropped: usize, consumed: usize) usize {
    const page = std.heap.pageSize();
    const base = @intFromPtr(input.ptr);
    const start = std.mem.alignForward(usize, base + dropped, page);
    const end = std.mem.alignBackward(usize, base + consumed, page);
    if (end <= start) return dropped;
    const ptr: [*]align(std.heap.page_size_min) u8 = @ptrFromInt(start);
    std.posix.madvise(ptr, end - start, std.posix.MADV.DONTNEED) catch return dropped;
    return end - base;
}

pub fn parseExportFile(ar: *Arena, input: []const u8, config: Config) ParseError!struct { ExportFile, []const []const u8 } {
    var parser = Parser.init(ar, config);
    var scratch = std.heap.ArenaAllocator.init(util.smp_allocator);
    defer scratch.deinit();
    var dropped: usize = 0;
    var next_reclaim: usize = RECLAIM_WINDOW;
    var lines = std.mem.splitScalar(u8, input, '\n');
    while (lines.next()) |raw_line| {
        if (raw_line.len == 0) continue;
        const consumed = @intFromPtr(raw_line.ptr) - @intFromPtr(input.ptr);
        if (consumed >= next_reclaim) {
            dropped = reclaimConsumed(input, dropped, consumed);
            next_reclaim = consumed + RECLAIM_WINDOW;
        }
        defer _ = scratch.reset(.retain_capacity);
        try go1(&parser, scratch.allocator(), raw_line);
        parser.line_num += 1;
    }

    parser.dag.exprs.buildUnique(parser.pending_exprs.items);
    parser.pending_exprs.deinit(util.smp_allocator);
    parser.names_by_idx.deinit(util.smp_allocator);
    parser.levels_by_idx.deinit(util.smp_allocator);
    parser.exprs_by_idx.deinit(util.smp_allocator);

    const name_cache = parser.dag.mkNameCache(parser.anon);
    const export_file = ExportFile{
        .dag = parser.dag,
        .anon = parser.anon,
        .zero = parser.zero,
        .declars = parser.declars,
        .name_cache = name_cache,
        .config = parser.config,
        .mutual_block_sizes = parser.mutual_block_sizes,
    };
    return .{ export_file, parser.skipped.items };
}

fn pushName(self: *Parser, expected: BackRef, n: Name) void {
    const ptr = NamePtr.global(self.dag.names.insertUnique(self.arena, n));
    const i = @as(usize, expected.index());
    if (i >= self.names_by_idx.items.len) {
        resizeOpt(NamePtr, &self.names_by_idx, i + 1, name_nil);
    }
    self.names_by_idx.items[i] = ptr;
}

fn pushLevel(self: *Parser, expected: BackRef, l: Level) void {
    const ptr = LevelPtr.global(self.dag.levels.insertUnique(self.arena, l));
    const i = @as(usize, expected.index());
    if (i >= self.levels_by_idx.items.len) {
        resizeOpt(LevelPtr, &self.levels_by_idx, i + 1, level_nil);
    }
    self.levels_by_idx.items[i] = ptr;
}

fn pushExpr(self: *Parser, expected: BackRef, e: Expr) void {
    const r = self.arena.create(Expr);
    r.* = e;
    self.pending_exprs.append(util.smp_allocator, .{ .hash = e.hash, .ref = r }) catch util.oom();
    const ptr = ExprPtr.global(r);
    const i = @as(usize, expected.index());
    if (i >= self.exprs_by_idx.items.len) {
        resizeOpt(ExprPtr, &self.exprs_by_idx, i + 1, expr_nil);
    }
    self.exprs_by_idx.items[i] = ptr;
}

fn resizeOpt(comptime T: type, list: *std.ArrayList(T), new_len: usize, nil: T) void {
    const old_len = list.items.len;
    list.resize(util.smp_allocator, new_len) catch util.oom();
    @memset(list.items[old_len..], nil);
}

fn axiomPermitted(self: *const Parser, n: NamePtr) bool {
    if (self.config.unsafe_permit_all_axioms) {
        return true;
    }
    if (self.config.permitted_axioms) |v| {
        const s = nameToString(self, n);
        defer util.smp_allocator.free(s);
        for (v) |a| {
            if (std.mem.eql(u8, a, s)) {
                return true;
            }
        }
        return false;
    }
    return false;
}

fn numLooseBvars(self: *const Parser, e: ExprPtr) u16 {
    _ = self;
    return e.asRef().numLooseBvars();
}

fn hasFvars(self: *const Parser, e: ExprPtr) bool {
    _ = self;
    return e.asRef().hasFvars();
}

fn getNamePtr(self: *const Parser, idx: u32) ParseError!NamePtr {
    if (idx < self.names_by_idx.items.len) {
        const p = self.names_by_idx.items[idx];
        if (p != name_nil) return p;
    }
    return fail("export references name index before it is defined");
}

fn getLevelPtr(self: *const Parser, idx: u32) ParseError!LevelPtr {
    if (idx < self.levels_by_idx.items.len) {
        const p = self.levels_by_idx.items[idx];
        if (p != level_nil) return p;
    }
    return fail("export references level index before it is defined");
}

fn getNames(self: *const Parser, ta: std.mem.Allocator, idxs: []const u32) ParseError![]const NamePtr {
    var out = ta.alloc(NamePtr, idxs.len) catch util.oom();
    for (idxs, 0..) |idx, i| {
        out[i] = try getNamePtr(self, idx);
    }
    return out;
}

fn getUparamsPtr(self: *Parser, ta: std.mem.Allocator, name_idxs: []const u32) ParseError!LevelsPtr {
    var levels = ta.alloc(LevelPtr, name_idxs.len) catch util.oom();
    for (name_idxs, 0..) |name_idx, i| {
        const name_ptr = try getNamePtr(self, name_idx);
        const hash = hash64(.{ level.param_hash, name_ptr });
        const probe = Level{ .hash = hash, .kind = .{ .param = name_ptr } };
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

fn getExprPtr(self: *const Parser, idx: u32) ParseError!ExprPtr {
    if (idx < self.exprs_by_idx.items.len) {
        const p = self.exprs_by_idx.items[idx];
        if (p != expr_nil) return p;
    }
    return fail("export references expression index before it is defined");
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

fn parseUint(comptime T: type, s: []const u8) ParseError!T {
    if (s.len == 0 or s.len > 19) return fail("expected integer");
    var x: u64 = 0;
    for (s) |c| {
        if (c < '0' or c > '9') return fail("expected integer");
        x = x * 10 + (c - '0');
    }
    return std.math.cast(T, x) orelse fail("integer out of range");
}

fn asU32(v: JVal) ParseError!u32 {
    return switch (v) {
        .number => |s| parseUint(u32, s),
        else => fail("expected integer"),
    };
}

fn asU16(v: JVal) ParseError!u16 {
    return switch (v) {
        .number => |s| parseUint(u16, s),
        else => fail("expected integer"),
    };
}

fn asUsize(v: JVal) ParseError!usize {
    return switch (v) {
        .number => |s| parseUint(usize, s),
        else => fail("expected integer"),
    };
}

fn asBool(v: JVal) ParseError!bool {
    return switch (v) {
        .boolean => |b| b,
        else => fail("expected bool"),
    };
}

fn asStr(v: JVal) ParseError![]const u8 {
    return switch (v) {
        .string => |s| s,
        else => fail("expected string"),
    };
}

fn asU32Array(ta: std.mem.Allocator, v: JVal) ParseError![]const u32 {
    const arr = switch (v) {
        .array => |a| a,
        else => return fail("expected array"),
    };
    var out = ta.alloc(u32, arr.len) catch util.oom();
    for (arr, 0..) |item, i| {
        out[i] = try asU32(item);
    }
    return out;
}

fn binderStyleOf(s: []const u8) ?BinderStyle {
    switch (s.len) {
        7 => if (std.mem.eql(u8, s, "default")) return .default,
        8 => if (std.mem.eql(u8, s, "implicit")) return .implicit,
        14 => if (std.mem.eql(u8, s, "strictImplicit")) return .strict_implicit,
        12 => if (std.mem.eql(u8, s, "instImplicit")) return .instance_implicit,
        else => {},
    }
    return null;
}

fn parseBinderStyle(v: JVal) ParseError!BinderStyle {
    return binderStyleOf(try asStr(v)) orelse fail("unknown binderInfo");
}

const DefinitionSafety = enum { unsafe_, safe, partial };

fn parseSafety(v: JVal) ParseError!DefinitionSafety {
    const s = try asStr(v);
    if (std.mem.eql(u8, s, "unsafe")) return .unsafe_;
    if (std.mem.eql(u8, s, "safe")) return .safe;
    if (std.mem.eql(u8, s, "partial")) return .partial;
    return fail("unknown safety");
}

fn parseReducibilityHint(v: JVal) ParseError!ReducibilityHint {
    switch (v) {
        .string => |s| {
            if (std.mem.eql(u8, s, "opaque")) return .opaque_;
            if (std.mem.eql(u8, s, "abbrev")) return .abbrev;
            return fail("unknown hint");
        },
        .object => {
            if (v.get("regular")) |r| {
                return ReducibilityHint{ .regular = try asU16(r) };
            }
            if (v.get("opaque") != null) return .opaque_;
            if (v.get("abbrev") != null) return .abbrev;
            if (v.get("kind")) |k| {
                const s = try asStr(k);
                if (std.mem.eql(u8, s, "opaque")) return .opaque_;
                if (std.mem.eql(u8, s, "abbrev")) return .abbrev;
                if (std.mem.eql(u8, s, "regular")) {
                    if (v.get("depth")) |d| return ReducibilityHint{ .regular = try asU16(d) };
                    return ReducibilityHint{ .regular = 0 };
                }
            }
            return fail("unknown hint");
        },
        else => return fail("unknown hint"),
    }
}

const Kind = enum {
    meta,
    str,
    num,
    natVal,
    strVal,
    succ,
    max,
    imax,
    param,
    sort,
    mdata,
    @"const",
    app,
    bvar,
    lam,
    forallE,
    letE,
    proj,
    axiom,
    def,
    thm,
    @"opaque",
    quot,
    inductive,
};

const kind_map = std.StaticStringMap(Kind).initComptime(.{
    .{ "meta", .meta },
    .{ "str", .str },
    .{ "num", .num },
    .{ "natVal", .natVal },
    .{ "strVal", .strVal },
    .{ "succ", .succ },
    .{ "max", .max },
    .{ "imax", .imax },
    .{ "param", .param },
    .{ "sort", .sort },
    .{ "mdata", .mdata },
    .{ "const", .@"const" },
    .{ "app", .app },
    .{ "bvar", .bvar },
    .{ "lam", .lam },
    .{ "forallE", .forallE },
    .{ "letE", .letE },
    .{ "proj", .proj },
    .{ "axiom", .axiom },
    .{ "def", .def },
    .{ "thm", .thm },
    .{ "opaque", .@"opaque" },
    .{ "quot", .quot },
    .{ "inductive", .inductive },
});

fn kindv(kind: ?Kind, kv: JVal, comptime tag: Kind) ?JVal {
    if (kind != null and kind.? == tag) return kv;
    return null;
}

const Member = struct { key: []const u8, value: JVal };

const JVal = union(enum) {
    object: []const Member,
    array: []const JVal,
    string: []const u8,
    number: []const u8,
    boolean: bool,
    nul: void,

    fn get(self: JVal, key: []const u8) ?JVal {
        switch (self) {
            .object => |ms| {
                for (ms) |m| {
                    if (std.mem.eql(u8, m.key, key)) return m.value;
                }
                return null;
            },
            else => return null,
        }
    }
};

const Jp = struct {
    s: []const u8,
    i: usize,
    a: std.mem.Allocator,

    fn skipWs(self: *Jp) void {
        while (self.i < self.s.len) {
            switch (self.s[self.i]) {
                ' ', '\t', '\n', '\r' => self.i += 1,
                else => return,
            }
        }
    }

    fn value(self: *Jp) ParseError!JVal {
        self.skipWs();
        if (self.i >= self.s.len) return fail("unexpected end of JSON");
        switch (self.s[self.i]) {
            '{' => return self.object(),
            '[' => return self.array(),
            '"' => return JVal{ .string = try self.string() },
            't' => {
                if (self.i + 4 > self.s.len or !std.mem.eql(u8, self.s[self.i .. self.i + 4], "true")) return fail("invalid literal");
                self.i += 4;
                return JVal{ .boolean = true };
            },
            'f' => {
                if (self.i + 5 > self.s.len or !std.mem.eql(u8, self.s[self.i .. self.i + 5], "false")) return fail("invalid literal");
                self.i += 5;
                return JVal{ .boolean = false };
            },
            'n' => {
                if (self.i + 4 > self.s.len or !std.mem.eql(u8, self.s[self.i .. self.i + 4], "null")) return fail("invalid literal");
                self.i += 4;
                return JVal.nul;
            },
            else => return JVal{ .number = self.number() },
        }
    }

    fn object(self: *Jp) ParseError!JVal {
        self.i += 1;
        var members = std.ArrayList(Member).initCapacity(self.a, 12) catch util.oom();
        self.skipWs();
        if (self.i < self.s.len and self.s[self.i] == '}') {
            self.i += 1;
            return JVal{ .object = members.items };
        }
        while (true) {
            self.skipWs();
            if (self.i >= self.s.len or self.s[self.i] != '"') return fail("expected object key");
            const key = try self.string();
            self.skipWs();
            if (self.i >= self.s.len or self.s[self.i] != ':') return fail("expected ':'");
            self.i += 1;
            const val = try self.value();
            members.append(self.a, Member{ .key = key, .value = val }) catch util.oom();
            self.skipWs();
            if (self.i >= self.s.len) return fail("unterminated object");
            if (self.s[self.i] == ',') {
                self.i += 1;
                continue;
            }
            if (self.s[self.i] == '}') {
                self.i += 1;
                break;
            }
            return fail("expected ',' or '}'");
        }
        return JVal{ .object = members.items };
    }

    fn array(self: *Jp) ParseError!JVal {
        self.i += 1;
        var items = std.ArrayList(JVal).initCapacity(self.a, 8) catch util.oom();
        self.skipWs();
        if (self.i < self.s.len and self.s[self.i] == ']') {
            self.i += 1;
            return JVal{ .array = items.items };
        }
        while (true) {
            const val = try self.value();
            items.append(self.a, val) catch util.oom();
            self.skipWs();
            if (self.i >= self.s.len) return fail("unterminated array");
            if (self.s[self.i] == ',') {
                self.i += 1;
                continue;
            }
            if (self.s[self.i] == ']') {
                self.i += 1;
                break;
            }
            return fail("expected ',' or ']'");
        }
        return JVal{ .array = items.items };
    }

    fn number(self: *Jp) []const u8 {
        const start = self.i;
        while (self.i < self.s.len) {
            switch (self.s[self.i]) {
                '0'...'9', '-', '+', '.', 'e', 'E' => self.i += 1,
                else => break,
            }
        }
        return self.s[start..self.i];
    }

    fn string(self: *Jp) ParseError![]const u8 {
        self.i += 1;
        const start = self.i;
        var has_escape = false;
        while (self.i < self.s.len) {
            const c = self.s[self.i];
            if (c == '"') {
                const raw = self.s[start..self.i];
                self.i += 1;
                if (!has_escape) return raw;
                return self.unescape(raw);
            }
            if (c == '\\') {
                has_escape = true;
                self.i += 2;
                continue;
            }
            self.i += 1;
        }
        return fail("unterminated string");
    }

    fn unescape(self: *Jp, raw: []const u8) ParseError![]const u8 {
        var out = std.ArrayList(u8).empty;
        var k: usize = 0;
        while (k < raw.len) {
            const c = raw[k];
            if (c != '\\') {
                out.append(self.a, c) catch util.oom();
                k += 1;
                continue;
            }
            k += 1;
            if (k >= raw.len) return fail("bad escape");
            switch (raw[k]) {
                '"' => {
                    out.append(self.a, '"') catch util.oom();
                    k += 1;
                },
                '\\' => {
                    out.append(self.a, '\\') catch util.oom();
                    k += 1;
                },
                '/' => {
                    out.append(self.a, '/') catch util.oom();
                    k += 1;
                },
                'b' => {
                    out.append(self.a, 0x08) catch util.oom();
                    k += 1;
                },
                'f' => {
                    out.append(self.a, 0x0c) catch util.oom();
                    k += 1;
                },
                'n' => {
                    out.append(self.a, '\n') catch util.oom();
                    k += 1;
                },
                'r' => {
                    out.append(self.a, '\r') catch util.oom();
                    k += 1;
                },
                't' => {
                    out.append(self.a, '\t') catch util.oom();
                    k += 1;
                },
                'u' => {
                    if (k + 5 > raw.len) return fail("bad unicode escape");
                    var cp: u32 = std.fmt.parseInt(u32, raw[k + 1 .. k + 5], 16) catch return fail("bad unicode escape");
                    k += 5;
                    if (cp >= 0xD800 and cp <= 0xDBFF) {
                        if (k + 6 > raw.len or raw[k] != '\\' or raw[k + 1] != 'u') return fail("bad surrogate pair");
                        const lo: u32 = std.fmt.parseInt(u32, raw[k + 2 .. k + 6], 16) catch return fail("bad surrogate pair");
                        if (lo < 0xDC00 or lo > 0xDFFF) return fail("bad surrogate pair");
                        cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                        k += 6;
                    }
                    var buf: [4]u8 = undefined;
                    const n = std.unicode.utf8Encode(@intCast(cp), &buf) catch return fail("bad codepoint");
                    out.appendSlice(self.a, buf[0..n]) catch util.oom();
                },
                else => return fail("bad escape"),
            }
        }
        return out.items;
    }
};

fn doStr(self: *Parser, idx: BackRef, pre: u32, s: []const u8) ParseError!void {
    const pfx = try getNamePtr(self, pre);
    const owned = self.arena.dupe(u8, s);
    const sfx = StringPtr.global(self.dag.strings.intern(self.arena, owned));
    const hash = hash64(.{ name.str_hash, pfx, sfx });
    pushName(self, idx, Name{ .hash = hash, .kind = .{ .str = .{ .pfx = pfx, .sfx = sfx } } });
}

fn doNum(self: *Parser, idx: BackRef, pre: u32, i: u32) ParseError!void {
    const pfx = try getNamePtr(self, pre);
    const sfx = @as(u64, i);
    const hash = hash64(.{ name.num_hash, pfx, sfx });
    pushName(self, idx, Name{ .hash = hash, .kind = .{ .num = .{ .pfx = pfx, .n = sfx } } });
}

fn doNatVal(self: *Parser, idx: BackRef, s: []const u8) ParseError!void {
    if (!self.config.nat_extension) {
        return fail("Nat lit extension disallowed by checker execution config, but export file contains a nat literal");
    }
    const big = nat.fromDecimal(s) orelse return fail("invalid BigUint decimal string");
    const num_ptr = BigUintPtr.global(self.dag.bignums.?.intern(self.arena, big));
    const hash = hash64(.{ expr.nat_lit_hash, num_ptr });
    pushExpr(self, idx, Expr{ .hash = hash, .kind = .{ .nat_lit = .{ .ptr = num_ptr } } });
}

fn doStrVal(self: *Parser, idx: BackRef, s: []const u8) ParseError!void {
    if (!self.config.string_extension) {
        return fail("String lit extension disallowed by checker execution config, but export file contains a string literal");
    }
    const owned = self.arena.dupe(u8, s);
    const string_ptr = StringPtr.global(self.dag.strings.intern(self.arena, owned));
    const hash = hash64(.{ expr.string_lit_hash, string_ptr });
    pushExpr(self, idx, Expr{ .hash = hash, .kind = .{ .string_lit = .{ .ptr = string_ptr } } });
}

fn doSucc(self: *Parser, idx: BackRef, prev: u32) ParseError!void {
    const l = try getLevelPtr(self, prev);
    const hash = hash64(.{ level.succ_hash, l });
    pushLevel(self, idx, Level{ .hash = hash, .kind = .{ .succ = l } });
}

fn doMax(self: *Parser, idx: BackRef, a: u32, b: u32) ParseError!void {
    const l = try getLevelPtr(self, a);
    const r = try getLevelPtr(self, b);
    const hash = hash64(.{ level.max_hash, l, r });
    pushLevel(self, idx, Level{ .hash = hash, .kind = .{ .max = .{ .l = l, .r = r } } });
}

fn doImax(self: *Parser, idx: BackRef, a: u32, b: u32) ParseError!void {
    const l = try getLevelPtr(self, a);
    const r = try getLevelPtr(self, b);
    const hash = hash64(.{ level.imax_hash, l, r });
    pushLevel(self, idx, Level{ .hash = hash, .kind = .{ .imax = .{ .l = l, .r = r } } });
}

fn doLevelParam(self: *Parser, idx: BackRef, name_idx: u32) ParseError!void {
    const n = try getNamePtr(self, name_idx);
    const hash = hash64(.{ level.param_hash, n });
    pushLevel(self, idx, Level{ .hash = hash, .kind = .{ .param = n } });
}

fn doSort(self: *Parser, idx: BackRef, level_idx: u32) ParseError!void {
    const lvl = try getLevelPtr(self, level_idx);
    const hash = hash64(.{ expr.sort_hash, lvl });
    pushExpr(self, idx, Expr{ .hash = hash, .kind = .{ .sort = .{ .level = lvl } } });
}

fn doConst(self: *Parser, ta: std.mem.Allocator, idx: BackRef, name_idx: u32, us: []const u32) ParseError!void {
    const cname = try getNamePtr(self, name_idx);
    const levels = try getLevelsPtr(self, ta, us);
    const hash = hash64(.{ expr.const_hash, cname, levels });
    pushExpr(self, idx, Expr{ .hash = hash, .kind = .{ .@"const" = .{ .name = cname, .levels = levels } } });
}

fn doApp(self: *Parser, idx: BackRef, fn_idx: u32, arg_idx: u32) ParseError!void {
    const fun = try getExprPtr(self, fn_idx);
    const arg = try getExprPtr(self, arg_idx);
    const hash = hash64(.{ expr.app_hash, fun, arg });
    const num_bvars = @max(numLooseBvars(self, fun), numLooseBvars(self, arg));
    const locals = hasFvars(self, fun) or hasFvars(self, arg);
    pushExpr(self, idx, Expr{ .hash = hash, .kind = .{ .app = .{
        .fun = fun,
        .arg = arg,
        .num_loose_bvars = num_bvars,
        .has_fvars = locals,
    } } });
}

fn doBvar(self: *Parser, idx: BackRef, dbj_idx: u16) ParseError!void {
    if (dbj_idx == std.math.maxInt(u16)) return fail("bvar index too large");
    const hash = hash64(.{ expr.var_hash, dbj_idx });
    pushExpr(self, idx, Expr{ .hash = hash, .kind = .{ .@"var" = .{ .dbj_idx = dbj_idx } } });
}

fn doLam(self: *Parser, idx: BackRef, name_idx: u32, type_idx: u32, body_idx: u32, style: BinderStyle) ParseError!void {
    const binder_name = try getNamePtr(self, name_idx);
    const binder_type = try getExprPtr(self, type_idx);
    const body = try getExprPtr(self, body_idx);
    const hash = hash64(.{ expr.lambda_hash, binder_name, style, binder_type, body });
    const num_bvars = @max(numLooseBvars(self, binder_type), (numLooseBvars(self, body) -| 1));
    const locals = hasFvars(self, binder_type) or hasFvars(self, body);
    pushExpr(self, idx, Expr{ .hash = hash, .kind = .{ .lambda = .{
        .binder_name = binder_name,
        .binder_style = style,
        .binder_type = binder_type,
        .body = body,
        .num_loose_bvars = num_bvars,
        .has_fvars = locals,
    } } });
}

fn doPi(self: *Parser, idx: BackRef, name_idx: u32, type_idx: u32, body_idx: u32, style: BinderStyle) ParseError!void {
    const binder_name = try getNamePtr(self, name_idx);
    const binder_type = try getExprPtr(self, type_idx);
    const body = try getExprPtr(self, body_idx);
    const hash = hash64(.{ expr.pi_hash, binder_name, style, binder_type, body });
    const num_bvars = @max(numLooseBvars(self, binder_type), (numLooseBvars(self, body) -| 1));
    const locals = hasFvars(self, binder_type) or hasFvars(self, body);
    pushExpr(self, idx, Expr{ .hash = hash, .kind = .{ .pi = .{
        .binder_name = binder_name,
        .binder_style = style,
        .binder_type = binder_type,
        .body = body,
        .num_loose_bvars = num_bvars,
        .has_fvars = locals,
    } } });
}

fn doLet(self: *Parser, idx: BackRef, name_idx: u32, type_idx: u32, value_idx: u32, body_idx: u32, nondep: bool) ParseError!void {
    const binder_name = try getNamePtr(self, name_idx);
    const binder_type = try getExprPtr(self, type_idx);
    const val = try getExprPtr(self, value_idx);
    const body = try getExprPtr(self, body_idx);
    const hash = hash64(.{ expr.let_hash, binder_name, binder_type, val, body, nondep });
    const num_bvars = @max(
        numLooseBvars(self, binder_type),
        @max(numLooseBvars(self, val), (numLooseBvars(self, body) -| 1)),
    );
    const locals = hasFvars(self, binder_type) or hasFvars(self, val) or hasFvars(self, body);
    const d = self.arena.create(expr.LetData);
    d.* = .{
        .binder_name = binder_name,
        .binder_type = binder_type,
        .val = val,
        .body = body,
        .num_loose_bvars = num_bvars,
        .has_fvars = locals,
        .nondep = nondep,
    };
    pushExpr(self, idx, Expr{ .hash = hash, .kind = .{ .let = .{ .data = d } } });
}

fn doProj(self: *Parser, idx: BackRef, ty_name_idx: u32, proj_idx: usize, struct_idx: u32) ParseError!void {
    const ty_name = try getNamePtr(self, ty_name_idx);
    const structure = try getExprPtr(self, struct_idx);
    const hash = hash64(.{ expr.proj_hash, ty_name, proj_idx, structure });
    const num_bvars = numLooseBvars(self, structure);
    const locals = hasFvars(self, structure);
    pushExpr(self, idx, Expr{ .hash = hash, .kind = .{ .proj = .{
        .ty_name = ty_name,
        .idx = proj_idx,
        .structure = structure,
        .num_loose_bvars = num_bvars,
        .has_fvars = locals,
    } } });
}

const FastError = error{ Fallback, ParseFailed };

const Cur = struct {
    s: []const u8,
    i: usize,

    inline fn lit(c: *Cur, comptime l: []const u8) error{Fallback}!void {
        if (c.i + l.len > c.s.len) return error.Fallback;
        if (!std.mem.eql(u8, c.s[c.i..][0..l.len], l)) return error.Fallback;
        c.i += l.len;
    }

    inline fn uint(c: *Cur, comptime T: type) error{Fallback}!T {
        const start = c.i;
        var x: u64 = 0;
        while (c.i < c.s.len) : (c.i += 1) {
            const d = c.s[c.i] -% '0';
            if (d > 9) break;
            x = x * 10 + d;
        }
        if (c.i == start or c.i - start > 19) return error.Fallback;
        return std.math.cast(T, x) orelse error.Fallback;
    }

    fn quoted(c: *Cur) error{Fallback}![]const u8 {
        try c.lit("\"");
        const start = c.i;
        while (c.i < c.s.len) : (c.i += 1) {
            switch (c.s[c.i]) {
                '"' => {
                    const r = c.s[start..c.i];
                    c.i += 1;
                    return r;
                },
                '\\' => return error.Fallback,
                else => {},
            }
        }
        return error.Fallback;
    }

    fn boolean(c: *Cur) error{Fallback}!bool {
        if (c.i < c.s.len and c.s[c.i] == 't') {
            try c.lit("true");
            return true;
        }
        try c.lit("false");
        return false;
    }

    fn u32Array(c: *Cur, ta: std.mem.Allocator) error{Fallback}![]const u32 {
        try c.lit("[");
        if (c.i < c.s.len and c.s[c.i] == ']') {
            c.i += 1;
            return &.{};
        }
        var list = std.ArrayList(u32).empty;
        while (true) {
            list.append(ta, try c.uint(u32)) catch util.oom();
            if (c.i >= c.s.len) return error.Fallback;
            switch (c.s[c.i]) {
                ',' => c.i += 1,
                ']' => {
                    c.i += 1;
                    return list.items;
                },
                else => return error.Fallback,
            }
        }
    }

    fn done(c: *Cur) error{Fallback}!void {
        if (c.i != c.s.len) return error.Fallback;
    }
};

fn fastLine(self: *Parser, ta: std.mem.Allocator, line: []const u8) FastError!void {
    if (line.len < 8) return error.Fallback;
    var c = Cur{ .s = line, .i = 0 };
    switch (line[2]) {
        'i' => switch (line[3]) {
            'e' => {
                try c.lit("{\"ie\":");
                const idx = BackRef{ .kind = .ie, .i = try c.uint(u32) };
                try c.lit(",\"");
                if (c.i + 1 >= line.len) return error.Fallback;
                switch (line[c.i]) {
                    'l' => switch (line[c.i + 1]) {
                        'a' => {
                            try c.lit("lam\":{\"binderInfo\":");
                            const style = binderStyleOf(try c.quoted()) orelse return error.Fallback;
                            try c.lit(",\"body\":");
                            const body = try c.uint(u32);
                            try c.lit(",\"name\":");
                            const binder_name = try c.uint(u32);
                            try c.lit(",\"type\":");
                            const binder_type = try c.uint(u32);
                            try c.lit("}}");
                            try c.done();
                            try doLam(self, idx, binder_name, binder_type, body, style);
                        },
                        'e' => {
                            try c.lit("letE\":{\"body\":");
                            const body = try c.uint(u32);
                            try c.lit(",\"name\":");
                            const binder_name = try c.uint(u32);
                            try c.lit(",\"nondep\":");
                            const nondep = try c.boolean();
                            try c.lit(",\"type\":");
                            const binder_type = try c.uint(u32);
                            try c.lit(",\"value\":");
                            const val = try c.uint(u32);
                            try c.lit("}}");
                            try c.done();
                            try doLet(self, idx, binder_name, binder_type, val, body, nondep);
                        },
                        else => return error.Fallback,
                    },
                    'n' => {
                        try c.lit("natVal\":");
                        const s = try c.quoted();
                        try c.lit("}");
                        try c.done();
                        try doNatVal(self, idx, s);
                    },
                    'p' => {
                        try c.lit("proj\":{\"idx\":");
                        const proj_idx = try c.uint(usize);
                        try c.lit(",\"struct\":");
                        const structure = try c.uint(u32);
                        try c.lit(",\"typeName\":");
                        const ty_name = try c.uint(u32);
                        try c.lit("}}");
                        try c.done();
                        try doProj(self, idx, ty_name, proj_idx, structure);
                    },
                    's' => switch (line[c.i + 1]) {
                        'o' => {
                            try c.lit("sort\":");
                            const lvl = try c.uint(u32);
                            try c.lit("}");
                            try c.done();
                            try doSort(self, idx, lvl);
                        },
                        't' => {
                            try c.lit("strVal\":");
                            const s = try c.quoted();
                            try c.lit("}");
                            try c.done();
                            try doStrVal(self, idx, s);
                        },
                        else => return error.Fallback,
                    },
                    else => return error.Fallback,
                }
            },
            'l' => {
                try c.lit("{\"il\":");
                const idx = BackRef{ .kind = .il, .i = try c.uint(u32) };
                try c.lit(",\"");
                if (c.i >= line.len) return error.Fallback;
                switch (line[c.i]) {
                    'i' => {
                        try c.lit("imax\":[");
                        const l = try c.uint(u32);
                        try c.lit(",");
                        const r = try c.uint(u32);
                        try c.lit("]}");
                        try c.done();
                        try doImax(self, idx, l, r);
                    },
                    'm' => {
                        try c.lit("max\":[");
                        const l = try c.uint(u32);
                        try c.lit(",");
                        const r = try c.uint(u32);
                        try c.lit("]}");
                        try c.done();
                        try doMax(self, idx, l, r);
                    },
                    'p' => {
                        try c.lit("param\":");
                        const n = try c.uint(u32);
                        try c.lit("}");
                        try c.done();
                        try doLevelParam(self, idx, n);
                    },
                    's' => {
                        try c.lit("succ\":");
                        const l = try c.uint(u32);
                        try c.lit("}");
                        try c.done();
                        try doSucc(self, idx, l);
                    },
                    else => return error.Fallback,
                }
            },
            'n' => {
                try c.lit("{\"in\":");
                const idx = BackRef{ .kind = .in_, .i = try c.uint(u32) };
                try c.lit(",\"");
                if (c.i >= line.len) return error.Fallback;
                switch (line[c.i]) {
                    'n' => {
                        try c.lit("num\":{\"i\":");
                        const i = try c.uint(u32);
                        try c.lit(",\"pre\":");
                        const pre = try c.uint(u32);
                        try c.lit("}}");
                        try c.done();
                        try doNum(self, idx, pre, i);
                    },
                    's' => {
                        try c.lit("str\":{\"pre\":");
                        const pre = try c.uint(u32);
                        try c.lit(",\"str\":");
                        const s = try c.quoted();
                        try c.lit("}}");
                        try c.done();
                        try doStr(self, idx, pre, s);
                    },
                    else => return error.Fallback,
                }
            },
            else => return error.Fallback,
        },
        'a' => {
            try c.lit("{\"app\":{\"arg\":");
            const arg = try c.uint(u32);
            try c.lit(",\"fn\":");
            const fun = try c.uint(u32);
            try c.lit("},\"ie\":");
            const idx = BackRef{ .kind = .ie, .i = try c.uint(u32) };
            try c.lit("}");
            try c.done();
            try doApp(self, idx, fun, arg);
        },
        'b' => {
            try c.lit("{\"bvar\":");
            const dbj_idx = try c.uint(u16);
            try c.lit(",\"ie\":");
            const idx = BackRef{ .kind = .ie, .i = try c.uint(u32) };
            try c.lit("}");
            try c.done();
            try doBvar(self, idx, dbj_idx);
        },
        'c' => {
            try c.lit("{\"const\":{\"name\":");
            const cname = try c.uint(u32);
            try c.lit(",\"us\":");
            const us = try c.u32Array(ta);
            try c.lit("},\"ie\":");
            const idx = BackRef{ .kind = .ie, .i = try c.uint(u32) };
            try c.lit("}");
            try c.done();
            try doConst(self, ta, idx, cname, us);
        },
        'f' => {
            try c.lit("{\"forallE\":{\"binderInfo\":");
            const style = binderStyleOf(try c.quoted()) orelse return error.Fallback;
            try c.lit(",\"body\":");
            const body = try c.uint(u32);
            try c.lit(",\"name\":");
            const binder_name = try c.uint(u32);
            try c.lit(",\"type\":");
            const binder_type = try c.uint(u32);
            try c.lit("},\"ie\":");
            const idx = BackRef{ .kind = .ie, .i = try c.uint(u32) };
            try c.lit("}");
            try c.done();
            try doPi(self, idx, binder_name, binder_type, body, style);
        },
        else => return error.Fallback,
    }
}

fn go1(self: *Parser, ta: std.mem.Allocator, line: []const u8) ParseError!void {
    if (fastLine(self, ta, line)) |_| {
        return;
    } else |err| switch (err) {
        error.Fallback => {},
        error.ParseFailed => return error.ParseFailed,
    }

    var jp = Jp{ .s = line, .i = 0, .a = ta };
    const obj = try jp.value();
    switch (obj) {
        .object => {},
        else => return fail("export line is not a JSON object"),
    }

    var assigned_idx: ?BackRef = null;
    var kk: []const u8 = "";
    var kv: JVal = JVal.nul;
    for (obj.object) |m| {
        if (m.key.len == 2 and m.key[0] == 'i') {
            const backref_kind: ?BackRefKind = switch (m.key[1]) {
                'n' => .in_,
                'l' => .il,
                'e' => .ie,
                else => null,
            };
            if (backref_kind) |bk| {
                assigned_idx = BackRef{ .kind = bk, .i = try asU32(m.value) };
                continue;
            }
        }
        kk = m.key;
        kv = m.value;
    }
    const kind = kind_map.get(kk);

    if (kindv(kind, kv, .meta)) |meta_val| {
        const format = meta_val.get("format") orelse return fail("missing format");
        const version = try asStr(format.get("version") orelse return fail("missing format version"));
        try checkSemver(version);
        return;
    }

    if (kindv(kind, kv, .str)) |v| {
        const o = try objAsObject(v);
        try doStr(self, assigned_idx orelse return fail("missing backref index"), try asU32(o.get("pre") orelse return fail("missing pre")), try asStr(o.get("str") orelse return fail("missing str")));
        return;
    }

    if (kindv(kind, kv, .num)) |v| {
        const o = try objAsObject(v);
        try doNum(self, assigned_idx orelse return fail("missing backref index"), try asU32(o.get("pre") orelse return fail("missing pre")), try asU32(o.get("i") orelse return fail("missing i")));
        return;
    }

    if (kindv(kind, kv, .natVal)) |v| {
        return doNatVal(self, assigned_idx orelse return fail("missing backref index"), try asStr(v));
    }

    if (kindv(kind, kv, .strVal)) |v| {
        return doStrVal(self, assigned_idx orelse return fail("missing backref index"), try asStr(v));
    }

    if (kindv(kind, kv, .succ)) |v| {
        try doSucc(self, assigned_idx orelse return fail("missing backref index"), try asU32(v));
        return;
    }

    if (kindv(kind, kv, .max)) |v| {
        const pair = try asU32Array(ta, v);
        if (pair.len != 2) return fail("max expects two level indices");
        try doMax(self, assigned_idx orelse return fail("missing backref index"), pair[0], pair[1]);
        return;
    }

    if (kindv(kind, kv, .imax)) |v| {
        const pair = try asU32Array(ta, v);
        if (pair.len != 2) return fail("imax expects two level indices");
        try doImax(self, assigned_idx orelse return fail("missing backref index"), pair[0], pair[1]);
        return;
    }

    if (kindv(kind, kv, .param)) |v| {
        try doLevelParam(self, assigned_idx orelse return fail("missing backref index"), try asU32(v));
        return;
    }

    if (kindv(kind, kv, .sort)) |v| {
        try doSort(self, assigned_idx orelse return fail("missing backref index"), try asU32(v));
        return;
    }

    if (kindv(kind, kv, .mdata) != null) {
        return fail("Expr.mdata not supported");
    }

    if (kindv(kind, kv, .@"const")) |v| {
        const o = try objAsObject(v);
        try doConst(self, ta, assigned_idx orelse return fail("missing backref index"), try asU32(o.get("name") orelse return fail("missing name")), try asU32Array(ta, o.get("us") orelse return fail("missing us")));
        return;
    }

    if (kindv(kind, kv, .app)) |v| {
        const o = try objAsObject(v);
        try doApp(self, assigned_idx orelse return fail("missing backref index"), try asU32(o.get("fn") orelse return fail("missing fn")), try asU32(o.get("arg") orelse return fail("missing arg")));
        return;
    }

    if (kindv(kind, kv, .bvar)) |v| {
        try doBvar(self, assigned_idx orelse return fail("missing backref index"), try asU16(v));
        return;
    }

    if (kindv(kind, kv, .lam)) |v| {
        const o = try objAsObject(v);
        try doLam(
            self,
            assigned_idx orelse return fail("missing backref index"),
            try asU32(o.get("name") orelse return fail("missing name")),
            try asU32(o.get("type") orelse return fail("missing type")),
            try asU32(o.get("body") orelse return fail("missing body")),
            try parseBinderStyle(o.get("binderInfo") orelse return fail("missing binderInfo")),
        );
        return;
    }

    if (kindv(kind, kv, .forallE)) |v| {
        const o = try objAsObject(v);
        try doPi(
            self,
            assigned_idx orelse return fail("missing backref index"),
            try asU32(o.get("name") orelse return fail("missing name")),
            try asU32(o.get("type") orelse return fail("missing type")),
            try asU32(o.get("body") orelse return fail("missing body")),
            try parseBinderStyle(o.get("binderInfo") orelse return fail("missing binderInfo")),
        );
        return;
    }

    if (kindv(kind, kv, .letE)) |v| {
        const o = try objAsObject(v);
        try doLet(
            self,
            assigned_idx orelse return fail("missing backref index"),
            try asU32(o.get("name") orelse return fail("missing name")),
            try asU32(o.get("type") orelse return fail("missing type")),
            try asU32(o.get("value") orelse return fail("missing value")),
            try asU32(o.get("body") orelse return fail("missing body")),
            try asBool(o.get("nondep") orelse return fail("missing nondep")),
        );
        return;
    }

    if (kindv(kind, kv, .proj)) |v| {
        const o = try objAsObject(v);
        try doProj(
            self,
            assigned_idx orelse return fail("missing backref index"),
            try asU32(o.get("typeName") orelse return fail("missing typeName")),
            try asUsize(o.get("idx") orelse return fail("missing idx")),
            try asU32(o.get("struct") orelse return fail("missing struct")),
        );
        return;
    }

    if (kindv(kind, kv, .axiom)) |v| {
        const o = try objAsObject(v);
        const is_unsafe = try asBool(o.get("isUnsafe") orelse return fail("missing isUnsafe"));
        if (is_unsafe) return fail("unsafe declarations are not supported");
        const aname = try getNamePtr(self, try asU32(o.get("name") orelse return fail("missing name")));
        const uparams = try getUparamsPtr(self, ta, try asU32Array(ta, o.get("levelParams") orelse return fail("missing levelParams")));
        const ty = try getExprPtr(self, try asU32(o.get("type") orelse return fail("missing type")));
        const info = DeclarInfo{ .name = aname, .ty = ty, .uparams = uparams };
        const axiom = Declar{ .axiom = .{ .info = info } };
        if (axiomPermitted(self, aname)) {
            try insertDeclar(self, aname, axiom);
        } else {
            const name_string = nameToString(self, aname);
            if (self.config.unpermitted_axiom_hard_error) {
                util.smp_allocator.free(name_string);
                return fail("export file declares unpermitted axiom");
            } else {
                self.skipped.append(util.smp_allocator, name_string) catch util.oom();
            }
        }
        return;
    }

    if (kindv(kind, kv, .def)) |v| {
        const o = try objAsObject(v);
        const safety = try parseSafety(o.get("safety") orelse return fail("missing safety"));
        if (safety != .safe) return fail("unsafe and partial definitions are not supported");
        const dname = try getNamePtr(self, try asU32(o.get("name") orelse return fail("missing name")));
        const ty = try getExprPtr(self, try asU32(o.get("type") orelse return fail("missing type")));
        const val = try getExprPtr(self, try asU32(o.get("value") orelse return fail("missing value")));
        const uparams = try getUparamsPtr(self, ta, try asU32Array(ta, o.get("levelParams") orelse return fail("missing levelParams")));
        const hint = try parseReducibilityHint(o.get("hints") orelse return fail("missing hints"));
        const info = DeclarInfo{ .name = dname, .ty = ty, .uparams = uparams };
        const definition = Declar{ .definition = .{ .info = info, .val = val, .hint = hint } };
        try insertDeclar(self, dname, definition);
        return;
    }

    if (kindv(kind, kv, .thm)) |v| {
        const o = try objAsObject(v);
        const tname = try getNamePtr(self, try asU32(o.get("name") orelse return fail("missing name")));
        const ty = try getExprPtr(self, try asU32(o.get("type") orelse return fail("missing type")));
        const val = try getExprPtr(self, try asU32(o.get("value") orelse return fail("missing value")));
        const uparams = try getUparamsPtr(self, ta, try asU32Array(ta, o.get("levelParams") orelse return fail("missing levelParams")));
        const info = DeclarInfo{ .name = tname, .ty = ty, .uparams = uparams };
        const theorem = Declar{ .theorem = .{ .info = info, .val = val } };
        try insertDeclar(self, tname, theorem);
        return;
    }

    if (kindv(kind, kv, .@"opaque")) |v| {
        const o = try objAsObject(v);
        const is_unsafe = try asBool(o.get("isUnsafe") orelse return fail("missing isUnsafe"));
        if (is_unsafe) return fail("unsafe declarations are not supported");
        const oname = try getNamePtr(self, try asU32(o.get("name") orelse return fail("missing name")));
        const ty = try getExprPtr(self, try asU32(o.get("type") orelse return fail("missing type")));
        const val = try getExprPtr(self, try asU32(o.get("value") orelse return fail("missing value")));
        const uparams = try getUparamsPtr(self, ta, try asU32Array(ta, o.get("levelParams") orelse return fail("missing levelParams")));
        const info = DeclarInfo{ .name = oname, .ty = ty, .uparams = uparams };
        const definition = Declar{ .opaque_ = .{ .info = info, .val = val } };
        try insertDeclar(self, oname, definition);
        return;
    }

    if (kindv(kind, kv, .quot)) |v| {
        const o = try objAsObject(v);
        const qname = try getNamePtr(self, try asU32(o.get("name") orelse return fail("missing name")));
        const ty = try getExprPtr(self, try asU32(o.get("type") orelse return fail("missing type")));
        const uparams = try getUparamsPtr(self, ta, try asU32Array(ta, o.get("levelParams") orelse return fail("missing levelParams")));
        const info = DeclarInfo{ .name = qname, .ty = ty, .uparams = uparams };
        const quot = Declar{ .quot = .{ .info = info } };
        try insertDeclar(self, qname, quot);
        return;
    }

    if (kindv(kind, kv, .inductive)) |v| {
        const o = try objAsObject(v);
        const ind_vals = try objAsArray(o.get("types") orelse return fail("missing types"));
        const ctor_vals = try objAsArray(o.get("ctors") orelse return fail("missing ctors"));
        const rec_vals = try objAsArray(o.get("recs") orelse return fail("missing recs"));
        const block_start = self.declars.count();
        const block_size = ind_vals.len + ctor_vals.len + rec_vals.len;
        for (ind_vals) |ind_v| {
            const io = try objAsObject(ind_v);
            const is_unsafe = try asBool(io.get("isUnsafe") orelse return fail("missing isUnsafe"));
            if (is_unsafe) return fail("unsafe declarations are not supported");
            const iname = try getNamePtr(self, try asU32(io.get("name") orelse return fail("missing name")));
            self.mutual_block_sizes.put(util.smp_allocator, iname, .{ block_start, block_size }) catch util.oom();
            const uparams = try getUparamsPtr(self, ta, try asU32Array(ta, io.get("levelParams") orelse return fail("missing levelParams")));
            const ty = try getExprPtr(self, try asU32(io.get("type") orelse return fail("missing type")));
            const all_ind_names = self.arena.dupe(NamePtr, try getNames(self, ta, try asU32Array(ta, io.get("all") orelse return fail("missing all"))));
            const all_ctor_names = self.arena.dupe(NamePtr, try getNames(self, ta, try asU32Array(ta, io.get("ctors") orelse return fail("missing ctors"))));
            const is_rec = try asBool(io.get("isRec") orelse return fail("missing isRec"));
            const num_nested = try asU16(io.get("numNested") orelse return fail("missing numNested"));
            const num_params = try asU16(io.get("numParams") orelse return fail("missing numParams"));
            const num_indices = try asU16(io.get("numIndices") orelse return fail("missing numIndices"));
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
            const co = try objAsObject(ctor_v);
            const is_unsafe = try asBool(co.get("isUnsafe") orelse return fail("missing isUnsafe"));
            if (is_unsafe) return fail("unsafe declarations are not supported");
            const cname = try getNamePtr(self, try asU32(co.get("name") orelse return fail("missing name")));
            const ty = try getExprPtr(self, try asU32(co.get("type") orelse return fail("missing type")));
            const uparams = try getUparamsPtr(self, ta, try asU32Array(ta, co.get("levelParams") orelse return fail("missing levelParams")));
            const info = DeclarInfo{ .name = cname, .ty = ty, .uparams = uparams };
            const parent_inductive = try getNamePtr(self, try asU32(co.get("induct") orelse return fail("missing induct")));
            const ctor_idx = try asU16(co.get("cidx") orelse return fail("missing cidx"));
            const num_params = try asU16(co.get("numParams") orelse return fail("missing numParams"));
            const num_fields = try asU16(co.get("numFields") orelse return fail("missing numFields"));
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
            const ro = try objAsObject(rec_v);
            const is_unsafe = try asBool(ro.get("isUnsafe") orelse return fail("missing isUnsafe"));
            if (is_unsafe) return fail("unsafe declarations are not supported");
            const rname = try getNamePtr(self, try asU32(ro.get("name") orelse return fail("missing name")));
            const ty = try getExprPtr(self, try asU32(ro.get("type") orelse return fail("missing type")));
            const uparams = try getUparamsPtr(self, ta, try asU32Array(ta, ro.get("levelParams") orelse return fail("missing levelParams")));
            const info = DeclarInfo{ .name = rname, .ty = ty, .uparams = uparams };
            const rules_arr = try objAsArray(ro.get("rules") orelse return fail("missing rules"));
            var rules = ta.alloc(RecRule, rules_arr.len) catch util.oom();
            for (rules_arr, 0..) |rule_v, i| {
                const rr = try objAsObject(rule_v);
                rules[i] = RecRule{
                    .val = try getExprPtr(self, try asU32(rr.get("rhs") orelse return fail("missing rhs"))),
                    .ctor_name = try getNamePtr(self, try asU32(rr.get("ctor") orelse return fail("missing ctor"))),
                    .ctor_telescope_size_wo_params = try asU16(rr.get("nfields") orelse return fail("missing nfields")),
                };
            }
            const num_params = try asU16(ro.get("numParams") orelse return fail("missing numParams"));
            const num_indices = try asU16(ro.get("numIndices") orelse return fail("missing numIndices"));
            const num_motives = try asU16(ro.get("numMotives") orelse return fail("missing numMotives"));
            const num_minors = try asU16(ro.get("numMinors") orelse return fail("missing numMinors"));
            const k = try asBool(ro.get("k") orelse return fail("missing k"));
            const all_inductives = try getNames(self, ta, try asU32Array(ta, ro.get("all") orelse return fail("missing all")));
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
        return;
    }

    return fail("unrecognized export line kind");
}

fn insertDeclar(self: *Parser, n: NamePtr, d: Declar) ParseError!void {
    if (self.declars.get(n) != null) return fail("duplicate declaration in export file");
    self.declars.put(util.smp_allocator, n, d) catch util.oom();
}

fn objAsObject(v: JVal) ParseError!JVal {
    return switch (v) {
        .object => v,
        else => fail("expected object"),
    };
}

fn objAsArray(v: JVal) ParseError![]const JVal {
    return switch (v) {
        .array => |a| a,
        else => fail("expected array"),
    };
}
