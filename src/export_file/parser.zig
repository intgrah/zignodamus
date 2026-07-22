const std = @import("std");
const util = @import("../util.zig");
const Arena = @import("../Arena.zig");
const interner = @import("../interner.zig");
const swiss_map = @import("../swiss_map.zig");
const env = @import("../env.zig");
const expr = @import("../expr.zig");
const level = @import("../level.zig");
const name = @import("../name.zig");
const Dag = @import("../Dag.zig");
const Config = @import("../export_file.zig").Config;
const ExportFile = @import("../export_file.zig").ExportFile;
const json = @import("json.zig");
const item = @import("item.zig");
const fast = @import("fast.zig");
const declar = @import("declar.zig");

const NamePtr = @import("../ptr.zig").NamePtr;
const LevelPtr = @import("../ptr.zig").LevelPtr;
const ExprPtr = @import("../ptr.zig").ExprPtr;

const Name = name.Name;
const Level = level.Level;
const BinderStyle = expr.BinderStyle;
const Declar = env.Declar;
const JVal = json.JVal;

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

pub fn fail(msg: []const u8) ParseError {
    std.debug.print("{s}\n", .{msg});
    return error.ParseFailed;
}

pub const BackRefKind = enum { in_, il, ie };

pub const BackRef = struct {
    kind: BackRefKind,
    i: u32,

    pub fn index(self: BackRef) u32 {
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
        try parseLine(&parser, scratch.allocator(), raw_line);
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

fn parseBinderStyle(v: JVal) ParseError!BinderStyle {
    return item.binderStyleOf(try json.asStr(v)) orelse fail("unknown binderInfo");
}

fn parseLine(self: *Parser, ta: std.mem.Allocator, line: []const u8) ParseError!void {
    if (fast.fastLine(self, ta, line)) |_| {
        return;
    } else |err| switch (err) {
        error.Fallback => {},
        error.ParseFailed => return error.ParseFailed,
    }

    var jp = json.Jp{ .s = line, .i = 0, .a = ta };
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
                assigned_idx = BackRef{ .kind = bk, .i = try json.asU32(m.value) };
                continue;
            }
        }
        kk = m.key;
        kv = m.value;
    }
    const kind = kind_map.get(kk);

    if (kindv(kind, kv, .meta)) |meta_val| {
        const format = meta_val.get("format") orelse return fail("missing format");
        const version = try json.asStr(format.get("version") orelse return fail("missing format version"));
        try checkSemver(version);
        return;
    }

    if (kindv(kind, kv, .str)) |v| {
        const o = try json.asObject(v);
        try item.doStr(self, assigned_idx orelse return fail("missing backref index"), try json.asU32(o.get("pre") orelse return fail("missing pre")), try json.asStr(o.get("str") orelse return fail("missing str")));
        return;
    }

    if (kindv(kind, kv, .num)) |v| {
        const o = try json.asObject(v);
        try item.doNum(self, assigned_idx orelse return fail("missing backref index"), try json.asU32(o.get("pre") orelse return fail("missing pre")), try json.asU32(o.get("i") orelse return fail("missing i")));
        return;
    }

    if (kindv(kind, kv, .natVal)) |v| {
        return item.doNatVal(self, assigned_idx orelse return fail("missing backref index"), try json.asStr(v));
    }

    if (kindv(kind, kv, .strVal)) |v| {
        return item.doStrVal(self, assigned_idx orelse return fail("missing backref index"), try json.asStr(v));
    }

    if (kindv(kind, kv, .succ)) |v| {
        try item.doSucc(self, assigned_idx orelse return fail("missing backref index"), try json.asU32(v));
        return;
    }

    if (kindv(kind, kv, .max)) |v| {
        const pair = try json.asU32Array(ta, v);
        if (pair.len != 2) return fail("max expects two level indices");
        try item.doMax(self, assigned_idx orelse return fail("missing backref index"), pair[0], pair[1]);
        return;
    }

    if (kindv(kind, kv, .imax)) |v| {
        const pair = try json.asU32Array(ta, v);
        if (pair.len != 2) return fail("imax expects two level indices");
        try item.doImax(self, assigned_idx orelse return fail("missing backref index"), pair[0], pair[1]);
        return;
    }

    if (kindv(kind, kv, .param)) |v| {
        try item.doLevelParam(self, assigned_idx orelse return fail("missing backref index"), try json.asU32(v));
        return;
    }

    if (kindv(kind, kv, .sort)) |v| {
        try item.doSort(self, assigned_idx orelse return fail("missing backref index"), try json.asU32(v));
        return;
    }

    if (kindv(kind, kv, .mdata) != null) {
        return fail("Expr.mdata not supported");
    }

    if (kindv(kind, kv, .@"const")) |v| {
        const o = try json.asObject(v);
        try item.doConst(self, ta, assigned_idx orelse return fail("missing backref index"), try json.asU32(o.get("name") orelse return fail("missing name")), try json.asU32Array(ta, o.get("us") orelse return fail("missing us")));
        return;
    }

    if (kindv(kind, kv, .app)) |v| {
        const o = try json.asObject(v);
        try item.doApp(self, assigned_idx orelse return fail("missing backref index"), try json.asU32(o.get("fn") orelse return fail("missing fn")), try json.asU32(o.get("arg") orelse return fail("missing arg")));
        return;
    }

    if (kindv(kind, kv, .bvar)) |v| {
        try item.doBvar(self, assigned_idx orelse return fail("missing backref index"), try json.asU16(v));
        return;
    }

    if (kindv(kind, kv, .lam)) |v| {
        const o = try json.asObject(v);
        try item.doLam(
            self,
            assigned_idx orelse return fail("missing backref index"),
            try json.asU32(o.get("name") orelse return fail("missing name")),
            try json.asU32(o.get("type") orelse return fail("missing type")),
            try json.asU32(o.get("body") orelse return fail("missing body")),
            try parseBinderStyle(o.get("binderInfo") orelse return fail("missing binderInfo")),
        );
        return;
    }

    if (kindv(kind, kv, .forallE)) |v| {
        const o = try json.asObject(v);
        try item.doPi(
            self,
            assigned_idx orelse return fail("missing backref index"),
            try json.asU32(o.get("name") orelse return fail("missing name")),
            try json.asU32(o.get("type") orelse return fail("missing type")),
            try json.asU32(o.get("body") orelse return fail("missing body")),
            try parseBinderStyle(o.get("binderInfo") orelse return fail("missing binderInfo")),
        );
        return;
    }

    if (kindv(kind, kv, .letE)) |v| {
        const o = try json.asObject(v);
        try item.doLet(
            self,
            assigned_idx orelse return fail("missing backref index"),
            try json.asU32(o.get("name") orelse return fail("missing name")),
            try json.asU32(o.get("type") orelse return fail("missing type")),
            try json.asU32(o.get("value") orelse return fail("missing value")),
            try json.asU32(o.get("body") orelse return fail("missing body")),
            try json.asBool(o.get("nondep") orelse return fail("missing nondep")),
        );
        return;
    }

    if (kindv(kind, kv, .proj)) |v| {
        const o = try json.asObject(v);
        try item.doProj(
            self,
            assigned_idx orelse return fail("missing backref index"),
            try json.asU32(o.get("typeName") orelse return fail("missing typeName")),
            try json.asUsize(o.get("idx") orelse return fail("missing idx")),
            try json.asU32(o.get("struct") orelse return fail("missing struct")),
        );
        return;
    }

    if (kindv(kind, kv, .axiom)) |v| {
        return declar.parseAxiom(self, ta, v);
    }

    if (kindv(kind, kv, .def)) |v| {
        return declar.parseDef(self, ta, v);
    }

    if (kindv(kind, kv, .thm)) |v| {
        return declar.parseThm(self, ta, v);
    }

    if (kindv(kind, kv, .@"opaque")) |v| {
        return declar.parseOpaque(self, ta, v);
    }

    if (kindv(kind, kv, .quot)) |v| {
        return declar.parseQuot(self, ta, v);
    }

    if (kindv(kind, kv, .inductive)) |v| {
        return declar.parseInductive(self, ta, v);
    }

    return fail("unrecognized export line kind");
}
