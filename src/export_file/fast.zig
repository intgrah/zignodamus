const std = @import("std");
const util = @import("../util.zig");
const env = @import("../env.zig");
const expr = @import("../expr.zig");
const parser = @import("parser.zig");
const item = @import("item.zig");
const declar = @import("declar.zig");

const Parser = parser.Parser;
const BackRef = parser.BackRef;
const BinderStyle = expr.BinderStyle;
const ReducibilityHint = env.ReducibilityHint;

pub const FastError = error{ Fallback, ParseFailed, Declined };

fn NonVoid(comptime types: anytype) []const type {
    comptime var out: []const type = &.{};
    inline for (types) |T| {
        if (T != void) out = out ++ &[_]type{T};
    }
    return out;
}

fn Match(comptime types: anytype) type {
    const nv = NonVoid(types);
    return if (nv.len == 1) nv[0] else std.meta.Tuple(nv);
}

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

    fn skipU32Array(c: *Cur) error{Fallback}!void {
        try c.lit("[");
        if (c.i < c.s.len and c.s[c.i] == ']') {
            c.i += 1;
            return;
        }
        while (true) {
            _ = try c.uint(u32);
            if (c.i >= c.s.len) return error.Fallback;
            switch (c.s[c.i]) {
                ',' => c.i += 1,
                ']' => {
                    c.i += 1;
                    return;
                },
                else => return error.Fallback,
            }
        }
    }

    fn hint(c: *Cur) error{Fallback}!ReducibilityHint {
        if (c.i < c.s.len and c.s[c.i] == '{') {
            try c.lit("{\"regular\":");
            const depth = try c.uint(u16);
            try c.lit("}");
            return ReducibilityHint{ .regular = depth };
        }
        const s = try c.quoted();
        if (std.mem.eql(u8, s, "abbrev")) return .abbrev;
        if (std.mem.eql(u8, s, "opaque")) return .opaque_;
        return error.Fallback;
    }

    inline fn field(c: *Cur, comptime T: type, ta: std.mem.Allocator) error{Fallback}!T {
        return switch (T) {
            u16, u32, usize => c.uint(T),
            bool => c.boolean(),
            []const u8 => c.quoted(),
            []const u32 => c.u32Array(ta),
            BinderStyle => item.binderStyleOf(try c.quoted()) orelse error.Fallback,
            ReducibilityHint => c.hint(),
            else => @compileError("unsupported match field type " ++ @typeName(T)),
        };
    }

    fn done(c: *Cur) error{Fallback}!void {
        if (c.i != c.s.len) return error.Fallback;
    }

    fn match(c: *Cur, ta: std.mem.Allocator, comptime pattern: []const u8, comptime types: anytype) error{Fallback}!Match(types) {
        const nv = comptime NonVoid(types);
        var result: std.meta.Tuple(nv) = undefined;
        comptime var lit_start = 0;
        comptime var ti = 0;
        comptime var ri = 0;
        inline for (pattern, 0..) |ch, i| {
            if (comptime ch == '$') {
                try c.lit(pattern[lit_start..i]);
                if (types[ti] == void) {
                    try c.skipU32Array();
                } else {
                    result[ri] = try c.field(types[ti], ta);
                    ri += 1;
                }
                ti += 1;
                lit_start = i + 1;
            }
        }
        try c.lit(pattern[lit_start..]);
        try c.done();
        return if (comptime nv.len == 1) result[0] else result;
    }
};

pub fn fastLine(self: *Parser, ta: std.mem.Allocator, line: []const u8) FastError!void {
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
                            const style, const body, const binder_name, const binder_type = try c.match(ta,
                                \\lam":{"binderInfo":$,"body":$,"name":$,"type":$}}
                            , .{ BinderStyle, u32, u32, u32 });
                            try item.doLam(self, idx, binder_name, binder_type, body, style);
                        },
                        'e' => {
                            const body, const binder_name, const nondep, const binder_type, const val = try c.match(ta,
                                \\letE":{"body":$,"name":$,"nondep":$,"type":$,"value":$}}
                            , .{ u32, u32, bool, u32, u32 });
                            try item.doLet(self, idx, binder_name, binder_type, val, body, nondep);
                        },
                        else => return error.Fallback,
                    },
                    'n' => {
                        const s = try c.match(ta,
                            \\natVal":$}
                        , .{[]const u8});
                        try item.doNatVal(self, idx, s);
                    },
                    'p' => {
                        const proj_idx, const structure, const ty_name = try c.match(ta,
                            \\proj":{"idx":$,"struct":$,"typeName":$}}
                        , .{ usize, u32, u32 });
                        try item.doProj(self, idx, ty_name, proj_idx, structure);
                    },
                    's' => switch (line[c.i + 1]) {
                        'o' => {
                            const lvl = try c.match(ta,
                                \\sort":$}
                            , .{u32});
                            try item.doSort(self, idx, lvl);
                        },
                        't' => {
                            const s = try c.match(ta,
                                \\strVal":$}
                            , .{[]const u8});
                            try item.doStrVal(self, idx, s);
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
                        const l, const r = try c.match(ta,
                            \\imax":[$,$]}
                        , .{ u32, u32 });
                        try item.doImax(self, idx, l, r);
                    },
                    'm' => {
                        const l, const r = try c.match(ta,
                            \\max":[$,$]}
                        , .{ u32, u32 });
                        try item.doMax(self, idx, l, r);
                    },
                    'p' => {
                        const n = try c.match(ta,
                            \\param":$}
                        , .{u32});
                        try item.doLevelParam(self, idx, n);
                    },
                    's' => {
                        const l = try c.match(ta,
                            \\succ":$}
                        , .{u32});
                        try item.doSucc(self, idx, l);
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
                        const i, const pre = try c.match(ta,
                            \\num":{"i":$,"pre":$}}
                        , .{ u32, u32 });
                        try item.doNum(self, idx, pre, i);
                    },
                    's' => {
                        const pre, const s = try c.match(ta,
                            \\str":{"pre":$,"str":$}}
                        , .{ u32, []const u8 });
                        try item.doStr(self, idx, pre, s);
                    },
                    else => return error.Fallback,
                }
            },
            else => return error.Fallback,
        },
        'a' => {
            const arg, const fun, const idx = try c.match(ta,
                \\{"app":{"arg":$,"fn":$},"ie":$}
            , .{ u32, u32, u32 });
            try item.doApp(self, BackRef{ .kind = .ie, .i = idx }, fun, arg);
        },
        'b' => {
            const dbj_idx, const idx = try c.match(ta,
                \\{"bvar":$,"ie":$}
            , .{ u16, u32 });
            try item.doBvar(self, BackRef{ .kind = .ie, .i = idx }, dbj_idx);
        },
        'c' => {
            const cname, const us, const idx = try c.match(ta,
                \\{"const":{"name":$,"us":$},"ie":$}
            , .{ u32, []const u32, u32 });
            try item.doConst(self, ta, BackRef{ .kind = .ie, .i = idx }, cname, us);
        },
        'd' => {
            const h, const uparam_idxs, const name_idx, const ty_idx, const val_idx = try c.match(ta,
                \\{"def":{"all":$,"hints":$,"levelParams":$,"name":$,"safety":"safe","type":$,"value":$}}
            , .{ void, ReducibilityHint, []const u32, u32, u32, u32 });
            try declar.doDef(self, ta, name_idx, ty_idx, val_idx, uparam_idxs, h);
        },
        'f' => {
            const style, const body, const binder_name, const binder_type, const idx = try c.match(ta,
                \\{"forallE":{"binderInfo":$,"body":$,"name":$,"type":$},"ie":$}
            , .{ BinderStyle, u32, u32, u32, u32 });
            try item.doPi(self, BackRef{ .kind = .ie, .i = idx }, binder_name, binder_type, body, style);
        },
        't' => {
            const uparam_idxs, const name_idx, const ty_idx, const val_idx = try c.match(ta,
                \\{"thm":{"all":$,"levelParams":$,"name":$,"type":$,"value":$}}
            , .{ void, []const u32, u32, u32, u32 });
            try declar.doThm(self, ta, name_idx, ty_idx, val_idx, uparam_idxs);
        },
        else => return error.Fallback,
    }
}
