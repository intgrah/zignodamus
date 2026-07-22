const std = @import("std");
const util = @import("../util.zig");
const parser = @import("parser.zig");
const item = @import("item.zig");

const Parser = parser.Parser;
const BackRef = parser.BackRef;

pub const FastError = error{ Fallback, ParseFailed };

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
                            try c.lit("lam\":{\"binderInfo\":");
                            const style = item.binderStyleOf(try c.quoted()) orelse return error.Fallback;
                            try c.lit(",\"body\":");
                            const body = try c.uint(u32);
                            try c.lit(",\"name\":");
                            const binder_name = try c.uint(u32);
                            try c.lit(",\"type\":");
                            const binder_type = try c.uint(u32);
                            try c.lit("}}");
                            try c.done();
                            try item.doLam(self, idx, binder_name, binder_type, body, style);
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
                            try item.doLet(self, idx, binder_name, binder_type, val, body, nondep);
                        },
                        else => return error.Fallback,
                    },
                    'n' => {
                        try c.lit("natVal\":");
                        const s = try c.quoted();
                        try c.lit("}");
                        try c.done();
                        try item.doNatVal(self, idx, s);
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
                        try item.doProj(self, idx, ty_name, proj_idx, structure);
                    },
                    's' => switch (line[c.i + 1]) {
                        'o' => {
                            try c.lit("sort\":");
                            const lvl = try c.uint(u32);
                            try c.lit("}");
                            try c.done();
                            try item.doSort(self, idx, lvl);
                        },
                        't' => {
                            try c.lit("strVal\":");
                            const s = try c.quoted();
                            try c.lit("}");
                            try c.done();
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
                        try c.lit("imax\":[");
                        const l = try c.uint(u32);
                        try c.lit(",");
                        const r = try c.uint(u32);
                        try c.lit("]}");
                        try c.done();
                        try item.doImax(self, idx, l, r);
                    },
                    'm' => {
                        try c.lit("max\":[");
                        const l = try c.uint(u32);
                        try c.lit(",");
                        const r = try c.uint(u32);
                        try c.lit("]}");
                        try c.done();
                        try item.doMax(self, idx, l, r);
                    },
                    'p' => {
                        try c.lit("param\":");
                        const n = try c.uint(u32);
                        try c.lit("}");
                        try c.done();
                        try item.doLevelParam(self, idx, n);
                    },
                    's' => {
                        try c.lit("succ\":");
                        const l = try c.uint(u32);
                        try c.lit("}");
                        try c.done();
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
                        try c.lit("num\":{\"i\":");
                        const i = try c.uint(u32);
                        try c.lit(",\"pre\":");
                        const pre = try c.uint(u32);
                        try c.lit("}}");
                        try c.done();
                        try item.doNum(self, idx, pre, i);
                    },
                    's' => {
                        try c.lit("str\":{\"pre\":");
                        const pre = try c.uint(u32);
                        try c.lit(",\"str\":");
                        const s = try c.quoted();
                        try c.lit("}}");
                        try c.done();
                        try item.doStr(self, idx, pre, s);
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
            try item.doApp(self, idx, fun, arg);
        },
        'b' => {
            try c.lit("{\"bvar\":");
            const dbj_idx = try c.uint(u16);
            try c.lit(",\"ie\":");
            const idx = BackRef{ .kind = .ie, .i = try c.uint(u32) };
            try c.lit("}");
            try c.done();
            try item.doBvar(self, idx, dbj_idx);
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
            try item.doConst(self, ta, idx, cname, us);
        },
        'f' => {
            try c.lit("{\"forallE\":{\"binderInfo\":");
            const style = item.binderStyleOf(try c.quoted()) orelse return error.Fallback;
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
            try item.doPi(self, idx, binder_name, binder_type, body, style);
        },
        else => return error.Fallback,
    }
}
