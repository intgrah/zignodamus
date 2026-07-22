const std = @import("std");
const util = @import("../util.zig");
const parser = @import("parser.zig");
const ParseError = parser.ParseError;
const fail = parser.fail;

pub const Member = struct { key: []const u8, value: JVal };

pub const JVal = union(enum) {
    object: []const Member,
    array: []const JVal,
    string: []const u8,
    number: []const u8,
    boolean: bool,
    nul: void,

    pub fn get(self: JVal, key: []const u8) ?JVal {
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

fn parseUint(comptime T: type, s: []const u8) ParseError!T {
    if (s.len == 0 or s.len > 19) return fail("expected integer");
    var x: u64 = 0;
    for (s) |c| {
        if (c < '0' or c > '9') return fail("expected integer");
        x = x * 10 + (c - '0');
    }
    return std.math.cast(T, x) orelse fail("integer out of range");
}

pub fn asU32(v: JVal) ParseError!u32 {
    return switch (v) {
        .number => |s| parseUint(u32, s),
        else => fail("expected integer"),
    };
}

pub fn asU16(v: JVal) ParseError!u16 {
    return switch (v) {
        .number => |s| parseUint(u16, s),
        else => fail("expected integer"),
    };
}

pub fn asUsize(v: JVal) ParseError!usize {
    return switch (v) {
        .number => |s| parseUint(usize, s),
        else => fail("expected integer"),
    };
}

pub fn asBool(v: JVal) ParseError!bool {
    return switch (v) {
        .boolean => |b| b,
        else => fail("expected bool"),
    };
}

pub fn asStr(v: JVal) ParseError![]const u8 {
    return switch (v) {
        .string => |s| s,
        else => fail("expected string"),
    };
}

pub fn asU32Array(ta: std.mem.Allocator, v: JVal) ParseError![]const u32 {
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

pub fn asObject(v: JVal) ParseError!JVal {
    return switch (v) {
        .object => v,
        else => fail("expected object"),
    };
}

pub fn asArray(v: JVal) ParseError![]const JVal {
    return switch (v) {
        .array => |a| a,
        else => fail("expected array"),
    };
}

pub const Jp = struct {
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

    pub fn value(self: *Jp) ParseError!JVal {
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
