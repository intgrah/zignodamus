const std = @import("std");

pub const FxHasher = struct {
    state: u64 = 0,

    const seed: u64 = 0x51_7c_c1_b7_27_22_0a_95;

    pub inline fn writeU64(self: *FxHasher, chunk: u64) void {
        self.state = (std.math.rotl(u64, self.state, 5) ^ chunk) *% seed;
    }

    pub inline fn finish(self: *const FxHasher) u64 {
        return self.state;
    }
};

fn tagHash(comptime U: type, comptime tag: std.meta.Tag(U)) u64 {
    return std.hash.Fnv1a_64.hash(@typeName(U) ++ "." ++ @tagName(tag));
}

pub inline fn kindHash(kind: anytype) u64 {
    switch (kind) {
        inline else => |payload, tag| {
            var hasher = FxHasher{};
            hasher.writeU64(tagHash(@TypeOf(kind), tag));
            feedPayload(&hasher, payload);
            return hasher.finish();
        },
    }
}

fn feedPayload(hasher: *FxHasher, payload: anytype) void {
    const T = @TypeOf(payload);
    switch (@typeInfo(T)) {
        .void => {},
        .pointer => feedPayload(hasher, payload.*),
        .@"struct" => |s| if (@hasDecl(T, "getHash")) {
            hasher.writeU64(payload.getHash());
        } else inline for (s.fields) |f| {
            if (comptime !isDerived(f.name)) {
                feedPayload(hasher, @field(payload, f.name));
            }
        },
        else => hasher.writeU64(toU64(payload)),
    }
}

fn isDerived(field_name: []const u8) bool {
    return std.mem.eql(u8, field_name, "num_loose_bvars") or
        std.mem.eql(u8, field_name, "has_fvars");
}

pub fn hash64(args: anytype) u64 {
    var hasher = FxHasher{};
    inline for (args) |a| {
        hasher.writeU64(toU64(a));
    }
    return hasher.finish();
}

inline fn toU64(a: anytype) u64 {
    const T = @TypeOf(a);
    return switch (@typeInfo(T)) {
        .int, .comptime_int => @as(u64, @intCast(a)),
        .bool => @intFromBool(a),
        .@"enum" => @as(u64, @intFromEnum(a)),
        else => blk: {
            if (@hasDecl(T, "getHash")) break :blk a.getHash();
            @compileError("toU64: unsupported type " ++ @typeName(T));
        },
    };
}

pub fn FxContext(comptime K: type) type {
    return struct {
        pub inline fn hash(_: @This(), key: K) u64 {
            return fxHashKey(key);
        }
        pub inline fn eql(_: @This(), a: K, b: K) bool {
            return keyEql(a, b);
        }
    };
}

pub fn UniqueContext(comptime K: type) type {
    return struct {
        pub inline fn hash(_: @This(), key: K) u64 {
            return uniqueHashKey(key);
        }
        pub inline fn eql(_: @This(), a: K, b: K) bool {
            return keyEql(a, b);
        }
    };
}

pub fn FxArrayContext(comptime K: type) type {
    return struct {
        pub fn hash(_: @This(), key: K) u32 {
            return @truncate(fxHashKey(key));
        }
        pub fn eql(_: @This(), a: K, b: K, _: usize) bool {
            return keyEql(a, b);
        }
    };
}

fn keyEql(a: anytype, b: @TypeOf(a)) bool {
    const T = @TypeOf(a);
    return switch (@typeInfo(T)) {
        .int, .comptime_int, .bool => a == b,
        .@"enum" => @intFromEnum(a) == @intFromEnum(b),
        .@"struct" => |s| blk: {
            if (@hasDecl(T, "eql")) break :blk a.eql(b);
            if (s.is_tuple) {
                inline for (a, b) |fa, fb| {
                    if (!keyEql(fa, fb)) break :blk false;
                }
                break :blk true;
            }
            inline for (s.fields) |f| {
                if (!keyEql(@field(a, f.name), @field(b, f.name))) break :blk false;
            }
            break :blk true;
        },
        else => @compileError("keyEql: unsupported type " ++ @typeName(T)),
    };
}

inline fn fxHashKey(key: anytype) u64 {
    var hasher = FxHasher{};
    feedKey(&hasher, key);
    return hasher.finish();
}

fn feedKey(hasher: *FxHasher, key: anytype) void {
    const T = @TypeOf(key);
    switch (@typeInfo(T)) {
        .int, .comptime_int, .bool => hasher.writeU64(toU64(key)),
        .@"enum" => hasher.writeU64(@intFromEnum(key)),
        .@"struct" => |s| {
            if (@hasDecl(T, "getHash")) {
                hasher.writeU64(key.getHash());
            } else if (s.is_tuple) {
                inline for (key) |f| feedKey(hasher, f);
            } else {
                inline for (s.fields) |f| feedKey(hasher, @field(key, f.name));
            }
        },
        else => @compileError("feedKey: unsupported type " ++ @typeName(T)),
    }
}

inline fn uniqueHashKey(key: anytype) u64 {
    const T = @TypeOf(key);
    return switch (@typeInfo(T)) {
        .@"enum" => @intFromEnum(key),
        .int, .comptime_int => @as(u64, @intCast(key)),
        else => @compileError("uniqueHashKey: key must be a single u64-like value"),
    };
}
