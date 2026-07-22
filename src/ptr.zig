const expr = @import("expr.zig");
const level = @import("level.zig");
const name = @import("name.zig");
const BigUint = @import("nat.zig").BigUint;

pub const ptr_tag: usize = 1 << 56;

pub fn Ptr(comptime T: type) type {
    return enum(usize) {
        _,

        const Self = @This();

        pub fn global(r: *const T) Self {
            return @enumFromInt(@intFromPtr(r));
        }

        pub fn local(r: *const T) Self {
            return @enumFromInt(@intFromPtr(r) | ptr_tag);
        }

        pub fn isLocal(self: Self) bool {
            return (@intFromEnum(self) & ptr_tag) != 0;
        }

        pub fn asRef(self: Self) *const T {
            return @ptrFromInt(@intFromEnum(self) & ~ptr_tag);
        }

        pub fn getHash(self: Self) u64 {
            return @intFromEnum(self);
        }
    };
}

pub const StringPtr = Ptr([]const u8);
pub const NamePtr = Ptr(name.Name);
pub const LevelPtr = Ptr(level.Level);
pub const ExprPtr = Ptr(expr.Expr);
pub const BigUintPtr = Ptr(BigUint);

pub const LevelsPtr = struct {
    ptr: usize,
    len: usize,

    const Self = @This();

    pub fn global(s: []const LevelPtr) Self {
        return .{ .ptr = @intFromPtr(s.ptr), .len = s.len };
    }

    pub fn local(s: []const LevelPtr) Self {
        return .{ .ptr = @intFromPtr(s.ptr) | ptr_tag, .len = s.len };
    }

    pub fn isLocal(self: Self) bool {
        return (self.ptr & ptr_tag) != 0;
    }

    pub fn asRef(self: Self) []const LevelPtr {
        if (self.len == 0) return &[_]LevelPtr{};
        const p: [*]const LevelPtr = @ptrFromInt(self.ptr & ~ptr_tag);
        return p[0..self.len];
    }

    pub fn getHash(self: Self) u64 {
        return self.ptr;
    }

    pub fn eql(self: Self, o: Self) bool {
        return self.ptr == o.ptr and self.len == o.len;
    }
};
