const std = @import("std");
const expr = @import("expr.zig");
const level = @import("level.zig");
const name = @import("name.zig");
const BigUint = @import("nat.zig").BigUint;

const is_64 = switch (@bitSizeOf(usize)) {
    64 => true,
    32 => false,
    else => @compileError("pointer tagging requires a 32-bit or 64-bit target"),
};

pub const ptr_tag: usize = 1 << 1;

pub fn Ptr(comptime T: type) type {
    return enum(usize) {
        _,

        const Self = @This();

        comptime {
            std.debug.assert(@alignOf(T) >= 4);
        }

        pub const nil: Self = @enumFromInt(0);

        pub fn lowTagged(self: Self) usize {
            comptime std.debug.assert(@alignOf(T) >= 2 and ptr_tag & 1 == 0);
            return @intFromEnum(self) | 1;
        }

        pub fn fromLowTagged(v: usize) Self {
            return @enumFromInt(v & ~@as(usize, 1));
        }

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
pub const BigUintPtr = Ptr(BigUint);

/// ## 64-bit
/// - 16 bit num_loose_bvars
/// - 45 bit address
/// - 2 bits unused
/// - 1 bit is_local
/// Assumption: 8-byte alignment means lower 3 bits are free
///
/// ## 32-bit
/// - 16 bit num_loose_bvars
/// - 15 bits unused
/// - 1 bit is_local
/// - 32 bit address
pub const ExprPtr = enum(u64) {
    _,

    const Self = @This();
    const addr_mask: u64 = if (is_64) 0x0000_ffff_ffff_fff8 else 0xffff_ffff;
    const local_bit: u64 = if (is_64) 1 << 0 else 1 << 32;
    const bvar_shift: u6 = 48;

    comptime {
        if (is_64) std.debug.assert(@alignOf(expr.Expr) >= 8);
    }

    pub const nil: Self = @enumFromInt(0);

    pub fn global(r: *const expr.Expr) Self {
        return pack(r, 0);
    }

    pub fn local(r: *const expr.Expr) Self {
        return pack(r, local_bit);
    }

    fn pack(r: *const expr.Expr, tag: u64) Self {
        const addr = @as(u64, @intFromPtr(r));
        std.debug.assert(addr & ~addr_mask == 0);
        return @enumFromInt(addr | tag | derived(r));
    }

    fn derived(r: *const expr.Expr) u64 {
        return switch (r.kind) {
            .string_lit, .nat_lit, .sort, .@"const" => 0,
            .@"var" => |x| (@as(u64, x.dbj_idx) + 1) << bvar_shift,
            .app => |x| bits(@max(x.fun.numLooseBvars(), x.arg.numLooseBvars())),
            .pi => |x| bits(@max(x.binder_type.numLooseBvars(), x.body.numLooseBvars() -| 1)),
            .lambda => |x| bits(@max(x.binder_type.numLooseBvars(), x.body.numLooseBvars() -| 1)),
            .let => |x| bits(@max(
                x.data.binder_type.numLooseBvars(),
                @max(x.data.val.numLooseBvars(), x.data.body.numLooseBvars() -| 1),
            )),
            .proj => |x| bits(x.structure.numLooseBvars()),
        };
    }

    fn bits(num_loose_bvars: u16) u64 {
        return @as(u64, num_loose_bvars) << bvar_shift;
    }

    pub fn isLocal(self: Self) bool {
        return (@intFromEnum(self) & local_bit) != 0;
    }

    pub fn numLooseBvars(self: Self) u16 {
        return @truncate(@intFromEnum(self) >> bvar_shift);
    }

    pub fn asRef(self: Self) *const expr.Expr {
        return @ptrFromInt(@as(usize, @intCast(@intFromEnum(self) & addr_mask)));
    }

    pub fn getHash(self: Self) u64 {
        return @intFromEnum(self);
    }
};

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
