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

/// Interned pointer: Shared(addr) | Local(addr).
/// ## Shared
/// - [64-2] addr 4-byte aligned
/// - [2-1] tag = 0
/// - [1-0] 0, free for lowTagged
/// ## Local
/// - [64-2] addr 4-byte aligned
/// - [2-1] tag = 1
/// - [1-0] 0, free for lowTagged
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
/// - [64-48] num_loose_bvars
/// - [48-3] addr 8-byte aligned
/// - [3-1] holder tag, meaning owned by whoever stores the pointer
/// - [1-0] is_local
/// ## 32-bit
/// - [64-48] num_loose_bvars
/// - [48-35] 0
/// - [35-33] holder tag, meaning owned by whoever stores the pointer
/// - [33-32] is_local
/// - [32-0] addr
pub const ExprPtr = enum(u64) {
    _,

    const Self = @This();
    const addr_mask: u64 = if (is_64) 0x0000_ffff_ffff_fff8 else 0xffff_ffff;
    const local_bit: u64 = if (is_64) 1 << 0 else 1 << 32;
    const tag_shift: u6 = if (is_64) 1 else 33;
    const tag_mask: u64 = @as(u64, 0b11) << tag_shift;
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

    fn pack(r: *const expr.Expr, local_tag: u64) Self {
        const addr = @as(u64, @intFromPtr(r));
        std.debug.assert(addr & ~addr_mask == 0);
        return @enumFromInt(addr | local_tag | derived(r));
    }

    fn derived(r: *const expr.Expr) u64 {
        return switch (r.kind) {
            .string_lit, .nat_lit, .sort, .@"const" => 0,
            .@"var" => |x| (@as(u64, x.dbj_idx) + 1) << bvar_shift,
            .app => |x| bits(@max(x.fun.numLooseBvars(), x.arg.numLooseBvars())),
            .pi => |x| bits(@max(x.binderType().numLooseBvars(), x.body.numLooseBvars() -| 1)),
            .lambda => |x| bits(@max(x.binderType().numLooseBvars(), x.body.numLooseBvars() -| 1)),
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

    pub fn withTag(self: Self, t: u2) Self {
        return @enumFromInt((@intFromEnum(self) & ~tag_mask) | (@as(u64, t) << tag_shift));
    }

    pub fn tag(self: Self) u2 {
        return @truncate(@intFromEnum(self) >> tag_shift);
    }

    pub fn untag(self: Self) Self {
        return @enumFromInt(@intFromEnum(self) & ~tag_mask);
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

/// ## 64-bit
/// - [64-48] len
/// - [48-2] addr 4-byte aligned, 0 when len is 0
/// - [2-1] is_local
/// - [1-0] 0
/// ## 32-bit
/// - [64-48] len
/// - [48-33] 0
/// - [33-32] is_local
/// - [32-0] addr, 0 when len is 0
pub const LevelsPtr = enum(u64) {
    _,

    const Self = @This();
    const addr_mask: u64 = if (is_64) 0x0000_ffff_ffff_fffc else 0xffff_ffff;
    const local_bit: u64 = if (is_64) ptr_tag else 1 << 32;
    const len_shift: u6 = 48;

    comptime {
        std.debug.assert(@alignOf(LevelPtr) >= 4);
    }

    pub fn global(s: []const LevelPtr) Self {
        return pack(s, 0);
    }

    pub fn local(s: []const LevelPtr) Self {
        return pack(s, local_bit);
    }

    fn pack(s: []const LevelPtr, local_tag: u64) Self {
        if (s.len == 0) return @enumFromInt(local_tag);
        const addr = @as(u64, @intFromPtr(s.ptr));
        std.debug.assert(addr & ~addr_mask == 0);
        std.debug.assert(s.len <= std.math.maxInt(u16));
        return @enumFromInt(addr | local_tag | (@as(u64, s.len) << len_shift));
    }

    pub fn isLocal(self: Self) bool {
        return (@intFromEnum(self) & local_bit) != 0;
    }

    pub fn len(self: Self) usize {
        return @as(u16, @truncate(@intFromEnum(self) >> len_shift));
    }

    pub fn asRef(self: Self) []const LevelPtr {
        const n = self.len();
        if (n == 0) return &[_]LevelPtr{};
        const p: [*]const LevelPtr = @ptrFromInt(@as(usize, @intCast(@intFromEnum(self) & addr_mask)));
        return p[0..n];
    }

    pub fn getHash(self: Self) u64 {
        return @intFromEnum(self);
    }

    pub fn eql(self: Self, o: Self) bool {
        return self == o;
    }
};
