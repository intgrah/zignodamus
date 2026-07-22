const std = @import("std");

pub fn assert(cond: bool) void {
    if (!cond) @panic("assertion failed");
}

pub fn oom() noreturn {
    std.debug.print("out of memory\n", .{});
    std.process.exit(2);
}

pub const smp_allocator = std.heap.c_allocator;

pub fn OnceCell(comptime T: type) type {
    return struct {
        cell: ?T = null,

        const Self = @This();

        pub const empty: Self = .{};

        pub fn get(self: *const Self) ?T {
            return self.cell;
        }

        pub fn set(self: *Self, x: T) void {
            if (self.cell == null) self.cell = x;
        }
    };
}
