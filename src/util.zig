const std = @import("std");

pub fn assert(cond: bool) void {
    if (!cond) @panic("assertion failed");
}

pub fn oom() noreturn {
    std.debug.print("out of memory\n", .{});
    std.process.exit(3);
}

pub const smp_allocator = std.heap.c_allocator;
