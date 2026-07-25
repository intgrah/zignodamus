const std = @import("std");

pub fn assert(cond: bool) void {
    if (!cond) @panic("assertion failed");
}

pub fn oom() noreturn {
    std.debug.print("out of memory\n", .{});
    std.process.exit(3);
}

pub const smp_allocator = std.heap.c_allocator;

pub const map_granule: usize = 2 << 20;

pub const map_align = std.heap.page_size_min;

pub fn mapAnon(len: usize) []align(map_align) u8 {
    return std.posix.mmap(
        null,
        std.mem.alignForward(usize, len, map_granule),
        .{ .READ = true, .WRITE = true },
        .{ .TYPE = .PRIVATE, .ANONYMOUS = true, .NORESERVE = true },
        -1,
        0,
    ) catch oom();
}

pub fn unmapAnon(p: [*]align(map_align) u8, len: usize) void {
    std.posix.munmap(p[0..std.mem.alignForward(usize, len, map_granule)]);
}
