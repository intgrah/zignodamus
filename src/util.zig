const std = @import("std");

pub fn assert(cond: bool) void {
    if (!cond) @panic("assertion failed");
}

pub fn oom() noreturn {
    std.debug.print("out of memory\n", .{});
    std.process.exit(3);
}

pub const smp_allocator = std.heap.c_allocator;

pub var bmi2: bool = false;

pub fn detectCpuFeatures() void {
    if (@import("builtin").cpu.arch != .x86_64) return;
    var eax: u32 = undefined;
    var ebx: u32 = undefined;
    var ecx: u32 = undefined;
    var edx: u32 = undefined;
    asm volatile ("cpuid"
        : [_] "={eax}" (eax),
          [_] "={ebx}" (ebx),
          [_] "={ecx}" (ecx),
          [_] "={edx}" (edx),
        : [_] "{eax}" (@as(u32, 7)),
          [_] "{ecx}" (@as(u32, 0)),
    );
    bmi2 = (ebx >> 8) & 1 != 0;
}

inline fn pext(a: u64, m: u64) u64 {
    return asm ("pextq %[m], %[a], %[r]"
        : [r] "=r" (-> u64),
        : [a] "r" (a),
          [m] "r" (m),
    );
}

pub inline fn selectRanks(sub: u64, sup: u64) u64 {
    if (@import("builtin").cpu.arch == .x86_64 and bmi2) return pext(sub, sup);
    var out: u64 = 0;
    var f = sup;
    var rank: u6 = 0;
    while (f != 0) {
        const j: u6 = @intCast(@ctz(f));
        f &= f - 1;
        if ((sub >> j) & 1 != 0) out |= @as(u64, 1) << rank;
        rank +%= 1;
    }
    return out;
}

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

pub fn remapAnon(p: [*]align(map_align) u8, old_len: usize, new_len: usize) []align(map_align) u8 {
    return std.posix.mremap(
        p,
        std.mem.alignForward(usize, old_len, map_granule),
        std.mem.alignForward(usize, new_len, map_granule),
        .{ .MAYMOVE = true },
        null,
    ) catch oom();
}
