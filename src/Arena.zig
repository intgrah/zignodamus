const util = @import("util.zig");
const std = @import("std");

child: std.mem.Allocator,
slabs: std.ArrayList([]u8),
ptr: [*]u8,
end: [*]u8,
next_slab_size: usize,

const Arena = @This();

const initial_slab_size: usize = 1 << 16;
const max_slab_size: usize = 1 << 20;

pub fn init(child: std.mem.Allocator) Arena {
    const sentinel: [*]u8 = @ptrFromInt(@alignOf(usize));
    return .{
        .child = child,
        .slabs = .empty,
        .ptr = sentinel,
        .end = sentinel,
        .next_slab_size = initial_slab_size,
    };
}

pub fn deinit(self: *Arena) void {
    for (self.slabs.items) |slab| {
        self.child.free(@as([]align(@alignOf(usize)) u8, @alignCast(slab)));
    }
    self.slabs.deinit(self.child);
    self.* = undefined;
}

fn grow(self: *Arena, min: usize) void {
    var size = self.next_slab_size;
    while (size < min) size *= 2;
    const slab = self.child.alignedAlloc(u8, .of(usize), size) catch util.oom();
    self.slabs.append(self.child, slab) catch util.oom();
    self.ptr = slab.ptr;
    self.end = slab.ptr + slab.len;
    self.next_slab_size = @min(size * 2, max_slab_size);
}

inline fn bump(self: *Arena, size: usize, alignment: usize) [*]u8 {
    const addr = @intFromPtr(self.ptr);
    const aligned = std.mem.alignForward(usize, addr, alignment);
    const new_ptr: [*]u8 = @ptrFromInt(aligned);
    const after = new_ptr + size;
    if (@intFromPtr(after) > @intFromPtr(self.end)) {
        return self.bumpSlow(size, alignment);
    }
    self.ptr = after;
    return new_ptr;
}

fn bumpSlow(self: *Arena, size: usize, alignment: usize) [*]u8 {
    self.grow(size + alignment);
    const addr = @intFromPtr(self.ptr);
    const aligned = std.mem.alignForward(usize, addr, alignment);
    const new_ptr: [*]u8 = @ptrFromInt(aligned);
    self.ptr = new_ptr + size;
    return new_ptr;
}

pub fn backingAllocator(self: *Arena) std.mem.Allocator {
    return self.child;
}

pub fn bumpAllocator(self: *Arena) std.mem.Allocator {
    return .{ .ptr = self, .vtable = &bump_vtable };
}

const bump_vtable = std.mem.Allocator.VTable{
    .alloc = bumpAlloc,
    .resize = bumpResize,
    .remap = bumpRemap,
    .free = bumpFree,
};

fn bumpAlloc(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
    _ = ret_addr;
    const self: *Arena = @ptrCast(@alignCast(ctx));
    return self.bump(len, alignment.toByteUnits());
}

fn bumpResize(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
    _ = ctx;
    _ = alignment;
    _ = ret_addr;
    return new_len <= memory.len;
}

fn bumpRemap(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
    _ = ctx;
    _ = alignment;
    _ = ret_addr;
    return if (new_len <= memory.len) memory.ptr else null;
}

fn bumpFree(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
    _ = ctx;
    _ = memory;
    _ = alignment;
    _ = ret_addr;
}

pub inline fn create(self: *Arena, comptime T: type) *T {
    const raw = self.bump(@sizeOf(T), @alignOf(T));
    return @ptrCast(@alignCast(raw));
}

pub fn alloc(self: *Arena, comptime T: type, value: T) *T {
    const r = self.create(T);
    r.* = value;
    return r;
}

pub fn allocSlice(self: *Arena, comptime T: type, n: usize) []T {
    if (n == 0) return &[_]T{};
    const raw = self.bump(@sizeOf(T) * n, @alignOf(T));
    const many: [*]T = @ptrCast(@alignCast(raw));
    return many[0..n];
}

pub fn dupe(self: *Arena, comptime T: type, src: []const T) []T {
    const dst = self.allocSlice(T, src.len);
    @memcpy(dst, src);
    return dst;
}
