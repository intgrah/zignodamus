const std = @import("std");
const util = @import("util.zig");

pub fn IndexArray(comptime T: type) type {
    return struct {
        items: [*]T,
        cap: usize,
        len: usize,

        const Self = @This();
        const min_cap: usize = util.map_granule / @sizeOf(T);
        pub const zero: T = std.mem.zeroes(T);

        fn map(cap: usize) [*]T {
            return @ptrCast(@alignCast(util.mapAnon(cap * @sizeOf(T)).ptr));
        }

        fn unmap(items: [*]T, cap: usize) void {
            util.unmapAnon(@ptrCast(@alignCast(items)), cap * @sizeOf(T));
        }

        pub fn init(reserve: usize) Self {
            const cap = @max(reserve, min_cap);
            return .{ .items = map(cap), .cap = cap, .len = 0 };
        }

        pub fn deinit(self: *Self) void {
            unmap(self.items, self.cap);
            self.* = undefined;
        }

        pub inline fn at(self: *const Self, i: usize) T {
            if (i >= self.cap) return zero;
            return self.items[i];
        }

        pub inline fn set(self: *Self, i: usize, v: T) void {
            if (i >= self.cap) self.growTo(i + 1);
            self.items[i] = v;
            if (i >= self.len) self.len = i + 1;
        }

        pub fn slice(self: *const Self) []T {
            return self.items[0..self.len];
        }

        noinline fn growTo(self: *Self, need: usize) void {
            var cap = self.cap;
            while (cap < need) cap *= 2;
            const buf = util.remapAnon(
                @ptrCast(@alignCast(self.items)),
                self.cap * @sizeOf(T),
                cap * @sizeOf(T),
            );
            self.items = @ptrCast(@alignCast(buf.ptr));
            self.cap = cap;
        }
    };
}
