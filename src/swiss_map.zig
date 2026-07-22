const util = @import("util.zig");
const std = @import("std");
const hash = @import("hash.zig");

pub fn SwissMap(comptime K: type, comptime Val: type, comptime Ctx: type) type {
    return struct {
        ctrl: [*]u8 = dummy_ctrl[0..].ptr,
        slots: [*]Slot = undefined,
        cap: usize = 0,
        count: usize = 0,
        growth_left: usize = 0,

        const Self = @This();
        pub const Slot = struct { key: K, value: Val };
        const Group = @Vector(16, u8);
        const ctrl_empty: u8 = 0x80;
        var dummy_ctrl: [16]u8 = .{ctrl_empty} ** 16;
        pub const empty: Self = .{};

        inline fn h2(h: u64) u8 {
            return @as(u8, @truncate(h >> 57)) & 0x7f;
        }

        inline fn mix(h: u64) u64 {
            return h *% 0x9E3779B97F4A7C15;
        }

        fn maxLoad(c: usize) usize {
            return c - (c >> 3);
        }

        inline fn loadGroup(self: *const Self, pos: usize) Group {
            return @as(*align(1) const Group, @ptrCast(self.ctrl + pos)).*;
        }

        inline fn matchByte(g: Group, b: u8) u16 {
            const m: @Vector(16, bool) = g == @as(Group, @splat(b));
            return @as(u16, @bitCast(m));
        }

        fn setCtrl(self: *Self, i: usize, v: u8) void {
            self.ctrl[i] = v;
            if (i < 16) self.ctrl[self.cap + i] = v;
        }

        fn slotOff(c: usize) usize {
            return std.mem.alignForward(usize, c + 16, @alignOf(Slot));
        }
        fn bufLen(c: usize) usize {
            return slotOff(c) + c * @sizeOf(Slot);
        }

        pub fn deinit(self: *Self, a: std.mem.Allocator) void {
            if (self.cap != 0) {
                a.free(@as([*]align(@alignOf(Slot)) u8, @alignCast(self.ctrl))[0..bufLen(self.cap)]);
            }
            self.* = .{};
        }

        inline fn setEmpty(ptr: [*]u8, n: usize) void {
            const e: Group = @splat(ctrl_empty);
            var i: usize = 0;
            while (i + 16 <= n) : (i += 16) {
                @as(*align(1) Group, @ptrCast(ptr + i)).* = e;
            }
            while (i < n) : (i += 1) ptr[i] = ctrl_empty;
        }

        pub fn clearRetainingCapacity(self: *Self) void {
            if (self.count == 0) return;
            setEmpty(self.ctrl, self.cap + 16);
            self.count = 0;
            self.growth_left = maxLoad(self.cap);
        }

        noinline fn allocCap(self: *Self, a: std.mem.Allocator, newcap: usize) void {
            const buf = a.alignedAlloc(u8, .of(Slot), bufLen(newcap)) catch util.oom();
            setEmpty(buf.ptr, newcap + 16);
            const old_ctrl = self.ctrl;
            const old_slots = self.slots;
            const old_cap = self.cap;
            self.ctrl = buf.ptr;
            self.slots = @ptrCast(@alignCast(buf.ptr + slotOff(newcap)));
            self.cap = newcap;
            self.count = 0;
            self.growth_left = maxLoad(newcap);
            var i: usize = 0;
            while (i < old_cap) : (i += 1) {
                if (old_ctrl[i] & 0x80 == 0) {
                    self.insertNew(old_slots[i].key, old_slots[i].value);
                }
            }
            if (old_cap != 0) {
                a.free(@as([*]align(@alignOf(Slot)) u8, @alignCast(old_ctrl))[0..bufLen(old_cap)]);
            }
        }

        fn insertNew(self: *Self, key: K, val: Val) void {
            const h = mix(Ctx.hash(.{}, key));
            const f = h2(h);
            const mask = self.cap - 1;
            var pos = h & mask;
            var stride: usize = 16;
            while (true) {
                const g = self.loadGroup(pos);
                const empties = matchByte(g, ctrl_empty);
                if (empties != 0) {
                    const i = (pos + @ctz(empties)) & mask;
                    self.setCtrl(i, f);
                    self.slots[i] = .{ .key = key, .value = val };
                    self.count += 1;
                    self.growth_left -= 1;
                    return;
                }
                pos = (pos + stride) & mask;
                stride += 16;
            }
        }

        inline fn find(self: *const Self, key: K) ?usize {
            if (self.cap == 0) return null;
            const h = mix(Ctx.hash(.{}, key));
            const f = h2(h);
            const mask = self.cap - 1;
            var pos = h & mask;
            var stride: usize = 16;
            while (true) {
                const g = self.loadGroup(pos);
                var m = matchByte(g, f);
                while (m != 0) {
                    const i = (pos + @ctz(m)) & mask;
                    if (Ctx.eql(.{}, self.slots[i].key, key)) return i;
                    m &= m - 1;
                }
                if (matchByte(g, ctrl_empty) != 0) return null;
                pos = (pos + stride) & mask;
                stride += 16;
            }
        }

        pub inline fn get(self: *const Self, key: K) ?Val {
            if (self.find(key)) |i| return self.slots[i].value;
            return null;
        }

        pub inline fn getPtr(self: *const Self, key: K) ?*Val {
            if (self.find(key)) |i| return &self.slots[i].value;
            return null;
        }

        pub fn contains(self: *const Self, key: K) bool {
            return self.find(key) != null;
        }

        pub const GetOrPutResult = struct { found_existing: bool, key_ptr: *K, value_ptr: *Val };

        fn maybeGrow(self: *Self, a: std.mem.Allocator) void {
            if (self.growth_left == 0) {
                self.allocCap(a, if (self.cap == 0) 16 else self.cap * 2);
            }
        }

        pub inline fn getOrPut(self: *Self, a: std.mem.Allocator, key: K) !GetOrPutResult {
            self.maybeGrow(a);
            const h = mix(Ctx.hash(.{}, key));
            const f = h2(h);
            const mask = self.cap - 1;
            var pos = h & mask;
            var stride: usize = 16;
            while (true) {
                const g = self.loadGroup(pos);
                var m = matchByte(g, f);
                while (m != 0) {
                    const i = (pos + @ctz(m)) & mask;
                    if (Ctx.eql(.{}, self.slots[i].key, key)) {
                        return .{ .found_existing = true, .key_ptr = &self.slots[i].key, .value_ptr = &self.slots[i].value };
                    }
                    m &= m - 1;
                }
                const empties = matchByte(g, ctrl_empty);
                if (empties != 0) {
                    const i = (pos + @ctz(empties)) & mask;
                    self.setCtrl(i, f);
                    self.slots[i].key = key;
                    self.count += 1;
                    self.growth_left -= 1;
                    return .{ .found_existing = false, .key_ptr = &self.slots[i].key, .value_ptr = &self.slots[i].value };
                }
                pos = (pos + stride) & mask;
                stride += 16;
            }
        }

        pub fn put(self: *Self, a: std.mem.Allocator, key: K, val: Val) !void {
            const gop = try self.getOrPut(a, key);
            gop.value_ptr.* = val;
        }

        pub fn fetchPut(self: *Self, a: std.mem.Allocator, key: K, val: Val) !?Val {
            const gop = try self.getOrPut(a, key);
            if (gop.found_existing) {
                const old = gop.value_ptr.*;
                gop.value_ptr.* = val;
                return old;
            }
            gop.value_ptr.* = val;
            return null;
        }

        pub fn ensureTotalCapacity(self: *Self, a: std.mem.Allocator, n: usize) !void {
            if (n <= maxLoad(self.cap)) return;
            var newcap: usize = 16;
            while (maxLoad(newcap) < n) newcap *= 2;
            self.allocCap(a, newcap);
        }

        pub const KV = struct { key_ptr: *K, value_ptr: *Val };
        pub const Iterator = struct {
            m: *Self,
            i: usize,
            pub fn next(self: *Iterator) ?KV {
                while (self.i < self.m.cap) {
                    const j = self.i;
                    self.i += 1;
                    if (self.m.ctrl[j] & 0x80 == 0) return .{ .key_ptr = &self.m.slots[j].key, .value_ptr = &self.m.slots[j].value };
                }
                return null;
            }
        };

        pub fn iterator(self: *Self) Iterator {
            return .{ .m = self, .i = 0 };
        }
    };
}

pub fn FxHashMap(comptime K: type, comptime Val: type) type {
    return SwissMap(K, Val, hash.FxContext(K));
}

pub fn FxHashSet(comptime K: type) type {
    return SwissMap(K, void, hash.FxContext(K));
}

pub fn UniqueHashMap(comptime K: type, comptime Val: type) type {
    return SwissMap(K, Val, hash.UniqueContext(K));
}

pub fn FxIndexMap(comptime K: type, comptime Val: type) type {
    return std.ArrayHashMapUnmanaged(K, Val, hash.FxArrayContext(K), false);
}
