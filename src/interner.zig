const std = @import("std");
const Arena = @import("Arena.zig");
const expr = @import("expr.zig");
const value = @import("value.zig");
const level = @import("level.zig");
const name = @import("name.zig");
const ptr = @import("ptr.zig");
const util = @import("util.zig");
const FxHasher = @import("hash.zig").FxHasher;
const BigUint = @import("nat.zig").BigUint;
const LevelPtr = ptr.LevelPtr;
const smp_allocator = util.smp_allocator;

fn Interner(comptime T: type) type {
    return struct {
        ctrl: [*]u8 = dummy_ctrl[0..].ptr,
        slots: [*]Slot = undefined,
        cap: usize = 0,
        count: usize = 0,
        growth_left: usize = 0,

        const Self = @This();
        const Slot = *const T;
        const Group = @Vector(16, u8);
        const ctrl_empty: u8 = 0x80;
        var dummy_ctrl: [16]u8 = .{ctrl_empty} ** 16;

        inline fn h2(h: u64) u8 {
            return @as(u8, @truncate(h >> 57)) & 0x7f;
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

        pub const empty: Self = .{};

        pub fn len(self: *const Self) usize {
            return self.count;
        }

        fn place(self: *Self, h: u64, r: *const T) void {
            const f = h2(h);
            const mask = self.cap - 1;
            var pos: usize = @intCast(h & mask);
            var stride: usize = 16;
            while (true) {
                const empties = matchByte(self.loadGroup(pos), ctrl_empty);
                if (empties != 0) {
                    const i = (pos + @ctz(empties)) & mask;
                    self.setCtrl(i, f);
                    self.slots[i] = r;
                    self.count += 1;
                    self.growth_left -= 1;
                    return;
                }
                pos = (pos + stride) & mask;
                stride += 16;
            }
        }

        noinline fn allocCap(self: *Self, newcap: usize) void {
            const buf = smp_allocator.alignedAlloc(u8, .of(Slot), bufLen(newcap)) catch util.oom();
            @memset(buf[0 .. newcap + 16], ctrl_empty);
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
                if (old_ctrl[i] & 0x80 == 0) self.place(structHashRef(T, old_slots[i]), old_slots[i]);
            }
            if (old_cap != 0) {
                smp_allocator.free(@as([*]align(@alignOf(Slot)) u8, @alignCast(old_ctrl))[0..bufLen(old_cap)]);
            }
        }

        fn maybeGrow(self: *Self) void {
            if (self.growth_left == 0) self.allocCap(if (self.cap == 0) 16 else self.cap * 2);
        }

        pub inline fn get(self: *const Self, v: *const T) ?*const T {
            if (self.cap == 0) return null;
            const h = structHashRef(T, v);
            const f = h2(h);
            const mask = self.cap - 1;
            var pos: usize = @intCast(h & mask);
            var stride: usize = 16;
            while (true) {
                const g = self.loadGroup(pos);
                var m = matchByte(g, f);
                while (m != 0) {
                    const i = (pos + @ctz(m)) & mask;
                    if (refEql(T, self.slots[i], v)) return self.slots[i];
                    m &= m - 1;
                }
                if (matchByte(g, ctrl_empty) != 0) return null;
                pos = (pos + stride) & mask;
                stride += 16;
            }
        }

        pub fn insert(self: *Self, ar: *Arena, v: *const T) *const T {
            self.maybeGrow();
            const r = ar.create(T);
            r.* = v.*;
            self.place(structHashRef(T, r), r);
            return r;
        }

        pub fn intern(self: *Self, ar: *Arena, v: T) *const T {
            if (self.get(&v)) |r| return r;
            return self.insert(ar, &v);
        }

        pub fn insertUnique(self: *Self, ar: *Arena, v: T) *const T {
            self.maybeGrow();
            const r = ar.create(T);
            r.* = v;
            self.placeUniqueRef(structHashRef(T, r), r);
            return r;
        }

        fn placeUniqueRef(self: *Self, h: u64, r: Slot) void {
            const f = h2(h);
            const mask = self.cap - 1;
            var pos: usize = @intCast(h & mask);
            var stride: usize = 16;
            while (true) {
                const g = self.loadGroup(pos);
                var m = matchByte(g, f);
                while (m != 0) {
                    const i = (pos + @ctz(m)) & mask;
                    if (refEql(T, self.slots[i], r)) @panic("Attempted to insert duplicate");
                    m &= m - 1;
                }
                const empties = matchByte(g, ctrl_empty);
                if (empties != 0) {
                    const i = (pos + @ctz(empties)) & mask;
                    self.setCtrl(i, f);
                    self.slots[i] = r;
                    self.count += 1;
                    self.growth_left -= 1;
                    return;
                }
                pos = (pos + stride) & mask;
                stride += 16;
            }
        }

        pub const BuildEntry = struct { hash: u64, ref: Slot };

        pub fn buildUnique(self: *Self, entries: []BuildEntry) void {
            std.debug.assert(self.count == 0);
            if (entries.len == 0) return;
            var newcap: usize = 16;
            while (maxLoad(newcap) < entries.len) newcap *= 2;
            self.allocCap(newcap);
            const bits: usize = @ctz(newcap);
            const scratch = smp_allocator.alloc(BuildEntry, entries.len) catch util.oom();
            defer smp_allocator.free(scratch);
            var src: []BuildEntry = entries;
            var dst: []BuildEntry = scratch;
            var shift: usize = 0;
            while (shift < bits) : (shift += 8) {
                var counts = [_]usize{0} ** 256;
                for (src) |e| counts[@as(usize, @intCast((e.hash >> @intCast(shift)) & 0xff))] += 1;
                var sum: usize = 0;
                for (&counts) |*c| {
                    const t = c.*;
                    c.* = sum;
                    sum += t;
                }
                for (src) |e| {
                    const d: usize = @intCast((e.hash >> @intCast(shift)) & 0xff);
                    dst[counts[d]] = e;
                    counts[d] += 1;
                }
                const tmp = src;
                src = dst;
                dst = tmp;
            }
            for (src) |e| self.placeUniqueRef(e.hash, e.ref);
        }

        pub fn deinit(self: *Self) void {
            if (self.cap != 0) {
                smp_allocator.free(@as([*]align(@alignOf(Slot)) u8, @alignCast(self.ctrl))[0..bufLen(self.cap)]);
            }
            self.* = .{};
        }
    };
}

inline fn structHashRef(comptime T: type, v: *const T) u64 {
    return getHashOf(T, v);
}

inline fn getHashOf(comptime T: type, v: *const T) u64 {
    if (T == []const u8) {
        return std.hash.Wyhash.hash(0, v.*);
    }
    if (T == BigUint) {
        var hasher = FxHasher{};
        for (v.limbs[0..@as(usize, @intCast(v.len()))]) |limb| hasher.writeU64(limb);
        return hasher.finish();
    }
    return v.getHash();
}

inline fn refEql(comptime T: type, a: *const T, b: *const T) bool {
    if (T == []const u8) return std.mem.eql(u8, a.*, b.*);
    if (T == BigUint) return a.eql(b.*);
    if (T == value.Frame) {
        return a.mask == b.mask and a.lsub == b.lsub and std.mem.eql(value.V, a.slots, b.slots);
    }
    if (T == expr.Expr) {
        if (a.kind == .let) {
            if (b.kind != .let) return false;
            return a.hash == b.hash and std.meta.eql(a.kind.let.data.*, b.kind.let.data.*);
        }
        if (b.kind == .let) return false;
    }
    return std.meta.eql(a.*, b.*);
}

pub const NameInterner = Interner(name.Name);
pub const FrameInterner = Interner(value.Frame);
pub const LevelInterner = Interner(level.Level);
pub const ExprInterner = Interner(expr.Expr);
pub const StringInterner = Interner([]const u8);

pub const BigUintInterner = struct {
    table: std.HashMapUnmanaged(*const BigUint, void, Context, 80) = .{},

    const Context = struct {
        pub fn hash(_: Context, k: *const BigUint) u64 {
            return structHashRef(BigUint, k);
        }
        pub fn eql(_: Context, a: *const BigUint, b: *const BigUint) bool {
            return refEql(BigUint, a, b);
        }
    };

    pub const empty: BigUintInterner = .{};
    const Probe = struct {
        h: u64,
        pub fn hash(self: @This(), _: *const BigUint) u64 {
            return self.h;
        }
        pub fn eql(_: @This(), a: *const BigUint, b: *const BigUint) bool {
            return refEql(BigUint, a, b);
        }
    };

    pub fn get(self: *const BigUintInterner, v: *const BigUint) ?*const BigUint {
        const h = structHashRef(BigUint, v);
        return self.table.getKeyAdapted(v, Probe{ .h = h });
    }
    pub fn insert(self: *BigUintInterner, ar: *Arena, v: BigUint) *const BigUint {
        const r = ar.create(BigUint);
        r.* = v;
        self.table.putContext(ar.child, r, {}, Context{}) catch util.oom();
        return r;
    }
    pub fn intern(self: *BigUintInterner, ar: *Arena, v: BigUint) *const BigUint {
        if (self.get(&v)) |r| {
            var m = v;
            m.deinit();
            return r;
        }
        return self.insert(ar, v);
    }

    pub fn deinit(self: *BigUintInterner) void {
        var it = self.table.iterator();
        while (it.next()) |e| {
            var m = e.key_ptr.*.*;
            m.deinit();
        }
        self.table.deinit(smp_allocator);
    }
};

pub const LevelsInterner = struct {
    table: std.HashMapUnmanaged([]const LevelPtr, void, Context, 80) = .{},

    const Context = struct {
        pub fn hash(_: Context, k: []const LevelPtr) u64 {
            return slicesStructHash(k);
        }
        pub fn eql(_: Context, a: []const LevelPtr, b: []const LevelPtr) bool {
            return slicesEql(a, b);
        }
    };

    pub const empty: LevelsInterner = .{};

    pub fn get(self: *const LevelsInterner, v: []const LevelPtr) ?[]const LevelPtr {
        const h = slicesStructHash(v);
        return self.table.getKeyAdapted(v, SliceProbe{ .h = h });
    }

    pub fn intern(self: *LevelsInterner, ar: *Arena, v: []const LevelPtr) []const LevelPtr {
        if (self.get(v)) |r| return r;
        const r = ar.dupe(LevelPtr, v);
        self.table.putContext(ar.child, r, {}, Context{}) catch util.oom();
        return r;
    }

    pub fn deinit(self: *LevelsInterner) void {
        self.table.deinit(smp_allocator);
    }

    const SliceProbe = struct {
        h: u64,
        pub fn hash(self: @This(), _: []const LevelPtr) u64 {
            return self.h;
        }
        pub fn eql(_: @This(), a: []const LevelPtr, b: []const LevelPtr) bool {
            return slicesEql(a, b);
        }
    };
};

fn slicesStructHash(v: []const LevelPtr) u64 {
    var hasher = FxHasher{};
    for (v) |lp| hasher.writeU64(lp.getHash());
    return hasher.finish();
}

fn slicesEql(a: []const LevelPtr, b: []const LevelPtr) bool {
    if (a.len != b.len) return false;
    for (a, b) |x, y| {
        if (x != y) return false;
    }
    return true;
}
