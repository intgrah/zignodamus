const util = @import("util.zig");
const std = @import("std");
const A = std.heap.smp_allocator;

pub const BigUint = std.math.big.int.Managed;

pub fn zero() BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.set(0) catch util.oom();
    return r;
}

pub fn fromU32(n: u32) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.set(n) catch util.oom();
    return r;
}

pub fn isZero(n: BigUint) bool {
    return n.eqlZero();
}

pub fn clone(b: *const BigUint) BigUint {
    return b.cloneWithDifferentAllocator(A) catch util.oom();
}

pub fn free(n: BigUint) void {
    var m = n;
    m.deinit();
}

pub fn addUsize(b: BigUint, n: usize) BigUint {
    var bb = b;
    var r = BigUint.init(A) catch util.oom();
    r.addScalar(&bb, n) catch util.oom();
    return r;
}

pub fn subU8(b: BigUint, n: u8) BigUint {
    var bb = b;
    var r = BigUint.init(A) catch util.oom();
    r.addScalar(&bb, -@as(i16, n)) catch util.oom();
    return r;
}

pub fn fromUsize(n: usize) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.set(n) catch util.oom();
    return r;
}
