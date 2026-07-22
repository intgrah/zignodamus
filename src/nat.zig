const std = @import("std");
const util = @import("util.zig");

const A = util.smp_allocator;

pub const BigUint = std.math.big.int.Managed;

pub fn fromU32(n: u32) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.set(n) catch util.oom();
    return r;
}

pub fn fromUsize(n: usize) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.set(n) catch util.oom();
    return r;
}

pub fn fromDecimal(s: []const u8) ?BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.setString(10, s) catch |e| switch (e) {
        error.OutOfMemory => util.oom(),
        else => {
            r.deinit();
            return null;
        },
    };
    return r;
}

pub fn clone(b: *const BigUint) BigUint {
    return b.cloneWithDifferentAllocator(A) catch util.oom();
}

pub fn free(n: BigUint) void {
    var m = n;
    m.deinit();
}

pub fn addUsize(b: BigUint, n: usize) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.addScalar(&b, n) catch util.oom();
    return r;
}

/// Nat.zero
pub fn zero() BigUint {
    return BigUint.init(A) catch util.oom();
}

/// Nat.succ
pub fn succ(b: BigUint) BigUint {
    return addUsize(b, 1);
}

pub fn pred(b: BigUint) BigUint {
    std.debug.assert(!b.eqlZero());
    var r = BigUint.init(A) catch util.oom();
    r.addScalar(&b, -1) catch util.oom();
    return r;
}

/// Nat.add
pub fn add(x: BigUint, y: BigUint) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.add(&x, &y) catch util.oom();
    return r;
}

/// Nat.sub
pub fn sub(x: BigUint, y: BigUint) BigUint {
    if (y.order(x) == .gt) {
        return zero();
    }
    var r = BigUint.init(A) catch util.oom();
    r.sub(&x, &y) catch util.oom();
    return r;
}

/// Nat.mul
pub fn mul(x: BigUint, y: BigUint) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.mul(&x, &y) catch util.oom();
    return r;
}

/// Nat.pow
pub fn pow(x: BigUint, y: BigUint) ?BigUint {
    const e = y.toConst().toInt(u32) catch return null;
    var r = BigUint.init(A) catch util.oom();
    r.pow(&x, e) catch util.oom();
    return r;
}

/// Nat.div
pub fn div(x: BigUint, y: BigUint) BigUint {
    if (y.eqlZero()) {
        return zero();
    }
    var q = BigUint.init(A) catch util.oom();
    var rem = BigUint.init(A) catch util.oom();
    q.divFloor(&rem, &x, &y) catch util.oom();
    rem.deinit();
    return q;
}

/// Nat.mod
pub fn mod(x: BigUint, y: BigUint) BigUint {
    if (y.eqlZero()) {
        return clone(&x);
    }
    var q = BigUint.init(A) catch util.oom();
    var rem = BigUint.init(A) catch util.oom();
    q.divFloor(&rem, &x, &y) catch util.oom();
    q.deinit();
    return rem;
}

/// Nat.gcd
pub fn gcd(x: BigUint, y: BigUint) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.gcd(&x, &y) catch util.oom();
    return r;
}

/// Nat.beq
pub fn beq(x: BigUint, y: BigUint) bool {
    return x.eql(y);
}

/// Nat.ble
pub fn ble(x: BigUint, y: BigUint) bool {
    return x.order(y) != .gt;
}

/// Nat.land
pub fn land(x: BigUint, y: BigUint) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.bitAnd(&x, &y) catch util.oom();
    return r;
}

/// Nat.lor
pub fn lor(x: BigUint, y: BigUint) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.bitOr(&x, &y) catch util.oom();
    return r;
}

/// Nat.xor
pub fn xor(x: BigUint, y: BigUint) BigUint {
    var r = BigUint.init(A) catch util.oom();
    r.bitXor(&x, &y) catch util.oom();
    return r;
}

/// Nat.shiftLeft
pub fn shiftLeft(x: BigUint, y: BigUint) ?BigUint {
    const sh = y.toConst().toInt(usize) catch return null;
    var r = BigUint.init(A) catch util.oom();
    r.shiftLeft(&x, sh) catch util.oom();
    return r;
}

/// Nat.shiftRight
pub fn shiftRight(x: BigUint, y: BigUint) ?BigUint {
    const sh = y.toConst().toInt(usize) catch return null;
    var r = BigUint.init(A) catch util.oom();
    r.shiftRight(&x, sh) catch util.oom();
    return r;
}
