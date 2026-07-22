const std = @import("std");
const util = @import("util.zig");
const name = @import("name.zig");
const swiss_map = @import("swiss_map.zig");

const LevelPtr = @import("ptr.zig").LevelPtr;
const LevelsPtr = @import("ptr.zig").LevelsPtr;
const NamePtr = @import("ptr.zig").NamePtr;
const TcCtx = @import("TcCtx.zig");

pub const zero_hash: u64 = 283;
pub const succ_hash: u64 = 541;
pub const max_hash: u64 = 1091;
pub const imax_hash: u64 = 1747;
pub const param_hash: u64 = 947;

pub const Level = struct {
    hash: u64,
    kind: Kind,

    pub const Kind = union(enum) {
        zero,
        succ: LevelPtr,
        max: Pair,
        imax: Pair,
        param: NamePtr,
    };

    pub const Pair = struct { l: LevelPtr, r: LevelPtr };

    pub const zero: Level = .{ .hash = zero_hash, .kind = .zero };

    pub fn getHash(self: *const Level) u64 {
        return self.hash;
    }
};

pub fn levelSuccs(l_in: LevelPtr) struct { LevelPtr, usize } {
    var l = l_in;
    var num_succs: usize = 0;
    while (true) {
        switch (l.asRef().kind) {
            .succ => |p| {
                l = p;
                num_succs += 1;
            },
            else => break,
        }
    }
    return .{ l, num_succs };
}

fn combining(self: *TcCtx, l: LevelPtr, r: LevelPtr) LevelPtr {
    const pair = .{ l.asRef().kind, r.asRef().kind };
    switch (pair[0]) {
        .zero => return r,
        else => {},
    }
    switch (pair[1]) {
        .zero => return l,
        else => {},
    }
    switch (pair[0]) {
        .succ => |lp| switch (pair[1]) {
            .succ => |rp| {
                const pred = combining(self, lp, rp);
                return TcCtx.succ(self, pred);
            },
            else => {},
        },
        else => {},
    }
    return TcCtx.max(self, l, r);
}

pub fn simplify(self: *TcCtx, ptr: LevelPtr) LevelPtr {
    switch (ptr.asRef().kind) {
        .zero, .param => return ptr,
        else => {},
    }
    if (self.expr_cache.simplify_cache.get(ptr)) |cached| {
        return cached;
    }
    const result = switch (ptr.asRef().kind) {
        .zero, .param => ptr,
        .succ => |p| blk: {
            const val = simplify(self, p);
            break :blk TcCtx.succ(self, val);
        },
        .max => |p| blk: {
            const l = simplify(self, p.l);
            const r = simplify(self, p.r);
            break :blk combining(self, l, r);
        },
        .imax => |p| blk: {
            const l_simp = simplify(self, p.l);
            const r_simp = simplify(self, p.r);
            if (isZero(self, l_simp) or isOne(self, l_simp)) {
                break :blk r_simp;
            } else {
                break :blk switch (r_simp.asRef().kind) {
                    .zero => r_simp,
                    .succ => combining(self, l_simp, r_simp),
                    else => TcCtx.imax(self, l_simp, r_simp),
                };
            }
        },
    };
    self.expr_cache.simplify_cache.put(util.smp_allocator, ptr, result) catch util.oom();
    return result;
}

pub fn noDupesAllParams(self: *TcCtx, ls: LevelsPtr) bool {
    var set = swiss_map.FxHashSet(LevelPtr).empty;
    defer set.deinit(self.arena.child);
    for (ls.asRef()) |l| {
        switch (l.asRef().kind) {
            .param => {
                if (set.contains(l)) {
                    return false;
                } else {
                    set.put(self.arena.child, l, {}) catch util.oom();
                }
            },
            else => return false,
        }
    }
    return true;
}

pub fn substLevels(self: *TcCtx, uparams: LevelsPtr, ks: LevelsPtr, vs: LevelsPtr) LevelsPtr {
    const src = uparams.asRef();
    var out = std.ArrayList(LevelPtr).empty;
    defer out.deinit(self.arena.child);
    for (src) |l| {
        out.append(self.arena.child, substLevel(self, l, ks, vs)) catch util.oom();
    }
    return TcCtx.allocLevels(self, out.items);
}

pub fn substLevel(self: *TcCtx, level: LevelPtr, ks: LevelsPtr, vs: LevelsPtr) LevelPtr {
    switch (level.asRef().kind) {
        .zero => return TcCtx.zero(self),
        .succ => |p| {
            const val = substLevel(self, p, ks, vs);
            return TcCtx.succ(self, val);
        },
        .max => |p| {
            const l_prime = substLevel(self, p.l, ks, vs);
            const r_prime = substLevel(self, p.r, ks, vs);
            return TcCtx.max(self, l_prime, r_prime);
        },
        .imax => |p| {
            const l_prime = substLevel(self, p.l, ks, vs);
            const r_prime = substLevel(self, p.r, ks, vs);
            return TcCtx.imax(self, l_prime, r_prime);
        },
        .param => {
            const ks_s = ks.asRef();
            const vs_s = vs.asRef();
            var i: usize = 0;
            while (i < ks_s.len and i < vs_s.len) : (i += 1) {
                if (level == ks_s[i]) {
                    return vs_s[i];
                }
            }
            return level;
        },
    }
}

pub fn allUparamsDefined(self: *const TcCtx, level: LevelPtr, params: LevelsPtr) bool {
    switch (level.asRef().kind) {
        .zero => return true,
        .succ => |p| return allUparamsDefined(self, p, params),
        .max => |p| return allUparamsDefined(self, p.l, params) and allUparamsDefined(self, p.r, params),
        .imax => |p| return allUparamsDefined(self, p.l, params) and allUparamsDefined(self, p.r, params),
        .param => {
            for (params.asRef()) |x| {
                if (x == level) return true;
            }
            return false;
        },
    }
}

fn isAnyMax(level: LevelPtr) bool {
    return switch (level.asRef().kind) {
        .max, .imax => true,
        else => false,
    };
}

fn isParam(level: LevelPtr) bool {
    return switch (level.asRef().kind) {
        .param => true,
        else => false,
    };
}

fn substSimp(self: *TcCtx, level: LevelPtr, ks: LevelsPtr, vs: LevelsPtr) LevelPtr {
    const l = substLevel(self, level, ks, vs);
    return simplify(self, l);
}

fn leqImaxByCases(self: *TcCtx, param: LevelPtr, lhs: LevelPtr, rhs: LevelPtr, diff: isize) bool {
    const zero = TcCtx.zero(self);
    const succ_param = TcCtx.succ(self, param);
    const zero_slice = TcCtx.allocLevels(self, &.{zero});
    const succ_param_slice = TcCtx.allocLevels(self, &.{succ_param});
    const param_slice = TcCtx.allocLevels(self, &.{param});

    const lhs_0 = substSimp(self, lhs, param_slice, zero_slice);
    const rhs_0 = substSimp(self, rhs, param_slice, zero_slice);
    const lhs_s = substSimp(self, lhs, param_slice, succ_param_slice);
    const rhs_s = substSimp(self, rhs, param_slice, succ_param_slice);

    return leqCore(self, lhs_0, rhs_0, diff) and leqCore(self, lhs_s, rhs_s, diff);
}

fn leqCore(self: *TcCtx, l_in: LevelPtr, r_in: LevelPtr, diff: isize) bool {
    const lhs = l_in.asRef().kind;
    const rhs = r_in.asRef().kind;

    switch (lhs) {
        .zero => {
            if (diff >= 0) return true;
            switch (rhs) {
                .zero, .param => return false,
                .succ => |s| return leqCore(self, l_in, s, diff + 1),
                .max => |m| return leqCore(self, l_in, m.l, diff) or leqCore(self, l_in, m.r, diff),
                .imax => |x| return leqRhsImax(self, l_in, r_in, x, diff),
            }
        },
        .succ => |s| {
            if (rhs == .zero and diff < 0) return false;
            return leqCore(self, s, r_in, diff - 1);
        },
        .param => |a| switch (rhs) {
            .zero => return false,
            .param => |x| return a == x and diff >= 0,
            .succ => |s| return leqCore(self, l_in, s, diff + 1),
            .max => |m| return leqCore(self, l_in, m.l, diff) or leqCore(self, l_in, m.r, diff),
            .imax => |x| return leqRhsImax(self, l_in, r_in, x, diff),
        },
        .max => |m| {
            if (rhs == .zero and diff < 0) return false;
            if (rhs == .succ) return leqCore(self, l_in, rhs.succ, diff + 1);
            return leqCore(self, m.l, r_in, diff) and leqCore(self, m.r, r_in, diff);
        },
        .imax => |a| {
            if (rhs == .zero and diff < 0) return false;
            if (rhs == .succ) return leqCore(self, l_in, rhs.succ, diff + 1);
            if (rhs == .imax) {
                const x = rhs.imax;
                if (a.l == x.l and a.r == x.r and diff >= 0) return true;
            }
            if (isParam(a.r)) {
                return leqImaxByCases(self, a.r, l_in, r_in, diff);
            }
            if (rhs == .imax and isParam(rhs.imax.r)) {
                return leqImaxByCases(self, rhs.imax.r, l_in, r_in, diff);
            }
            switch (a.r.asRef().kind) {
                .imax => |b| {
                    const new_lhs = TcCtx.imax(self, a.l, b.r);
                    const new_rhs = TcCtx.imax(self, b.l, b.r);
                    const new_max = TcCtx.max(self, new_lhs, new_rhs);
                    return leqCore(self, new_max, r_in, diff);
                },
                .max => |b| {
                    const new_lhs = TcCtx.imax(self, a.l, b.l);
                    const new_rhs = TcCtx.imax(self, a.l, b.r);
                    const new_max = simplify(self, TcCtx.max(self, new_lhs, new_rhs));
                    return leqCore(self, new_max, r_in, diff);
                },
                else => {},
            }
            if (rhs == .imax) {
                return leqRhsImaxRewrite(self, l_in, rhs.imax, diff);
            }
            @panic("leq_core: non-normalized imax");
        },
    }
}

fn leqRhsImax(self: *TcCtx, l_in: LevelPtr, r_in: LevelPtr, x: Level.Pair, diff: isize) bool {
    if (isParam(x.r)) {
        return leqImaxByCases(self, x.r, l_in, r_in, diff);
    }
    return leqRhsImaxRewrite(self, l_in, x, diff);
}

fn leqRhsImaxRewrite(self: *TcCtx, l_in: LevelPtr, x: Level.Pair, diff: isize) bool {
    switch (x.r.asRef().kind) {
        .imax => |y| {
            const new_lhs = TcCtx.imax(self, x.l, y.r);
            const new_rhs = TcCtx.imax(self, y.l, y.r);
            const new_max = TcCtx.max(self, new_lhs, new_rhs);
            return leqCore(self, l_in, new_max, diff);
        },
        .max => |y| {
            const new_lhs = TcCtx.imax(self, x.l, y.l);
            const new_rhs0 = TcCtx.imax(self, x.l, y.r);
            const new_rhs = simplify(self, TcCtx.max(self, new_lhs, new_rhs0));
            return leqCore(self, l_in, new_rhs, diff);
        },
        else => @panic("leq_core: non-normalized imax"),
    }
}
pub fn leq(self: *TcCtx, l: LevelPtr, r: LevelPtr) bool {
    const l_prime = simplify(self, l);
    const r_prime = simplify(self, r);
    return leqCore(self, l_prime, r_prime, 0);
}

pub fn eqAntisymm(self: *TcCtx, l: LevelPtr, r: LevelPtr) bool {
    return leq(self, l, r) and leq(self, r, l);
}

pub fn eqAntisymmMany(self: *TcCtx, xs_in: LevelsPtr, ys_in: LevelsPtr) bool {
    const xs = xs_in.asRef();
    const ys = ys_in.asRef();
    if (xs.len != ys.len) {
        return false;
    }
    var i: usize = 0;
    while (i < xs.len) : (i += 1) {
        if (!eqAntisymm(self, xs[i], ys[i])) return false;
    }
    return true;
}

pub fn containsParam(uparams: LevelsPtr, candidate: NamePtr) bool {
    for (uparams.asRef()) |lptr| {
        switch (lptr.asRef().kind) {
            .param => |p| {
                if (p == candidate) return true;
            },
            else => {},
        }
    }
    return false;
}

fn isOne(self: *TcCtx, l: LevelPtr) bool {
    return switch (l.asRef().kind) {
        .succ => |p| isZero(self, p),
        else => false,
    };
}

pub fn isZero(self: *TcCtx, level: LevelPtr) bool {
    const zero = TcCtx.zero(self);
    return leq(self, level, zero);
}

pub fn isNonzero(self: *TcCtx, level: LevelPtr) bool {
    const zero = TcCtx.zero(self);
    const one = TcCtx.succ(self, zero);
    return leq(self, one, level);
}
