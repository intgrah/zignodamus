const std = @import("std");
const util = @import("util.zig");
const expr_mod = @import("expr.zig");
const Arena = @import("Arena.zig");
const ptr = @import("ptr.zig");

const BinderStyle = expr_mod.BinderStyle;
const ExprPtr = ptr.ExprPtr;
const LevelPtr = ptr.LevelPtr;
const LevelsPtr = ptr.LevelsPtr;
const NamePtr = ptr.NamePtr;
const StringPtr = ptr.StringPtr;
const BigUintPtr = ptr.BigUintPtr;

pub const V = *Value;
pub const E = *const Env;
pub const C = *const Ctx;
pub const S = *const Spine;

pub const Closure = struct {
    env: E,
    ctx: C,
    /// Body expression, with Kind in the ExprPtr holder tag
    tagged_body: ExprPtr,

    pub const Kind = enum(u2) { eval, infer };

    pub fn mk(env: E, b: ExprPtr, k: Kind, ctx: C) Closure {
        return .{ .env = env, .ctx = ctx, .tagged_body = b.withTag(@intFromEnum(k)) };
    }

    pub fn mkEval(env: E, b: ExprPtr) Closure {
        return mk(env, b, .eval, &Ctx.nil);
    }

    pub fn body(self: Closure) ExprPtr {
        return self.tagged_body.untag();
    }

    pub fn raw(self: Closure) ExprPtr {
        return self.tagged_body;
    }

    pub fn kind(self: Closure) Kind {
        return @enumFromInt(self.tagged_body.tag());
    }
};

pub const NameLevels = struct { name: NamePtr, levels: LevelsPtr };

pub const RigidHead = union(enum) {
    b_var: struct { lvl: u32, ty: V },
    axiom: NameLevels,
    ctor: NameLevels,
    recursor: NameLevels,
    quot_const: NameLevels,
    inductive: NameLevels,
};

pub const UnfoldHead = struct {
    name: NamePtr,
    levels: LevelsPtr,
};

/// Spine eliminator: App(arg: V) | Proj(ty_name, idx),
/// ## App
/// - [64-1] @intFromPtr(arg) 2-byte aligned
/// - [1-0] tag = 0
/// ## Proj
/// - [64-48] idx
/// - [48-1] ty_name 2-byte aligned
/// - [1-0] tag = 1
pub const Elim = struct {
    bits: u64,

    const idx_shift: u6 = 48;
    const name_mask: u64 = (1 << idx_shift) - 1;

    comptime {
        std.debug.assert(@alignOf(Value) > 1);
    }

    pub fn mkApp(v: V) Elim {
        const addr: u64 = @intFromPtr(v);
        std.debug.assert(addr & ~name_mask == 0);
        return .{ .bits = addr };
    }
    pub fn mkProj(ty_name: NamePtr, idx: u16) Elim {
        const low: u64 = ty_name.lowTagged();
        std.debug.assert(low & ~name_mask == 0);
        return .{ .bits = low | (@as(u64, idx) << idx_shift) };
    }
    pub fn isApp(self: Elim) bool {
        return self.bits & 1 == 0;
    }
    pub fn appV(self: Elim) V {
        return @ptrFromInt(@as(usize, @intCast(self.bits)));
    }
    pub fn projTyName(self: Elim) NamePtr {
        return NamePtr.fromLowTagged(@intCast(self.bits & name_mask));
    }
    pub fn projIdx(self: Elim) u16 {
        return @truncate(self.bits >> idx_shift);
    }
    pub fn raw(self: Elim) u64 {
        return self.bits;
    }
};

pub const Value = union(enum) {
    rigid: struct {
        head: RigidHead,
        spine: S,
    },
    unfold: struct {
        head: UnfoldHead,
        spine: S,
        head_value: *?V,
        forced: ?V,
    },
    lam: struct {
        binder_name: NamePtr,
        tagged_type: ExprPtr,
        domain: ?V,
        body: Closure,

        pub fn binderType(self: @This()) ExprPtr {
            return self.tagged_type.untag();
        }

        pub fn binderStyle(self: @This()) BinderStyle {
            return @enumFromInt(self.tagged_type.tag());
        }
    },
    pi: struct {
        binder_name: NamePtr,
        binder_style: BinderStyle,
        domain: V,
        body: Closure,
    },
    sort: struct {
        level: LevelPtr,
    },
    nat_lit: struct {
        ptr: BigUintPtr,
    },
    str_lit: struct {
        ptr: StringPtr,
    },
    thunk: struct {
        env: E,
        expr: ExprPtr,
        forced: ?V,
    },
};

pub const LevelSub = struct {
    ks: LevelsPtr,
    vs: LevelsPtr,
};

/// Hash-consed pruned env prefix. mask bit i set means bvar i is captured; slots holds the
/// captured values in index order, ranked by popcount. Never captures indices ≥ 64.
pub const Frame = struct {
    hash: u64,
    mask: u64,
    slots: []const V,
    lsub: ?*const LevelSub,

    pub fn getHash(self: *const Frame) u64 {
        return self.hash;
    }
};

pub const FramePair = struct {
    frame: Frame,
    env: Env,
};

pub const Env = struct {
    v: V,
    parent: E,
    frame: ?*const Frame,
    lsub: ?*const LevelSub,
    hash: u64,
    len: u32,

    pub const nil: Env = .{ .v = undefined, .parent = undefined, .frame = null, .lsub = null, .hash = 0, .len = 0 };

    pub fn getHash(self: *const Env) u64 {
        return self.hash;
    }

    pub fn lookup(self: *const Env, idx_in: u16) ?V {
        var idx = idx_in;
        var cur = self;
        while (cur.frame == null) {
            if (cur == &nil) return null;
            if (idx == 0) return cur.v;
            idx -= 1;
            cur = cur.parent;
        }
        const f = cur.frame.?;
        if (idx >= 64 or (f.mask >> @intCast(idx)) & 1 == 0) return null;
        const below = f.mask & ((@as(u64, 1) << @intCast(idx)) - 1);
        return f.slots[@popCount(below)];
    }
};

pub const Ctx = struct {
    ty: V,
    parent: C,

    pub const nil: Ctx = .{ .ty = undefined, .parent = undefined };

    pub fn lookup(self: *const Ctx, idx_in: u16) ?V {
        var idx = idx_in;
        var cur = self;
        while (cur != &nil) {
            if (idx == 0) return cur.ty;
            idx -= 1;
            cur = cur.parent;
        }
        return null;
    }
};

pub const Spine = struct {
    prev: S,
    elim: Elim,
    length: u32,

    pub const empty: Spine = .{ .prev = undefined, .elim = undefined, .length = 0 };

    pub fn isEmpty(self: *const Spine) bool {
        return self == &empty;
    }

    pub fn isSingleApp(self: *const Spine) bool {
        return self != &empty and self.prev == &empty and self.elim.isApp();
    }

    pub fn toVec(self: *const Spine, gpa: std.mem.Allocator) []const *const Elim {
        const length: usize = @intCast(self.length);
        const out = gpa.alloc(*const Elim, length) catch util.oom();
        var cur = self;
        var i: usize = length;
        while (cur != &empty) {
            i -= 1;
            out[i] = &cur.elim;
            cur = cur.prev;
        }
        return out;
    }

    pub fn get(self: *const Spine, i: usize) ?*const Elim {
        const length: usize = @intCast(self.length);
        if (i + 1 > length) return null;
        var steps = length - (i + 1);
        var cur = self;
        while (cur != &empty) {
            if (steps == 0) return &cur.elim;
            steps -= 1;
            cur = cur.prev;
        }
        return null;
    }
};

pub fn envEmpty() E {
    return &Env.nil;
}

pub fn envExtend(arena: *Arena, parent: E, v: V) E {
    const v_hash: u64 = @intCast(@intFromPtr(v));
    const parent_hash = parent.getHash();
    const hash = parent_hash *% 0x9E3779B97F4A7C15 +% v_hash;
    const e = arena.create(Env);
    e.* = .{ .v = v, .parent = parent, .frame = null, .lsub = parent.lsub, .hash = hash, .len = parent.len + 1 };
    return e;
}

pub fn ctxEmpty() C {
    return &Ctx.nil;
}

pub fn ctxExtend(arena: *Arena, parent: C, ty: V) C {
    const c = arena.create(Ctx);
    c.* = .{ .ty = ty, .parent = parent };
    return c;
}

pub fn spineEmpty() S {
    return &Spine.empty;
}

pub fn spineSnoc(arena: *Arena, prev: S, elim: Elim) S {
    const s = arena.create(Spine);
    s.* = .{ .prev = prev, .elim = elim, .length = prev.length + 1 };
    return s;
}

pub fn mkRigid(arena: *Arena, head: RigidHead, spine: S) V {
    const v = arena.create(Value);
    v.* = .{ .rigid = .{ .head = head, .spine = spine } };
    return v;
}

pub fn mkUnfold(
    arena: *Arena,
    name: NamePtr,
    levels: LevelsPtr,
    spine: S,
    head_value: *?V,
) V {
    const v = arena.create(Value);
    v.* = .{ .unfold = .{
        .head = .{ .name = name, .levels = levels },
        .spine = spine,
        .head_value = head_value,
        .forced = null,
    } };
    return v;
}

pub fn mkUnfoldHeadWithEmpty(
    arena: *Arena,
    name: NamePtr,
    levels: LevelsPtr,
    head_value: *?V,
    empty: S,
) V {
    const forced = head_value.*;
    const v = arena.create(Value);
    v.* = .{ .unfold = .{
        .head = .{ .name = name, .levels = levels },
        .spine = empty,
        .head_value = head_value,
        .forced = forced,
    } };
    return v;
}

pub fn mkLam(
    arena: *Arena,
    binder_name: NamePtr,
    binder_style: BinderStyle,
    binder_type: ExprPtr,
    body: Closure,
) V {
    const v = arena.create(Value);
    v.* = .{ .lam = .{
        .binder_name = binder_name,
        .tagged_type = binder_type.withTag(@intFromEnum(binder_style)),
        .domain = null,
        .body = body,
    } };
    return v;
}

pub fn mkPi(
    arena: *Arena,
    binder_name: NamePtr,
    binder_style: BinderStyle,
    domain: V,
    body: Closure,
) V {
    const v = arena.create(Value);
    v.* = .{ .pi = .{
        .binder_name = binder_name,
        .binder_style = binder_style,
        .domain = domain,
        .body = body,
    } };
    return v;
}

pub fn mkSort(arena: *Arena, level: LevelPtr) V {
    const v = arena.create(Value);
    v.* = .{ .sort = .{ .level = level } };
    return v;
}

pub fn mkNatlit(arena: *Arena, num: BigUintPtr) V {
    const v = arena.create(Value);
    v.* = .{ .nat_lit = .{ .ptr = num } };
    return v;
}

pub fn mkStrlit(arena: *Arena, s: StringPtr) V {
    const v = arena.create(Value);
    v.* = .{ .str_lit = .{ .ptr = s } };
    return v;
}

pub fn mkBvarWithEmpty(arena: *Arena, level: u32, ty: V, empty: S) V {
    const v = arena.create(Value);
    v.* = .{ .rigid = .{ .head = .{ .b_var = .{ .lvl = level, .ty = ty } }, .spine = empty } };
    return v;
}

pub fn mkRigidHeadWithEmpty(arena: *Arena, head: RigidHead, empty: S) V {
    const v = arena.create(Value);
    v.* = .{ .rigid = .{ .head = head, .spine = empty } };
    return v;
}

pub fn mkThunk(arena: *Arena, env: E, expr: ExprPtr) V {
    const v = arena.create(Value);
    v.* = .{ .thunk = .{ .env = env, .expr = expr, .forced = null } };
    return v;
}
