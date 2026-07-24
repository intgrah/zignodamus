const std = @import("std");
const util = @import("util.zig");
const expr_mod = @import("expr.zig");
const Arena = @import("Arena.zig");

const BinderStyle = expr_mod.BinderStyle;
const ExprPtr = @import("ptr.zig").ExprPtr;
const LevelPtr = @import("ptr.zig").LevelPtr;
const LevelsPtr = @import("ptr.zig").LevelsPtr;
const NamePtr = @import("ptr.zig").NamePtr;
const StringPtr = @import("ptr.zig").StringPtr;
const BigUintPtr = @import("ptr.zig").BigUintPtr;

pub const V = *Value;
pub const E = *const Env;
pub const C = *const Ctx;
pub const S = *const Spine;

pub const Closure = struct {
    env: E,
    body: ExprPtr,
    kind: Kind = .eval,
    ctx: C = &Ctx.nil,

    pub const Kind = enum { eval, infer };
};

pub const NameLevels = struct { name: NamePtr, levels: LevelsPtr };

pub const RigidHead = union(enum) {
    b_var: struct { lvl: u32, ty: V },
    local: ExprPtr,
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

pub const Elim = struct {
    a: usize,
    b: usize,

    comptime {
        std.debug.assert(@alignOf(Value) > 1);
    }

    pub fn mkApp(v: V) Elim {
        return .{ .a = @intFromPtr(v), .b = 0 };
    }
    pub fn mkProj(ty_name: NamePtr, idx: usize) Elim {
        return .{ .a = ty_name.lowTagged(), .b = idx };
    }
    pub fn isApp(self: Elim) bool {
        return self.a & 1 == 0;
    }
    pub fn appV(self: Elim) V {
        return @ptrFromInt(self.a);
    }
    pub fn projTyName(self: Elim) NamePtr {
        return NamePtr.fromLowTagged(self.a);
    }
    pub fn projIdx(self: Elim) usize {
        return self.b;
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
        binder_style: BinderStyle,
        binder_type: ExprPtr,
        domain: ?V,
        body: Closure,
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

pub const Frame = struct {
    hash: u64,
    mask: u64,
    slots: []const V,
    lsub: ?*const LevelSub,

    pub fn getHash(self: *const Frame) u64 {
        return self.hash;
    }
};

pub const Env = struct {
    v: V,
    parent: E,
    frame: ?*const Frame,
    lsub: ?*const LevelSub,
    hash: u64,
    len: u32,
    prune_mask: u64,
    prune_r: E,

    pub const nil: Env = .{ .v = undefined, .parent = undefined, .frame = null, .lsub = null, .hash = 0, .len = 0, .prune_mask = 0, .prune_r = undefined };

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
    e.* = .{ .v = v, .parent = parent, .frame = null, .lsub = parent.lsub, .hash = hash, .len = parent.len + 1, .prune_mask = 0, .prune_r = undefined };
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
        .binder_style = binder_style,
        .binder_type = binder_type,
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

pub fn mkNatlit(arena: *Arena, ptr: BigUintPtr) V {
    const v = arena.create(Value);
    v.* = .{ .nat_lit = .{ .ptr = ptr } };
    return v;
}

pub fn mkStrlit(arena: *Arena, ptr: StringPtr) V {
    const v = arena.create(Value);
    v.* = .{ .str_lit = .{ .ptr = ptr } };
    return v;
}

pub fn mkLocalWithEmpty(arena: *Arena, e: ExprPtr, empty: S) V {
    const v = arena.create(Value);
    v.* = .{ .rigid = .{ .head = .{ .local = e }, .spine = empty } };
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
