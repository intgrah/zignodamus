const env_mod = @import("env.zig");
const nat = @import("nat.zig");
const tc = @import("tc.zig");
const util = @import("util.zig");
const value = @import("value.zig");
const eval = @import("eval.zig");
const level = @import("level.zig");
const TcCtx = @import("TcCtx.zig");
const ptr = @import("ptr.zig");

const ConstructorData = env_mod.ConstructorData;
const Declar = env_mod.Declar;
const ReducibilityHint = env_mod.ReducibilityHint;
const TypeChecker = tc.TypeChecker;
const ExprPtr = ptr.ExprPtr;
const LevelPtr = ptr.LevelPtr;
const NamePtr = ptr.NamePtr;
const Elim = value.Elim;
const Env = value.Env;
const RigidHead = value.RigidHead;
const Spine = value.Spine;
const UnfoldHead = value.UnfoldHead;
const Value = value.Value;
const E = value.E;
const S = value.S;
const V = value.V;

fn rigidHeadEq(hx: RigidHead, hy: RigidHead) bool {
    return switch (hx) {
        .b_var => |a| switch (hy) {
            .b_var => |b| a.lvl == b.lvl,
            else => false,
        },
        .local => |a| switch (hy) {
            .local => |b| a == b,
            else => false,
        },
        else => false,
    };
}

fn isCacheable(v: *const Value) bool {
    return switch (v.*) {
        .pi, .lam, .unfold => true,
        .rigid => |r| switch (r.head) {
            .recursor, .quot_const => true,
            else => false,
        },
        else => false,
    };
}

pub fn defEqCore(self: *TypeChecker, x: ExprPtr, y: ExprPtr) bool {
    const depth: u32 = self.ctx.dbj_level_counter;
    const env = value.envEmpty();
    const vx = eval.eval(self, depth, env, x);
    const vy = eval.eval(self, depth, env, y);
    if (tryProofIrrelAt(self, depth, vx, vy)) {
        return true;
    }
    return convTypesAt(self, depth, vx, vy);
}

pub fn convTypesAt(self: *TypeChecker, depth: u32, a: V, b: V) bool {
    return conv(self, true, depth, a, b);
}

pub fn defEqAt(self: *TypeChecker, depth: u32, vx: V, vy: V) bool {
    if (tryProofIrrelAt(self, depth, vx, vy)) {
        return true;
    }
    return convTypesAt(self, depth, vx, vy);
}

fn envsPtrEqual(e1: E, e2: E) bool {
    var a = e1;
    var b = e2;
    const nil = &value.Env.nil;
    while (true) {
        if (a == b) {
            return true;
        }
        if (a == nil or b == nil) {
            return false;
        }
        if (a.frame != null or b.frame != null) {
            return false;
        }
        if (a.hash != b.hash) {
            return false;
        }
        if (a.v != b.v) {
            return false;
        }
        a = a.parent;
        b = b.parent;
    }
}

fn conv(self: *TypeChecker, comptime RIGID: bool, depth: u32, x_in: V, y_in: V) bool {
    const x = eval.forceThunk(self, depth, x_in);
    const y = eval.forceThunk(self, depth, y_in);
    if (x == y) {
        return true;
    }
    if (bvarSingleApps(x, y)) |args| {
        if (conv(self, RIGID, depth, args[0], args[1])) {
            return true;
        }
    }
    return convGeneral(self, RIGID, depth, x, y);
}

fn bvarSingleApps(x: V, y: V) ?[2]V {
    if (x.* != .rigid or y.* != .rigid) return null;
    const rx = x.rigid;
    const ry = y.rigid;
    if (rx.head != .b_var or ry.head != .b_var) return null;
    if (rx.head.b_var.lvl != ry.head.b_var.lvl) return null;
    if (!rx.spine.isSingleApp() or !ry.spine.isSingleApp()) return null;
    return .{ rx.spine.elim.appV(), ry.spine.elim.appV() };
}

fn isLam(v: V) bool {
    return switch (v.*) {
        .lam => true,
        else => false,
    };
}

fn convGeneral(self: *TypeChecker, comptime RIGID: bool, depth: u32, x: V, y: V) bool {
    const xa = @intFromPtr(x);
    const ya = @intFromPtr(y);
    const cacheable = isCacheable(x) or isCacheable(y);
    const neg_eligible = !isLam(x) and !isLam(y);
    if (cacheable) {
        if (self.tc_cache.value_eq.checkEqIfKnown(xa, ya)) {
            return true;
        }
        const cache_key = if (xa < ya) .{ xa, ya } else .{ ya, xa };
        if (RIGID and neg_eligible) {
            if (self.tc_cache.conv_cache_neg.contains(cache_key)) {
                return false;
            }
            if (self.tc_cache.probe_depth > 0 and self.tc_cache.conv_cache_neg_probe.contains(cache_key)) {
                return false;
            }
        }
        const result = convNoCache(self, RIGID, depth, x, y);
        if (result) {
            self.tc_cache.value_eq.unite(xa, ya);
        } else if (RIGID and neg_eligible) {
            if (self.tc_cache.probe_depth == 0) {
                self.tc_cache.conv_cache_neg.put(util.smp_allocator, cache_key, {}) catch util.oom();
            } else {
                self.tc_cache.conv_cache_neg_probe.put(util.smp_allocator, cache_key, {}) catch util.oom();
            }
        }
        return result;
    } else {
        return convNoCache(self, RIGID, depth, x, y);
    }
}

fn convNoCache(self: *TypeChecker, comptime RIGID: bool, depth: u32, t: V, t2: V) bool {
    if (convNat(self, RIGID, depth, t, t2)) |r| {
        return r;
    }
    if (convDirect(self, RIGID, depth, t, t2)) {
        return true;
    }
    return convCold(self, RIGID, depth, t, t2);
}

fn isRecursorOrQuot(v: V) bool {
    return switch (v.*) {
        .rigid => |r| switch (r.head) {
            .recursor, .quot_const => true,
            else => false,
        },
        else => false,
    };
}

fn isUnfold(v: V) bool {
    return switch (v.*) {
        .unfold => true,
        else => false,
    };
}

fn convDirect(self: *TypeChecker, comptime RIGID: bool, depth: u32, t: V, t2: V) bool {
    switch (t.*) {
        .sort => |sx| switch (t2.*) {
            .sort => |sy| return level.eqAntisymm(self.ctx, sx.level, sy.level),
            else => {},
        },
        .nat_lit => |px| switch (t2.*) {
            .nat_lit => |py| return px.ptr == py.ptr,
            else => {},
        },
        .str_lit => |px| switch (t2.*) {
            .str_lit => |py| return px.ptr == py.ptr,
            else => {},
        },
        else => {},
    }

    switch (t.*) {
        .rigid => |rx| switch (t2.*) {
            .rigid => |ry| {
                if (rigidHeadEq(rx.head, ry.head)) {
                    return convSpine(self, RIGID, depth, rx.spine, ry.spine);
                }
                switch (rx.head) {
                    .ctor => |cx| switch (ry.head) {
                        .ctor => |cy| {
                            if (cx.name == cy.name and level.eqAntisymmMany(self.ctx, cx.levels, cy.levels)) {
                                return convSpine(self, RIGID, depth, rx.spine, ry.spine);
                            }
                        },
                        else => {},
                    },
                    .inductive => |ix| switch (ry.head) {
                        .inductive => |iy| {
                            if (ix.name == iy.name and level.eqAntisymmMany(self.ctx, ix.levels, iy.levels)) {
                                return convSpine(self, RIGID, depth, rx.spine, ry.spine);
                            }
                        },
                        else => {},
                    },
                    .axiom => |ax| switch (ry.head) {
                        .axiom => |ay| {
                            if (ax.name == ay.name and level.eqAntisymmMany(self.ctx, ax.levels, ay.levels)) {
                                return convSpine(self, RIGID, depth, rx.spine, ry.spine);
                            }
                        },
                        else => {},
                    },
                    .recursor => |nx| switch (ry.head) {
                        .recursor => |ny| {
                            const heads_match = nx.name == ny.name and level.eqAntisymmMany(self.ctx, nx.levels, ny.levels);
                            return convIota(self, RIGID, depth, t, t2, heads_match, rx.spine, ry.spine);
                        },
                        else => {},
                    },
                    .quot_const => |nx| switch (ry.head) {
                        .quot_const => |ny| {
                            const heads_match = nx.name == ny.name and level.eqAntisymmMany(self.ctx, nx.levels, ny.levels);
                            return convIota(self, RIGID, depth, t, t2, heads_match, rx.spine, ry.spine);
                        },
                        else => {},
                    },
                    else => {},
                }
            },
            else => {},
        },
        else => {},
    }

    switch (t.*) {
        .pi => |bx_pi| switch (t2.*) {
            .pi => |by_pi| {
                if (bx_pi.body.body == by_pi.body.body and bx_pi.domain == by_pi.domain and bx_pi.body.kind == by_pi.body.kind and envsPtrEqual(bx_pi.body.env, by_pi.body.env)) {
                    return true;
                }
                if (!conv(self, RIGID, depth, bx_pi.domain, by_pi.domain)) {
                    return false;
                }
                const dx = bx_pi.domain;
                const fresh = eval.mkBvarHc(self, depth, dx);
                const vx = eval.applyClosure(self, depth + 1, &bx_pi.body, fresh, dx);
                const vy = eval.applyClosure(self, depth + 1, &by_pi.body, fresh, dx);
                return conv(self, RIGID, depth + 1, vx, vy);
            },
            else => {},
        },
        .lam => |bx_lam| switch (t2.*) {
            .lam => |by_lam| {
                if (bx_lam.body.body == by_lam.body.body and envsPtrEqual(bx_lam.body.env, by_lam.body.env)) {
                    return true;
                }
                const dx = eval.lamDomain(self, depth, t);
                const fresh = eval.mkBvarHc(self, depth, dx);
                const vx = eval.applyClosure(self, depth + 1, &bx_lam.body, fresh, null);
                const vy = eval.applyClosure(self, depth + 1, &by_lam.body, fresh, null);
                return conv(self, RIGID, depth + 1, vx, vy);
            },
            else => {},
        },
        else => {},
    }

    switch (t.*) {
        .unfold => |ux| switch (t2.*) {
            .unfold => |uy| {
                const nx = ux.head.name;
                const ny = uy.head.name;
                const heads_match = nx == ny and level.eqAntisymmMany(self.ctx, ux.head.levels, uy.head.levels);
                const sx = ux.spine;
                const sy = uy.spine;
                if (RIGID) {
                    if (heads_match and spineProbe(self, depth, sx, sy)) {
                        return true;
                    }
                    if (tryProofIrrelAt(self, depth, t, t2)) {
                        return true;
                    }
                    if (heads_match) {
                        return unfoldPair(self, depth, t, t2);
                    }
                    const lh = unfoldHint(self, nx);
                    const rh = unfoldHint(self, ny);
                    if (lh.isLt(rh)) {
                        const v2 = eval.unfoldValue(self, depth, t2);
                        if (v2 != t2) {
                            return conv(self, true, depth, t, v2);
                        }
                        const v1 = eval.unfoldValue(self, depth, t);
                        if (v1 != t) {
                            return conv(self, true, depth, v1, t2);
                        }
                        const f2 = eval.unfoldValueDemand(self, depth, t2);
                        if (f2 == t2) {
                            return false;
                        }
                        return conv(self, true, depth, t, f2);
                    } else if (rh.isLt(lh)) {
                        const v1 = eval.unfoldValue(self, depth, t);
                        if (v1 != t) {
                            return conv(self, true, depth, v1, t2);
                        }
                        const v2 = eval.unfoldValue(self, depth, t2);
                        if (v2 != t2) {
                            return conv(self, true, depth, t, v2);
                        }
                        const f1 = eval.unfoldValueDemand(self, depth, t);
                        if (f1 == t) {
                            return false;
                        }
                        return conv(self, true, depth, f1, t2);
                    } else {
                        return unfoldPair(self, depth, t, t2);
                    }
                } else if (heads_match) {
                    return convSpine(self, false, depth, sx, sy);
                } else {
                    return false;
                }
            },
            else => {},
        },
        else => {},
    }

    if (RIGID) {
        switch (t.*) {
            .unfold => {
                if (tryProofIrrelAt(self, depth, t, t2)) {
                    return true;
                }
                const v1 = eval.unfoldValue(self, depth, t);
                if (v1 == t) {
                    const f1 = eval.unfoldValueDemand(self, depth, t);
                    if (f1 == t) {
                        return false;
                    }
                    return conv(self, true, depth, f1, t2);
                }
                return conv(self, true, depth, v1, t2);
            },
            else => {},
        }
        switch (t2.*) {
            .unfold => {
                if (tryProofIrrelAt(self, depth, t, t2)) {
                    return true;
                }
                const v2 = eval.unfoldValue(self, depth, t2);
                if (v2 == t2) {
                    const f2 = eval.unfoldValueDemand(self, depth, t2);
                    if (f2 == t2) {
                        return false;
                    }
                    return conv(self, true, depth, t, f2);
                }
                return conv(self, true, depth, t, v2);
            },
            else => {},
        }
        if (isRecursorOrQuot(t)) {
            if (tryProofIrrelAt(self, depth, t, t2)) {
                return true;
            }
            if (eval.iotaValue(self, depth, t)) |v1| {
                return conv(self, true, depth, v1, t2);
            }
            if (isRecursorOrQuot(t2)) {
                if (eval.iotaValue(self, depth, t2)) |v2| {
                    return conv(self, true, depth, t, v2);
                }
            }
            if (isUnfold(t2)) {
                const v2 = eval.unfoldValueDemand(self, depth, t2);
                if (v2 != t2) {
                    return conv(self, true, depth, t, v2);
                }
            }
            return false;
        }
        if (isRecursorOrQuot(t2)) {
            if (tryProofIrrelAt(self, depth, t, t2)) {
                return true;
            }
            if (eval.iotaValue(self, depth, t2)) |v2| {
                return conv(self, true, depth, t, v2);
            }
            if (isUnfold(t)) {
                const v1 = eval.unfoldValueDemand(self, depth, t);
                if (v1 != t) {
                    return conv(self, true, depth, v1, t2);
                }
            }
            return false;
        }
    }

    return false;
}

fn spineProbe(self: *TypeChecker, depth: u32, sx: S, sy: S) bool {
    self.tc_cache.probe_depth += 1;
    const ok = convSpine(self, true, depth, sx, sy);
    self.tc_cache.probe_depth -= 1;
    return ok;
}

fn unfoldPair(self: *TypeChecker, depth: u32, t: V, t2: V) bool {
    const v1 = eval.unfoldValue(self, depth, t);
    const v2 = eval.unfoldValue(self, depth, t2);
    if (v1 == t and v2 == t2) {
        const f1 = eval.unfoldValueDemand(self, depth, t);
        const f2 = eval.unfoldValueDemand(self, depth, t2);
        if (f1 == t and f2 == t2) {
            return false;
        }
        return conv(self, true, depth, f1, f2);
    }
    return conv(self, true, depth, v1, v2);
}

fn convIota(self: *TypeChecker, comptime RIGID: bool, depth: u32, t: V, t2: V, heads_match: bool, sx: S, sy: S) bool {
    if (RIGID) {
        if (heads_match and spineProbe(self, depth, sx, sy)) {
            return true;
        }
        if (tryProofIrrelAt(self, depth, t, t2)) {
            return true;
        }
        const v1 = iotaOrSelf(self, depth, t);
        const v2 = iotaOrSelf(self, depth, t2);
        const progressed = (v1 != t) or (v2 != t2);
        if (progressed) {
            return conv(self, true, depth, v1, v2);
        }
        if (heads_match) {
            return convSpine(self, true, depth, sx, sy);
        }
        return false;
    } else if (heads_match) {
        return convSpine(self, false, depth, sx, sy);
    } else {
        return false;
    }
}

fn iotaOrSelf(self: *TypeChecker, depth: u32, v: V) V {
    return eval.iotaValue(self, depth, v) orelse v;
}

fn unfoldHint(self: *TypeChecker, name: NamePtr) ReducibilityHint {
    if (self.env.getDeclar(name)) |d| {
        switch (d.*) {
            .definition => |def| return def.hint,
            else => return ReducibilityHint.opaque_,
        }
    }
    return ReducibilityHint.opaque_;
}

fn convSpine(self: *TypeChecker, comptime RIGID: bool, depth: u32, sx: S, sy: S) bool {
    const empty = &Spine.empty;
    if (sx == empty or sy == empty) {
        return sx == empty and sy == empty;
    }
    if (!convSpine(self, RIGID, depth, sx.prev, sy.prev)) {
        return false;
    }
    if (sx.elim.isApp()) {
        if (!sy.elim.isApp()) return false;
        return conv(self, RIGID, depth, sx.elim.appV(), sy.elim.appV());
    } else {
        if (sy.elim.isApp()) return false;
        return sx.elim.projTyName() == sy.elim.projTyName() and sx.elim.projIdx() == sy.elim.projIdx();
    }
}

fn convCold(self: *TypeChecker, comptime RIGID: bool, depth: u32, x: V, y: V) bool {
    if (!RIGID) {
        return false;
    }
    if (tryProofIrrelAt(self, depth, x, y)) {
        return true;
    }
    switch (x.*) {
        .lam => |lx| {
            if (!isLam(y)) {
                const domain = eval.lamDomain(self, depth, x);
                const fresh = eval.mkBvarHc(self, depth, domain);
                const lhs = eval.applyClosure(self, depth + 1, &lx.body, fresh, null);
                const rhs = eval.apply(self, depth + 1, y, fresh);
                return conv(self, true, depth + 1, lhs, rhs);
            }
        },
        else => {},
    }
    switch (y.*) {
        .lam => |ly| {
            if (!isLam(x)) {
                const domain = eval.lamDomain(self, depth, y);
                const fresh = eval.mkBvarHc(self, depth, domain);
                const lhs = eval.apply(self, depth + 1, x, fresh);
                const rhs = eval.applyClosure(self, depth + 1, &ly.body, fresh, null);
                return conv(self, true, depth + 1, lhs, rhs);
            }
        },
        else => {},
    }
    return tryStructEta(self, depth, x, y);
}

fn tryStructEta(self: *TypeChecker, depth: u32, x: V, y: V) bool {
    const xt = valueTypeOpt(self, depth, x);
    const yt = valueTypeOpt(self, depth, y);
    const opts = [_]?V{ xt, yt };
    for (opts) |maybe_ty| {
        const ty = maybe_ty orelse continue;
        const ty_f = eval.forceAll(self, depth, ty);
        switch (ty_f.*) {
            .rigid => |r| switch (r.head) {
                .inductive => |ind| {
                    const ind_name = ind.name;
                    if (isUnitInductive(self, ind_name)) {
                        return true;
                    }
                    if (self.env.canBeStruct(ind_name) and
                        (tryEtaStructV(self, depth, ind_name, x, y) or tryEtaStructV(self, depth, ind_name, y, x)))
                    {
                        return true;
                    }
                },
                else => {},
            },
            else => {},
        }
    }
    return false;
}

fn valueTypeOpt(self: *TypeChecker, depth: u32, v: V) ?V {
    switch (v.*) {
        .pi, .lam => return null,
        else => return eval.valueType(self, depth, v),
    }
}

fn isRigidOrUnfold(v: V) bool {
    return switch (v.*) {
        .rigid, .unfold => true,
        else => false,
    };
}

fn tryProofIrrelAt(self: *TypeChecker, depth: u32, x: V, y: V) bool {
    if (isLam(x) or isLam(y)) {
        return tryProofIrrelLam(self, depth, x, y);
    }
    if (!isRigidOrUnfold(x)) {
        return false;
    }
    if (!isRigidOrUnfold(y)) {
        return false;
    }
    const tx = eval.valueType(self, depth, x);
    if (!isPropType(self, depth, tx)) {
        return false;
    }
    const ty = eval.valueType(self, depth, y);
    if (!isPropType(self, depth, ty)) {
        return false;
    }
    return convTypesAt(self, depth, tx, ty);
}

pub fn isPropType(self: *TypeChecker, depth: u32, t: V) bool {
    if (levelOfType(self, depth, t)) |l| {
        return level.isZero(self.ctx, l);
    } else {
        return false;
    }
}

fn tryProofIrrelLam(self: *TypeChecker, depth: u32, x: V, y: V) bool {
    const lam_side = blk: {
        if (isLam(x)) {
            break :blk x;
        } else if (isLam(y)) {
            break :blk y;
        } else {
            return false;
        }
    };
    const domain = eval.lamDomain(self, depth, lam_side);
    const fresh = eval.mkBvarHc(self, depth, domain);
    const xb = eval.apply(self, depth + 1, x, fresh);
    const yb = eval.apply(self, depth + 1, y, fresh);
    return tryProofIrrelAt(self, depth + 1, xb, yb);
}

fn tryEtaStructV(self: *TypeChecker, depth: u32, ind_name: NamePtr, x: V, y: V) bool {
    const yname, const yspine = switch (y.*) {
        .rigid => |r| switch (r.head) {
            .ctor => |c| .{ c.name, r.spine },
            else => return false,
        },
        else => return false,
    };
    var inductive_name: NamePtr = undefined;
    var num_params: u16 = undefined;
    var num_fields: u16 = undefined;
    if (self.env.getConstructor(yname)) |cd| {
        inductive_name = cd.inductive_name;
        num_params = cd.num_params;
        num_fields = cd.num_fields;
    } else {
        return false;
    }
    if (inductive_name != ind_name) {
        return false;
    }
    const yargs = blk: {
        if (eval.spineApps(self, depth, yspine)) |v| {
            if (v.len == @as(usize, num_params) + @as(usize, num_fields)) {
                break :blk v;
            }
        }
        return false;
    };
    var i: usize = 0;
    while (i < @as(usize, num_fields)) : (i += 1) {
        const proj = eval.doProj(self, depth, ind_name, i, x);
        const rhs = yargs[@as(usize, num_params) + i];
        if (!conv(self, true, depth, proj, rhs)) {
            return false;
        }
    }
    return true;
}

fn isUnitInductive(self: *TypeChecker, ind_name: NamePtr) bool {
    const ind = self.env.getInductive(ind_name) orelse return false;
    if (ind.all_ctor_names.len != 1 or ind.num_indices != 0) {
        return false;
    }
    const ctor = self.env.getConstructor(ind.all_ctor_names[0]) orelse return false;
    return ctor.num_fields == 0;
}

fn convNat(self: *TypeChecker, comptime RIGID: bool, depth: u32, x: V, y: V) ?bool {
    if (!mayBeNat(self, x) and !mayBeNat(self, y)) {
        return null;
    }
    if (isNatLit(x) and isNatLit(y)) {
        return null;
    }
    const xz = valueIsNatZero(self, x);
    const yz = valueIsNatZero(self, y);
    if (xz and yz) {
        return true;
    }
    const px = valueNatPred(self, x);
    const py = valueNatPred(self, y);
    if (px) |a| {
        if (py) |b| {
            return conv(self, RIGID, depth, a, b);
        }
    }
    return null;
}

fn isNatLit(v: V) bool {
    return switch (v.*) {
        .nat_lit => true,
        else => false,
    };
}

fn mayBeNat(self: *TypeChecker, v: V) bool {
    switch (v.*) {
        .nat_lit => return true,
        .rigid => |r| switch (r.head) {
            .ctor => |c| {
                const nc = &self.ctx.export_file.name_cache;
                const name = c.name;
                return nameEqOpt(name, nc.nat_zero) or nameEqOpt(name, nc.nat_succ);
            },
            else => return false,
        },
        else => return false,
    }
}

fn nameEqOpt(name: NamePtr, opt: ?NamePtr) bool {
    if (opt) |o| {
        return name == o;
    }
    return false;
}

fn valueIsNatZero(self: *TypeChecker, v: V) bool {
    switch (v.*) {
        .rigid => |r| switch (r.head) {
            .ctor => |c| {
                const name = c.name;
                return nameEqOpt(name, self.ctx.export_file.name_cache.nat_zero) and r.spine.isEmpty();
            },
            else => return false,
        },
        .nat_lit => |nl| {
            return nl.ptr.asRef().eqlZero();
        },
        else => return false,
    }
}

fn valueNatPred(self: *TypeChecker, v: V) ?V {
    switch (v.*) {
        .rigid => |r| switch (r.head) {
            .ctor => |c| {
                const name = c.name;
                if (nameEqOpt(name, self.ctx.export_file.name_cache.nat_succ)) {
                    if (r.spine != &Spine.empty and r.spine.prev == &Spine.empty and r.spine.elim.isApp()) {
                        return r.spine.elim.appV();
                    }
                }
                return null;
            },
            else => return null,
        },
        .nat_lit => |nl| {
            const n = nl.ptr.asRef().*;
            if (n.eqlZero()) {
                return null;
            }
            const pred = TcCtx.allocBignum(self.ctx, nat.pred(n)) orelse return null;
            return value.mkNatlit(self.arena, pred);
        },
        else => return null,
    }
}

fn levelOfType(self: *TypeChecker, depth: u32, ty_in: V) ?LevelPtr {
    const ty = eval.forceThunk(self, depth, ty_in);
    switch (ty.*) {
        .sort => |s| {
            const sc = TcCtx.succ(self.ctx, s.level);
            return level.simplify(self.ctx, sc);
        },
        .pi => |p| {
            const l_dom = levelOfType(self, depth, p.domain) orelse return null;
            const fresh = eval.mkBvarHc(self, depth, p.domain);
            const cod = eval.applyClosure(self, depth + 1, &p.body, fresh, p.domain);
            const cod_f = eval.forceAll(self, depth + 1, cod);
            const l_cod = levelOfType(self, depth + 1, cod_f) orelse return null;
            const l = TcCtx.imax(self.ctx, l_dom, l_cod);
            return level.simplify(self.ctx, l);
        },
        .rigid => |r| switch (r.head) {
            .axiom, .ctor, .recursor, .quot_const, .inductive => |payload| {
                const n = payload.name;
                const ls = payload.levels;
                if (eval.constResultLevel(self, n, ls)) |l| {
                    return l;
                }
                const t = eval.valueType(self, depth, ty);
                const t_f = eval.forceAll(self, depth, t);
                switch (t_f.*) {
                    .sort => |s2| return level.simplify(self.ctx, s2.level),
                    else => return null,
                }
            },
            .b_var, .local => {
                const t = eval.valueType(self, depth, ty);
                const ty_f = eval.forceAll(self, depth, t);
                switch (ty_f.*) {
                    .sort => |s2| return level.simplify(self.ctx, s2.level),
                    else => return null,
                }
            },
        },
        .unfold => |u| {
            const t = eval.valueType(self, depth, ty);
            const t_f = eval.forceAll(self, depth, t);
            switch (t_f.*) {
                .sort => |s2| return level.simplify(self.ctx, s2.level),
                else => {},
            }
            return eval.constResultLevel(self, u.head.name, u.head.levels);
        },
        else => return null,
    }
}
