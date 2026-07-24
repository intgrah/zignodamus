const eval = @import("eval.zig");
const tc = @import("tc.zig");
const util = @import("util.zig");
const value = @import("value.zig");
const TcCtx = @import("TcCtx.zig");

const ExprPtr = @import("ptr.zig").ExprPtr;
const TypeChecker = tc.TypeChecker;
const S = value.S;
const V = value.V;

pub const QuoteMemo = @import("swiss_map.zig").FxHashMap(struct { usize, u32 }, ExprPtr);

const PlainQuote = struct {
    memo: *QuoteMemo,

    pub fn hook(_: *PlainQuote, _: *TypeChecker, _: u32, _: V) tc.Reject!?ExprPtr {
        return null;
    }
};

pub fn quote(self: *TypeChecker, depth: u32, v: V) ExprPtr {
    var plain = PlainQuote{ .memo = &self.tc_cache.quote_cache };
    return quoteWith(self, &plain, depth, v) catch unreachable;
}

pub fn quoteWith(self: *TypeChecker, hctx: anytype, depth: u32, v0: V) tc.Reject!ExprPtr {
    const v = eval.forceThunk(self, depth, v0);
    const key = .{ @intFromPtr(v), depth };
    if (hctx.memo.get(key)) |q| {
        return q;
    }
    const r: ExprPtr = blk: {
        if (try hctx.hook(self, depth, v)) |e| break :blk e;
        break :blk switch (v.*) {
            .sort => |s| TcCtx.mkSort(self.ctx, s.level),
            .nat_lit => |n| TcCtx.mkNatLit(self.ctx, n.ptr) orelse @panic("quote: nat literal without extension"),
            .str_lit => |s| TcCtx.mkStringLit(self.ctx, s.ptr) orelse @panic("quote: string literal without extension"),
            .rigid => |rg| rigid: {
                const head: ExprPtr = switch (rg.head) {
                    .b_var => |b| head: {
                        util.assert(b.lvl < depth);
                        break :head TcCtx.mkVar(self.ctx, @intCast(depth - 1 - b.lvl));
                    },
                    .axiom, .ctor, .recursor, .quot_const, .inductive => |nl| TcCtx.mkConst(self.ctx, nl.name, nl.levels),
                };
                break :rigid try quoteSpineWith(self, hctx, depth, head, rg.spine);
            },
            .unfold => |u| try quoteSpineWith(self, hctx, depth, TcCtx.mkConst(self.ctx, u.head.name, u.head.levels), u.spine),
            .lam => |l| lam: {
                const dom = eval.lamDomain(self, depth, v);
                const fresh = eval.mkBvarHc(self, depth, dom);
                const body = eval.applyClosure(self, depth + 1, &v.lam.body, fresh, dom);
                break :lam TcCtx.mkLambda(self.ctx, l.binder_name, l.binder_style, try quoteWith(self, hctx, depth, dom), try quoteWith(self, hctx, depth + 1, body));
            },
            .pi => |p| pi: {
                const fresh = eval.mkBvarHc(self, depth, p.domain);
                const body = eval.applyClosure(self, depth + 1, &v.pi.body, fresh, p.domain);
                break :pi TcCtx.mkPi(self.ctx, p.binder_name, p.binder_style, try quoteWith(self, hctx, depth, p.domain), try quoteWith(self, hctx, depth + 1, body));
            },
            .thunk => @panic("quote: thunk after force"),
        };
    };
    hctx.memo.put(util.smp_allocator, key, r) catch util.oom();
    return r;
}

pub fn quoteSpineWith(self: *TypeChecker, hctx: anytype, depth: u32, head: ExprPtr, s: S) tc.Reject!ExprPtr {
    if (s.isEmpty()) {
        return head;
    }
    const prefix = try quoteSpineWith(self, hctx, depth, head, s.prev);
    if (s.elim.isApp()) {
        return TcCtx.mkApp(self.ctx, prefix, try quoteWith(self, hctx, depth, s.elim.appV()));
    }
    return TcCtx.mkProj(self.ctx, s.elim.projTyName(), s.elim.projIdx(), prefix);
}
