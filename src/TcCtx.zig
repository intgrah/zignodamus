const std = @import("std");
const Arena = @import("Arena.zig");
const expr = @import("expr.zig");
const level = @import("level.zig");
const name = @import("name.zig");
const ptr = @import("ptr.zig");
const util = @import("util.zig");
const Dag = @import("Dag.zig");
const ExportFile = @import("export_file.zig").ExportFile;
const FxHashMap = @import("swiss_map.zig").FxHashMap;
const BigUint = @import("nat.zig").BigUint;
const StringPtr = ptr.StringPtr;
const NamePtr = ptr.NamePtr;
const LevelPtr = ptr.LevelPtr;
const ExprPtr = ptr.ExprPtr;
const BigUintPtr = ptr.BigUintPtr;
const LevelsPtr = ptr.LevelsPtr;
const smp_allocator = util.smp_allocator;

const TcCtx = @This();

export_file: *const ExportFile,
arena: *Arena,
bump: std.mem.Allocator,
dag: Dag,
level_cache: LevelCache,

pub const LevelCache = struct {
    simplify_cache: FxHashMap(LevelPtr, LevelPtr) = .empty,

    pub const empty: LevelCache = .{};

    pub fn deinit(self: *LevelCache) void {
        inline for (@typeInfo(LevelCache).@"struct".fields) |f| {
            @field(self, f.name).deinit(smp_allocator);
        }
    }
};

pub fn init(export_file: *const ExportFile, ar: *Arena) TcCtx {
    const dag = Dag.init(&export_file.config);
    return .{
        .export_file = export_file,
        .arena = ar,
        .bump = ar.bumpAllocator(),
        .dag = dag,
        .level_cache = .empty,
    };
}

pub fn deinit(self: *TcCtx) void {
    self.dag.deinit();
    self.level_cache.deinit();
}

fn isExprLocalOnly(e: *const expr.Expr) bool {
    return switch (e.kind) {
        .string_lit => |x| x.ptr.isLocal(),
        .nat_lit => |x| x.ptr.isLocal(),
        .proj => |x| x.ty_name.isLocal() or x.structure.isLocal(),
        .@"var" => false,
        .sort => |x| x.level.isLocal(),
        .@"const" => |x| x.name.isLocal() or x.levels.isLocal(),
        .app => |x| x.fun.isLocal() or x.arg.isLocal(),
        .pi => |x| x.binder_name.isLocal() or x.binderType().isLocal() or x.body.isLocal(),
        .lambda => |x| x.binder_name.isLocal() or x.binderType().isLocal() or x.body.isLocal(),
        .let => |x| x.data.binder_name.isLocal() or x.data.binder_type.isLocal() or x.data.val.isLocal() or x.data.body.isLocal(),
    };
}

pub fn allocName(self: *TcCtx, n: name.Name) NamePtr {
    if (self.export_file.dag.names.get(&n)) |r| {
        return NamePtr.global(r);
    }
    return NamePtr.local(self.dag.names.intern(self.arena, n));
}

pub fn allocLevel(self: *TcCtx, l: level.Level) LevelPtr {
    if (self.export_file.dag.levels.get(&l)) |r| {
        return LevelPtr.global(r);
    }
    return LevelPtr.local(self.dag.levels.intern(self.arena, l));
}

pub fn allocExpr(self: *TcCtx, e: *const expr.Expr) ExprPtr {
    if (self.dag.exprs.get(e)) |r| {
        return ExprPtr.local(r);
    }
    if (!isExprLocalOnly(e)) {
        if (self.export_file.dag.exprs.get(e)) |r| {
            return ExprPtr.global(r);
        }
    }
    return ExprPtr.local(self.dag.exprs.insert(self.arena, e));
}

pub fn allocString(self: *TcCtx, s: []const u8) StringPtr {
    if (self.export_file.dag.strings.get(&s)) |r| {
        return StringPtr.global(r);
    }
    return StringPtr.local(self.dag.strings.intern(self.arena, s));
}

pub fn allocBignum(self: *TcCtx, n: BigUint) ?BigUintPtr {
    if (self.export_file.dag.bignums) |*global| {
        if (global.get(&n)) |r| {
            var m = n;
            m.deinit();
            return BigUintPtr.global(r);
        }
    }
    if (self.dag.bignums) |*local_interner| {
        return BigUintPtr.local(local_interner.intern(self.arena, n));
    }
    var m = n;
    m.deinit();
    return null;
}

pub fn allocLevels(self: *TcCtx, ls: []const LevelPtr) LevelsPtr {
    if (self.export_file.dag.uparams.get(ls)) |r| {
        return LevelsPtr.global(r);
    }
    return LevelsPtr.local(self.dag.uparams.intern(self.arena, ls));
}

pub fn anonymous(self: *const TcCtx) NamePtr {
    return self.export_file.anon;
}

pub fn str(self: *TcCtx, pfx: NamePtr, sfx: StringPtr) NamePtr {
    return allocName(self, .mk(.{ .str = .{ .pfx = pfx, .sfx = sfx } }));
}

pub fn str1(self: *TcCtx, s: []const u8) NamePtr {
    const anon = allocName(self, name.Name.anon);
    const sp = allocString(self, s);
    return str(self, anon, sp);
}

pub fn str2(self: *TcCtx, s1: []const u8, s2: []const u8) NamePtr {
    const sp1 = allocString(self, s1);
    const sp2 = allocString(self, s2);
    const n0 = anonymous(self);
    const n1 = str(self, n0, sp1);
    return str(self, n1, sp2);
}

pub fn zero(self: *const TcCtx) LevelPtr {
    return self.export_file.zero;
}

pub fn num(self: *TcCtx, pfx: NamePtr, sfx: u64) NamePtr {
    return allocName(self, .mk(.{ .num = .{ .pfx = pfx, .n = sfx } }));
}

pub fn succ(self: *TcCtx, l: LevelPtr) LevelPtr {
    return allocLevel(self, .mk(.{ .succ = l }));
}

pub fn max(self: *TcCtx, l: LevelPtr, r: LevelPtr) LevelPtr {
    return allocLevel(self, .mk(.{ .max = .{ .l = l, .r = r } }));
}

pub fn imax(self: *TcCtx, l: LevelPtr, r: LevelPtr) LevelPtr {
    return allocLevel(self, .mk(.{ .imax = .{ .l = l, .r = r } }));
}

pub fn param(self: *TcCtx, n: NamePtr) LevelPtr {
    return allocLevel(self, .mk(.{ .param = n }));
}

pub fn mkVar(self: *TcCtx, dbj_idx: u16) ExprPtr {
    const e: expr.Expr = .mk(.{ .@"var" = .{ .dbj_idx = dbj_idx } });
    return allocExpr(self, &e);
}

pub fn mkSort(self: *TcCtx, lvl: LevelPtr) ExprPtr {
    const e: expr.Expr = .mk(.{ .sort = .{ .level = lvl } });
    return allocExpr(self, &e);
}

pub fn mkConst(self: *TcCtx, n: NamePtr, levels: LevelsPtr) ExprPtr {
    const e: expr.Expr = .mk(.{ .@"const" = .{ .name = n, .levels = levels } });
    return allocExpr(self, &e);
}

pub fn mkApp(self: *TcCtx, fun: ExprPtr, arg: ExprPtr) ExprPtr {
    const e: expr.Expr = .mk(.{ .app = .{
        .fun = fun,
        .arg = arg,
    } });
    return allocExpr(self, &e);
}

pub fn mkLambda(
    self: *TcCtx,
    binder_name: NamePtr,
    binder_style: expr.BinderStyle,
    binder_type: ExprPtr,
    body: ExprPtr,
) ExprPtr {
    const e: expr.Expr = .mk(.{ .lambda = .mk(binder_name, binder_style, binder_type, body) });
    return allocExpr(self, &e);
}

pub fn mkPi(
    self: *TcCtx,
    binder_name: NamePtr,
    binder_style: expr.BinderStyle,
    binder_type: ExprPtr,
    body: ExprPtr,
) ExprPtr {
    const e: expr.Expr = .mk(.{ .pi = .mk(binder_name, binder_style, binder_type, body) });
    return allocExpr(self, &e);
}

pub fn mkProj(self: *TcCtx, ty_name: NamePtr, idx: usize, structure: ExprPtr) ExprPtr {
    const e: expr.Expr = .mk(.{ .proj = .{
        .ty_name = ty_name,
        .idx = idx,
        .structure = structure,
    } });
    return allocExpr(self, &e);
}

pub fn mkStringLit(self: *TcCtx, string_ptr: StringPtr) ?ExprPtr {
    if (!self.export_file.config.string_extension) {
        return null;
    }
    const e: expr.Expr = .mk(.{ .string_lit = .{ .ptr = string_ptr } });
    return allocExpr(self, &e);
}

pub fn mkNatLit(self: *TcCtx, num_ptr: BigUintPtr) ?ExprPtr {
    if (!self.export_file.config.nat_extension) {
        return null;
    }
    const e: expr.Expr = .mk(.{ .nat_lit = .{ .ptr = num_ptr } });
    return allocExpr(self, &e);
}
