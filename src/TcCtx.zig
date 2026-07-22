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
const hash64 = @import("hash.zig").hash64;
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
dbj_level_counter: u16,
unique_counter: u32,
expr_cache: ExprCache,

pub const ExprCache = struct {
    inst_cache: FxHashMap(struct { ExprPtr, u16 }, ExprPtr) = .empty,
    subst_cache: FxHashMap(struct { ExprPtr, LevelsPtr, LevelsPtr }, ExprPtr) = .empty,
    dsubst_cache: FxHashMap(struct { ExprPtr, LevelsPtr, LevelsPtr }, ExprPtr) = .empty,
    abstr_cache: FxHashMap(struct { ExprPtr, u16 }, ExprPtr) = .empty,
    abstr_cache_levels: FxHashMap(struct { ExprPtr, u16, u16 }, ExprPtr) = .empty,
    simplify_cache: FxHashMap(LevelPtr, LevelPtr) = .empty,

    pub const empty: ExprCache = .{};

    pub fn deinit(self: *ExprCache) void {
        inline for (@typeInfo(ExprCache).@"struct".fields) |f| {
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
        .dbj_level_counter = 0,
        .unique_counter = 0,
        .expr_cache = .empty,
    };
}

pub fn deinit(self: *TcCtx) void {
    self.dag.deinit();
    self.expr_cache.deinit();
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
        .pi => |x| x.binder_name.isLocal() or x.binder_type.isLocal() or x.body.isLocal(),
        .lambda => |x| x.binder_name.isLocal() or x.binder_type.isLocal() or x.body.isLocal(),
        .let => |x| x.data.binder_name.isLocal() or x.data.binder_type.isLocal() or x.data.val.isLocal() or x.data.body.isLocal(),
        .local => true,
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
    const hash = hash64(.{ name.str_hash, pfx, sfx });
    return allocName(self, name.Name{ .hash = hash, .kind = .{ .str = .{ .pfx = pfx, .sfx = sfx } } });
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
    const hash = hash64(.{ name.num_hash, pfx, sfx });
    return allocName(self, name.Name{ .hash = hash, .kind = .{ .num = .{ .pfx = pfx, .n = sfx } } });
}

pub fn succ(self: *TcCtx, l: LevelPtr) LevelPtr {
    const hash = hash64(.{ level.succ_hash, l });
    return allocLevel(self, level.Level{ .hash = hash, .kind = .{ .succ = l } });
}

pub fn max(self: *TcCtx, l: LevelPtr, r: LevelPtr) LevelPtr {
    const hash = hash64(.{ level.max_hash, l, r });
    return allocLevel(self, level.Level{ .hash = hash, .kind = .{ .max = .{ .l = l, .r = r } } });
}

pub fn imax(self: *TcCtx, l: LevelPtr, r: LevelPtr) LevelPtr {
    const hash = hash64(.{ level.imax_hash, l, r });
    return allocLevel(self, level.Level{ .hash = hash, .kind = .{ .imax = .{ .l = l, .r = r } } });
}

pub fn param(self: *TcCtx, n: NamePtr) LevelPtr {
    const hash = hash64(.{ level.param_hash, n });
    return allocLevel(self, level.Level{ .hash = hash, .kind = .{ .param = n } });
}

pub fn mkVar(self: *TcCtx, dbj_idx: u16) ExprPtr {
    const hash = hash64(.{ expr.var_hash, dbj_idx });
    const e = expr.Expr{ .hash = hash, .kind = .{ .@"var" = .{ .dbj_idx = dbj_idx } } };
    return allocExpr(self, &e);
}

pub fn mkSort(self: *TcCtx, lvl: LevelPtr) ExprPtr {
    const hash = hash64(.{ expr.sort_hash, lvl });
    const e = expr.Expr{ .hash = hash, .kind = .{ .sort = .{ .level = lvl } } };
    return allocExpr(self, &e);
}

pub fn mkConst(self: *TcCtx, n: NamePtr, levels: LevelsPtr) ExprPtr {
    const hash = hash64(.{ expr.const_hash, n, levels });
    const e = expr.Expr{ .hash = hash, .kind = .{ .@"const" = .{ .name = n, .levels = levels } } };
    return allocExpr(self, &e);
}

pub fn mkApp(self: *TcCtx, fun: ExprPtr, arg: ExprPtr) ExprPtr {
    const hash = hash64(.{ expr.app_hash, fun, arg });
    const num_loose_bvars = @max(expr.numLooseBvars(fun), expr.numLooseBvars(arg));
    const has_fvars = expr.hasFvars(fun) or expr.hasFvars(arg);
    const e = expr.Expr{ .hash = hash, .kind = .{ .app = .{
        .fun = fun,
        .arg = arg,
        .num_loose_bvars = num_loose_bvars,
        .has_fvars = has_fvars,
    } } };
    return allocExpr(self, &e);
}

pub fn mkLambda(
    self: *TcCtx,
    binder_name: NamePtr,
    binder_style: expr.BinderStyle,
    binder_type: ExprPtr,
    body: ExprPtr,
) ExprPtr {
    const hash = hash64(.{ expr.lambda_hash, binder_name, binder_style, binder_type, body });
    const num_loose_bvars = @max(expr.numLooseBvars(binder_type), (expr.numLooseBvars(body) -| 1));
    const has_fvars = expr.hasFvars(binder_type) or expr.hasFvars(body);
    const e = expr.Expr{ .hash = hash, .kind = .{ .lambda = .{
        .binder_name = binder_name,
        .binder_style = binder_style,
        .binder_type = binder_type,
        .body = body,
        .num_loose_bvars = num_loose_bvars,
        .has_fvars = has_fvars,
    } } };
    return allocExpr(self, &e);
}

pub fn mkPi(
    self: *TcCtx,
    binder_name: NamePtr,
    binder_style: expr.BinderStyle,
    binder_type: ExprPtr,
    body: ExprPtr,
) ExprPtr {
    const hash = hash64(.{ expr.pi_hash, binder_name, binder_style, binder_type, body });
    const num_loose_bvars = @max(expr.numLooseBvars(binder_type), (expr.numLooseBvars(body) -| 1));
    const has_fvars = expr.hasFvars(binder_type) or expr.hasFvars(body);
    const e = expr.Expr{ .hash = hash, .kind = .{ .pi = .{
        .binder_name = binder_name,
        .binder_style = binder_style,
        .binder_type = binder_type,
        .body = body,
        .num_loose_bvars = num_loose_bvars,
        .has_fvars = has_fvars,
    } } };
    return allocExpr(self, &e);
}

pub fn mkLet(
    self: *TcCtx,
    binder_name: NamePtr,
    binder_type: ExprPtr,
    val: ExprPtr,
    body: ExprPtr,
    nondep: bool,
) ExprPtr {
    const hash = hash64(.{ expr.let_hash, binder_name, binder_type, val, body, nondep });
    const num_loose_bvars = @max(
        expr.numLooseBvars(binder_type),
        @max(expr.numLooseBvars(val), (expr.numLooseBvars(body) -| 1)),
    );
    const has_fvars = expr.hasFvars(binder_type) or expr.hasFvars(val) or expr.hasFvars(body);
    const d = self.arena.create(expr.LetData);
    d.* = .{
        .binder_name = binder_name,
        .binder_type = binder_type,
        .val = val,
        .body = body,
        .num_loose_bvars = num_loose_bvars,
        .has_fvars = has_fvars,
        .nondep = nondep,
    };
    const e = expr.Expr{ .hash = hash, .kind = .{ .let = .{ .data = d } } };
    return allocExpr(self, &e);
}

pub fn mkProj(self: *TcCtx, ty_name: NamePtr, idx: usize, structure: ExprPtr) ExprPtr {
    const hash = hash64(.{ expr.proj_hash, ty_name, idx, structure });
    const num_loose_bvars = expr.numLooseBvars(structure);
    const has_fvars = expr.hasFvars(structure);
    const e = expr.Expr{ .hash = hash, .kind = .{ .proj = .{
        .ty_name = ty_name,
        .idx = idx,
        .structure = structure,
        .num_loose_bvars = num_loose_bvars,
        .has_fvars = has_fvars,
    } } };
    return allocExpr(self, &e);
}

pub fn mkStringLit(self: *TcCtx, string_ptr: StringPtr) ?ExprPtr {
    if (!self.export_file.config.string_extension) {
        return null;
    }
    const hash = hash64(.{ expr.string_lit_hash, string_ptr });
    const e = expr.Expr{ .hash = hash, .kind = .{ .string_lit = .{ .ptr = string_ptr } } };
    return allocExpr(self, &e);
}

pub fn mkStringLitQuick(self: *TcCtx, s: []const u8) ?ExprPtr {
    if (!self.export_file.config.string_extension) {
        return null;
    }
    const string_ptr = allocString(self, s);
    return mkStringLit(self, string_ptr);
}

pub fn mkNatLit(self: *TcCtx, num_ptr: BigUintPtr) ?ExprPtr {
    if (!self.export_file.config.nat_extension) {
        return null;
    }
    const hash = hash64(.{ expr.nat_lit_hash, num_ptr });
    const e = expr.Expr{ .hash = hash, .kind = .{ .nat_lit = .{ .ptr = num_ptr } } };
    return allocExpr(self, &e);
}

pub fn mkNatLitQuick(self: *TcCtx, n: BigUint) ?ExprPtr {
    const num_ptr = allocBignum(self, n) orelse return null;
    return mkNatLit(self, num_ptr);
}

pub fn mkDbjLevel(
    self: *TcCtx,
    binder_name: NamePtr,
    binder_style: expr.BinderStyle,
    binder_type: ExprPtr,
) ExprPtr {
    const lvl = self.dbj_level_counter;
    self.dbj_level_counter += 1;
    const id = expr.FVarId{ .dbj_level = lvl };
    const hash = hash64(.{ expr.local_hash, binder_name, binder_style, binder_type, id });
    const e = expr.Expr{ .hash = hash, .kind = .{ .local = .{
        .binder_name = binder_name,
        .binder_style = binder_style,
        .binder_type = binder_type,
        .id = id,
    } } };
    return allocExpr(self, &e);
}

pub fn remakeDbjLevel(
    self: *TcCtx,
    binder_name: NamePtr,
    binder_style: expr.BinderStyle,
    binder_type: ExprPtr,
    lvl: u16,
) ExprPtr {
    const id = expr.FVarId{ .dbj_level = lvl };
    const hash = hash64(.{ expr.local_hash, binder_name, binder_style, binder_type, id });
    const e = expr.Expr{ .hash = hash, .kind = .{ .local = .{
        .binder_name = binder_name,
        .binder_style = binder_style,
        .binder_type = binder_type,
        .id = id,
    } } };
    return allocExpr(self, &e);
}

pub fn mkUnique(
    self: *TcCtx,
    binder_name: NamePtr,
    binder_style: expr.BinderStyle,
    binder_type: ExprPtr,
) ExprPtr {
    const unique_id = self.unique_counter;
    self.unique_counter += 1;
    const id = expr.FVarId{ .unique = unique_id };
    const hash = hash64(.{ expr.local_hash, binder_name, binder_style, binder_type, id });
    const e = expr.Expr{ .hash = hash, .kind = .{ .local = .{
        .binder_name = binder_name,
        .binder_style = binder_style,
        .binder_type = binder_type,
        .id = id,
    } } };
    return allocExpr(self, &e);
}

pub fn replaceDbjLevel(self: *TcCtx, e: ExprPtr) void {
    switch (e.asRef().kind) {
        .local => |loc| switch (loc.id) {
            .dbj_level => |lvl| {
                std.debug.assert(lvl + 1 == self.dbj_level_counter);
                self.dbj_level_counter -= 1;
            },
            else => @panic("replace_dbj_level didn't get a DbjLevel Local"),
        },
        else => @panic("replace_dbj_level didn't get a Local"),
    }
}

pub fn fvarToBvar(self: *TcCtx, num_open_binders: u16, dbj_level: u16) ExprPtr {
    return mkVar(self, (num_open_binders - dbj_level) - 1);
}
