const std = @import("std");
const interner = @import("interner.zig");
const name = @import("name.zig");
const ptr = @import("ptr.zig");
const util = @import("util.zig");
const Config = @import("export_file.zig").Config;
const FxHashMap = @import("swiss_map.zig").FxHashMap;
const hash64 = @import("hash.zig").hash64;
const NamePtr = ptr.NamePtr;
const StringPtr = ptr.StringPtr;
const smp_allocator = util.smp_allocator;

const Dag = @This();

names: interner.NameInterner,
levels: interner.LevelInterner,
exprs: interner.ExprInterner,
uparams: interner.LevelsInterner,
strings: interner.StringInterner,
bignums: ?interner.BigUintInterner,

pub fn init(config: *const Config) Dag {
    return .{
        .names = .empty,
        .levels = .empty,
        .exprs = .empty,
        .uparams = .empty,
        .strings = .empty,
        .bignums = if (config.nat_extension) .empty else null,
    };
}

pub fn deinit(self: *Dag) void {
    self.names.deinit();
    self.levels.deinit();
    self.exprs.deinit();
    self.uparams.deinit();
    self.strings.deinit();
    if (self.bignums) |*b| b.deinit();
}

fn getStringPtr(self: *const Dag, s: []const u8) ?StringPtr {
    if (self.strings.get(&s)) |r| return StringPtr.global(r);
    return null;
}

fn findName(self: *const Dag, anon: NamePtr, dot_separated_name: []const u8) ?NamePtr {
    var pfx = anon;
    var it = std.mem.splitScalar(u8, dot_separated_name, '.');
    while (it.next()) |s| {
        if (std.fmt.parseInt(u64, s, 10)) |parsed_num| {
            const h = hash64(.{ name.num_hash, pfx, parsed_num });
            const probe = name.Name{ .hash = h, .kind = .{ .num = .{ .pfx = pfx, .n = parsed_num } } };
            if (self.names.get(&probe)) |r| {
                pfx = NamePtr.global(r);
                continue;
            }
        } else |_| {
            if (self.getStringPtr(s)) |sfx| {
                const h = hash64(.{ name.str_hash, pfx, sfx });
                const probe = name.Name{ .hash = h, .kind = .{ .str = .{ .pfx = pfx, .sfx = sfx } } };
                if (self.names.get(&probe)) |r| {
                    pfx = NamePtr.global(r);
                    continue;
                }
            }
        }
        return null;
    }
    return pfx;
}

pub fn mkNameCache(self: *const Dag, anon: NamePtr) NameCache {
    var cache: NameCache = .{
        .quot = self.findName(anon, "Quot"),
        .quot_mk = self.findName(anon, "Quot.mk"),
        .quot_lift = self.findName(anon, "Quot.lift"),
        .quot_ind = self.findName(anon, "Quot.ind"),
        .string = self.findName(anon, "String"),
        .string_of_list = self.findName(anon, "String.ofList"),
        .nat = self.findName(anon, "Nat"),
        .nat_zero = self.findName(anon, "Nat.zero"),
        .nat_succ = self.findName(anon, "Nat.succ"),
        .nat_add = self.findName(anon, "Nat.add"),
        .nat_sub = self.findName(anon, "Nat.sub"),
        .nat_mul = self.findName(anon, "Nat.mul"),
        .nat_pow = self.findName(anon, "Nat.pow"),
        .nat_mod = self.findName(anon, "Nat.mod"),
        .nat_div = self.findName(anon, "Nat.div"),
        .nat_div_go = self.findName(anon, "Nat.div.go"),
        .nat_mod_core_go = self.findName(anon, "Nat.modCore.go"),
        .nat_beq = self.findName(anon, "Nat.beq"),
        .nat_ble = self.findName(anon, "Nat.ble"),
        .nat_gcd = self.findName(anon, "Nat.gcd"),
        .nat_xor = self.findName(anon, "Nat.xor"),
        .nat_land = self.findName(anon, "Nat.land"),
        .nat_lor = self.findName(anon, "Nat.lor"),
        .nat_shl = self.findName(anon, "Nat.shiftLeft"),
        .nat_shr = self.findName(anon, "Nat.shiftRight"),
        .bool_true = self.findName(anon, "Bool.true"),
        .bool_false = self.findName(anon, "Bool.false"),
        .char = self.findName(anon, "Char"),
        .char_of_nat = self.findName(anon, "Char.ofNat"),
        .list = self.findName(anon, "List"),
        .list_nil = self.findName(anon, "List.nil"),
        .list_cons = self.findName(anon, "List.cons"),
        .nat_red = .empty,
    };
    putNatRed(&cache, cache.nat_succ, .succ);
    putNatRed(&cache, cache.nat_div_go, .div_go);
    putNatRed(&cache, cache.nat_mod_core_go, .mod_core_go);
    putNatRed(&cache, cache.nat_add, .add);
    putNatRed(&cache, cache.nat_sub, .sub);
    putNatRed(&cache, cache.nat_mul, .mul);
    putNatRed(&cache, cache.nat_pow, .pow);
    putNatRed(&cache, cache.nat_mod, .mod);
    putNatRed(&cache, cache.nat_div, .div);
    putNatRed(&cache, cache.nat_beq, .beq);
    putNatRed(&cache, cache.nat_ble, .ble);
    putNatRed(&cache, cache.nat_gcd, .gcd);
    putNatRed(&cache, cache.nat_land, .land);
    putNatRed(&cache, cache.nat_lor, .lor);
    putNatRed(&cache, cache.nat_xor, .xor);
    putNatRed(&cache, cache.nat_shl, .shl);
    putNatRed(&cache, cache.nat_shr, .shr);
    return cache;
}

fn putNatRed(cache: *NameCache, n: ?NamePtr, k: NatRed) void {
    if (n) |nn| cache.nat_red.put(smp_allocator, nn, k) catch util.oom();
}

pub const NatRed = enum {
    succ,
    div_go,
    mod_core_go,
    add,
    sub,
    mul,
    pow,
    mod,
    div,
    beq,
    ble,
    gcd,
    land,
    lor,
    xor,
    shl,
    shr,
};

pub const NameCache = struct {
    quot: ?NamePtr,
    quot_mk: ?NamePtr,
    quot_lift: ?NamePtr,
    quot_ind: ?NamePtr,
    nat: ?NamePtr,
    nat_zero: ?NamePtr,
    nat_succ: ?NamePtr,
    nat_add: ?NamePtr,
    nat_sub: ?NamePtr,
    nat_mul: ?NamePtr,
    nat_pow: ?NamePtr,
    nat_mod: ?NamePtr,
    nat_div: ?NamePtr,
    nat_div_go: ?NamePtr,
    nat_mod_core_go: ?NamePtr,
    nat_beq: ?NamePtr,
    nat_ble: ?NamePtr,
    nat_gcd: ?NamePtr,
    nat_xor: ?NamePtr,
    nat_land: ?NamePtr,
    nat_lor: ?NamePtr,
    nat_shr: ?NamePtr,
    nat_shl: ?NamePtr,
    string: ?NamePtr,
    string_of_list: ?NamePtr,
    bool_false: ?NamePtr,
    bool_true: ?NamePtr,
    char: ?NamePtr,
    char_of_nat: ?NamePtr,
    list: ?NamePtr,
    list_nil: ?NamePtr,
    list_cons: ?NamePtr,
    nat_red: FxHashMap(NamePtr, NatRed),
};
