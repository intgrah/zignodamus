const std = @import("std");
const interner = @import("interner.zig");
const name = @import("name.zig");
const ptr = @import("ptr.zig");
const util = @import("util.zig");
const Config = @import("export_file.zig").Config;
const FxHashMap = @import("swiss_map.zig").FxHashMap;
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
            const probe: name.Name = .mk(.{ .num = .{ .pfx = pfx, .n = parsed_num } });
            if (self.names.get(&probe)) |r| {
                pfx = NamePtr.global(r);
                continue;
            }
        } else |_| {
            if (self.getStringPtr(s)) |sfx| {
                const probe: name.Name = .mk(.{ .str = .{ .pfx = pfx, .sfx = sfx } });
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

const name_cache_entries = [_]struct { [:0]const u8, []const u8 }{
    .{ "quot", "Quot" },
    .{ "quot_mk", "Quot.mk" },
    .{ "quot_lift", "Quot.lift" },
    .{ "quot_ind", "Quot.ind" },
    .{ "string", "String" },
    .{ "string_of_list", "String.ofList" },
    .{ "nat", "Nat" },
    .{ "nat_zero", "Nat.zero" },
    .{ "nat_succ", "Nat.succ" },
    .{ "nat_add", "Nat.add" },
    .{ "nat_sub", "Nat.sub" },
    .{ "nat_mul", "Nat.mul" },
    .{ "nat_pow", "Nat.pow" },
    .{ "nat_mod", "Nat.mod" },
    .{ "nat_div", "Nat.div" },
    .{ "nat_div_go", "Nat.div.go" },
    .{ "nat_mod_core_go", "Nat.modCore.go" },
    .{ "nat_beq", "Nat.beq" },
    .{ "nat_ble", "Nat.ble" },
    .{ "nat_gcd", "Nat.gcd" },
    .{ "nat_xor", "Nat.xor" },
    .{ "nat_land", "Nat.land" },
    .{ "nat_lor", "Nat.lor" },
    .{ "nat_shl", "Nat.shiftLeft" },
    .{ "nat_shr", "Nat.shiftRight" },
    .{ "bool_true", "Bool.true" },
    .{ "bool_false", "Bool.false" },
    .{ "char", "Char" },
    .{ "char_of_nat", "Char.ofNat" },
    .{ "list", "List" },
    .{ "list_nil", "List.nil" },
    .{ "list_cons", "List.cons" },
};

pub fn mkNameCache(self: *const Dag, anon: NamePtr) NameCache {
    var cache: NameCache = undefined;
    inline for (name_cache_entries) |entry| {
        @field(cache, entry[0]) = self.findName(anon, entry[1]);
    }
    cache.nat_red = .empty;
    inline for (comptime std.meta.tags(NatRed)) |t| {
        putNatRed(&cache, @field(cache, "nat_" ++ @tagName(t)), t);
    }
    return cache;
}

fn putNatRed(cache: *NameCache, n: ?NamePtr, k: NatRed) void {
    if (n) |nn| {
        cache.nat_red.put(smp_allocator, nn, k) catch util.oom();
        name.setNatRed(nn, @intFromEnum(k));
    }
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

pub const NameCache = blk: {
    var names: [name_cache_entries.len + 1][:0]const u8 = undefined;
    var types: [name_cache_entries.len + 1]type = undefined;
    for (names[0..name_cache_entries.len], types[0..name_cache_entries.len], name_cache_entries) |*n, *t, entry| {
        n.* = entry[0];
        t.* = ?NamePtr;
    }
    names[name_cache_entries.len] = "nat_red";
    types[name_cache_entries.len] = FxHashMap(NamePtr, NatRed);
    break :blk @Struct(.auto, null, &names, &types, &@splat(.{}));
};
