const std = @import("std");
const name = @import("name.zig");
const ptr = @import("ptr.zig");
const swiss_map = @import("swiss_map.zig");

const Name = name.Name;
const NamePtr = ptr.NamePtr;
const LevelsPtr = ptr.LevelsPtr;
const ExprPtr = ptr.ExprPtr;
const FxIndexMap = swiss_map.FxIndexMap;

pub const ReducibilityHint = union(enum) {
    opaque_: void,
    regular: u16,
    abbrev: void,

    pub fn isLt(self: ReducibilityHint, other: ReducibilityHint) bool {
        return switch (self) {
            .opaque_ => other != .opaque_,
            .abbrev => false,
            .regular => |h| switch (other) {
                .opaque_ => false,
                .abbrev => true,
                .regular => |o| h < o,
            },
        };
    }
};

pub const DeclarInfo = struct {
    name: NamePtr,
    uparams: LevelsPtr,
    ty: ExprPtr,
};

pub const RecRule = struct {
    ctor_name: NamePtr,
    ctor_telescope_size_wo_params: u16,
    val: ExprPtr,
};

pub const Declar = union(enum) {
    axiom: struct { info: DeclarInfo },
    quot: struct { info: DeclarInfo },
    theorem: struct { info: DeclarInfo, val: ExprPtr },
    definition: struct { info: DeclarInfo, val: ExprPtr, hint: ReducibilityHint },
    opaque_: struct { info: DeclarInfo, val: ExprPtr },
    inductive: InductiveData,
    constructor: ConstructorData,
    recursor: RecursorData,

    pub fn info(self: *const Declar) *const DeclarInfo {
        return switch (self.*) {
            .axiom => |*d| &d.info,
            .quot => |*d| &d.info,
            .theorem => |*d| &d.info,
            .definition => |*d| &d.info,
            .opaque_ => |*d| &d.info,
            .inductive => |*d| &d.info,
            .constructor => |*d| &d.info,
            .recursor => |*d| &d.info,
        };
    }
};

pub const InductiveData = struct {
    info: DeclarInfo,
    is_recursive: bool,
    is_nested: bool,
    num_params: u16,
    num_indices: u16,
    all_ind_names: []const NamePtr,
    all_ctor_names: []const NamePtr,
};

pub const ConstructorData = struct {
    info: DeclarInfo,
    inductive_name: NamePtr,
    ctor_idx: u16,
    num_params: u16,
    num_fields: u16,
};

pub const RecursorData = struct {
    info: DeclarInfo,
    all_inductives: []const NamePtr,
    num_params: u16,
    num_indices: u16,
    num_motives: u16,
    num_minors: u16,
    rec_rules: []const RecRule,
    is_k: bool,

    pub fn majorIdx(self: *const RecursorData) usize {
        return @as(usize, self.num_params + self.num_motives + self.num_minors + self.num_indices);
    }
};

pub const EnvLimit = union(enum) {
    empty: void,
    by_index: usize,
    by_name: NamePtr,
};

pub const DeclarMap = FxIndexMap(NamePtr, Declar);

pub const Env = struct {
    declars: *const DeclarMap,
    temp_declars: ?*const DeclarMap,
    cutoff: usize,

    pub fn init(declars: *const DeclarMap, limit: EnvLimit) Env {
        return initWithTempExt(declars, null, limit);
    }

    pub fn initWithTempExt(
        declars: *const DeclarMap,
        temp_declars: ?*const DeclarMap,
        limit: EnvLimit,
    ) Env {
        const cutoff = switch (limit) {
            .empty => 0,
            .by_index => |idx| idx,
            .by_name => |n| switch (name.declIdx(n)) {
                Name.no_decl => 0,
                else => |i| @as(usize, i),
            },
        };
        return Env{ .declars = declars, .cutoff = cutoff, .temp_declars = temp_declars };
    }

    pub fn getDeclar(self: *const Env, n: NamePtr) ?*const Declar {
        if (self.temp_declars) |ext| {
            if (ext.getPtr(n)) |d| return d;
        }
        return self.getOldDeclar(n);
    }

    pub fn getDeclarAt(self: *const Env, n: NamePtr, idx: u32) ?*const Declar {
        if (self.temp_declars) |ext| {
            if (ext.getPtr(n)) |d| return d;
        }
        if (@as(usize, idx) < self.cutoff) {
            return &self.declars.values()[idx];
        }
        return null;
    }

    pub fn getTempDeclar(self: *const Env, n: NamePtr) ?*const Declar {
        if (self.temp_declars) |ext| {
            if (ext.getPtr(n)) |d| return d;
        }
        return null;
    }

    pub fn getOldDeclar(self: *const Env, n: NamePtr) ?*const Declar {
        const idx: usize = name.declIdx(n);
        if (idx < self.cutoff) {
            return &self.declars.values()[idx];
        } else {
            return null;
        }
    }

    pub fn getInductive(self: *const Env, n: NamePtr) ?*const InductiveData {
        if (self.getDeclar(n)) |d| {
            switch (d.*) {
                .inductive => |*i| return i,
                else => return null,
            }
        }
        return null;
    }

    pub fn getRecursor(self: *const Env, n: NamePtr) ?*const RecursorData {
        if (self.getDeclar(n)) |d| {
            switch (d.*) {
                .recursor => |*r| return r,
                else => return null,
            }
        }
        return null;
    }

    pub fn getConstructor(self: *const Env, n: NamePtr) ?*const ConstructorData {
        if (self.getDeclar(n)) |d| {
            switch (d.*) {
                .constructor => |*c| return c,
                else => return null,
            }
        }
        return null;
    }

    pub fn canBeStruct(self: *const Env, n: NamePtr) bool {
        if (self.getInductive(n)) |i| {
            return (!i.is_recursive) and (i.all_ctor_names.len == 1) and (i.num_indices == 0);
        }
        return false;
    }

    pub fn getDeclarVal(self: *const Env, n: NamePtr) ?struct { LevelsPtr, ExprPtr } {
        const d = self.getDeclar(n) orelse return null;
        switch (d.*) {
            .definition => |*x| return .{ x.info.uparams, x.val },
            .theorem => |*x| return .{ x.info.uparams, x.val },
            else => return null,
        }
    }
};
