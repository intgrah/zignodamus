const std = @import("std");
const name = @import("name.zig");
const level = @import("level.zig");
const expr = @import("expr.zig");
const env = @import("env.zig");
const ptr = @import("ptr.zig");

const NamePtr = ptr.NamePtr;
const LevelPtr = ptr.LevelPtr;
const ExprPtr = ptr.ExprPtr;
const LevelsPtr = ptr.LevelsPtr;
const StringPtr = ptr.StringPtr;
const BigUintPtr = ptr.BigUintPtr;
const Name = name.Name;
const Level = level.Level;
const Expr = expr.Expr;
const DeclarInfo = env.DeclarInfo;
const RecRule = env.RecRule;
const ReducibilityHint = env.ReducibilityHint;

const Writer = std.Io.Writer;
const Error = Writer.Error;

pub fn debugPrint(f: *Writer, elem: anytype) Error!void {
    const A = @TypeOf(elem);
    switch (A) {
        NamePtr => return debugName(f, elem),
        LevelPtr => return debugLevel(f, elem),
        ExprPtr => return debugExpr(f, elem),
        LevelsPtr => return debugLevels(f, elem),
        StringPtr => return debugString(f, elem),
        BigUintPtr => return debugBignum(f, elem),
        *const DeclarInfo, *DeclarInfo => return debugDeclarInfo(f, elem),
        DeclarInfo => return debugDeclarInfo(f, &elem),
        RecRule => return debugRecRule(f, elem),
        ReducibilityHint => return debugReducibilityHint(f, elem),
        else => {},
    }

    switch (@typeInfo(A)) {
        .optional => {
            if (elem) |x| {
                try f.print("Some({f})", .{d(x)});
            } else {
                try f.writeAll("None");
            }
            return;
        },
        .@"struct" => |s| {
            if (s.is_tuple) {
                try f.writeAll("(");
                inline for (s.fields, 0..) |field, i| {
                    if (i != 0) try f.writeAll(", ");
                    try debugPrint(f, @field(elem, field.name));
                }
                try f.writeAll(")");
                return;
            }
        },
        .pointer => |p| {
            if (p.size == .slice) return debugSlice(f, elem);
            if (p.size == .one) return debugPrint(f, elem.*);
        },
        else => {},
    }
    @compileError("debug_print: unsupported type " ++ @typeName(A));
}

fn Formatter(comptime T: type) type {
    return struct {
        e: T,
        pub fn format(self: @This(), w: *Writer) Error!void {
            return debugPrint(w, self.e);
        }
    };
}

fn d(elem: anytype) Formatter(@TypeOf(elem)) {
    return .{ .e = elem };
}

fn debugSlice(f: *Writer, elems: anytype) Error!void {
    try f.writeAll("[");
    for (elems, 0..) |x, i| {
        if (i != 0) try f.writeAll(", ");
        try debugPrint(f, x);
    }
    try f.writeAll("]");
}

fn debugName(f: *Writer, elem: NamePtr) Error!void {
    switch (elem.asRef().kind) {
        .anon => return,
        .str => |s| {
            const sfx = s.sfx.asRef().*;
            switch (s.pfx.asRef().kind) {
                .anon => try f.print("{s}", .{sfx}),
                else => try f.print("{f}.{s}", .{ d(s.pfx), sfx }),
            }
        },
        .num => |n| switch (n.pfx.asRef().kind) {
            .anon => try f.print("{d}", .{n.n}),
            else => try f.print("{f}.{d}", .{ d(n.pfx), n.n }),
        },
    }
}

fn debugLevel(f: *Writer, elem: LevelPtr) Error!void {
    switch (elem.asRef().kind) {
        .zero => try f.writeAll("0"),
        .succ => {
            const val, const n = level.levelSuccs(elem);
            if (val.asRef().kind == .zero) {
                try f.print("{d}", .{n});
            } else {
                try f.print("{f} + {d}", .{ d(val), n });
            }
        },
        .max => |m| try f.print("max({f}, {f})", .{ d(m.l), d(m.r) }),
        .imax => |m| try f.print("imax({f}, {f})", .{ d(m.l), d(m.r) }),
        .param => |p| try debugName(f, p),
    }
}

fn debugExpr(f: *Writer, elem: ExprPtr) Error!void {
    switch (elem.asRef().kind) {
        .@"var" => |v| try f.print("${d}", .{v.dbj_idx}),
        .sort => |s| try f.print("Sort({f})", .{d(s.level)}),
        .@"const" => |c| try f.print("{f}.{f}", .{ d(c.name), d(c.levels.asRef()) }),
        .app => |a| try f.print("({f} {f})", .{ d(a.fun), d(a.arg) }),
        .let => |l| try f.print(
            "let {f} : {f} := {f} in {f}",
            .{ d(l.data.binder_name), d(l.data.binder_type), d(l.data.val), d(l.data.body) },
        ),
        .pi => |p| try f.print(
            "Pi ({f} : {f}), {f}",
            .{ d(p.binder_name), d(p.binderType()), d(p.body) },
        ),
        .lambda => |la| try f.print(
            "fun ({f} : {f}) => {f}",
            .{ d(la.binder_name), d(la.binderType()), d(la.body) },
        ),
        .proj => |pr| try f.print("%({f}).{d}", .{ d(pr.structure), pr.idx }),
        .nat_lit => |nl| try f.print("NLit({any})", .{nl.ptr.asRef()}),
        .string_lit => |sl| try f.print("SLit({s})", .{sl.ptr.asRef().*}),
    }
}

fn debugLevels(f: *Writer, elem: LevelsPtr) Error!void {
    try debugSlice(f, elem.asRef());
}

fn debugString(f: *Writer, elem: StringPtr) Error!void {
    try f.print("\"{s}\"", .{elem.asRef().*});
}

fn debugBignum(f: *Writer, elem: BigUintPtr) Error!void {
    try f.print("{any}", .{elem.asRef()});
}

fn debugDeclarInfo(f: *Writer, elem: *const DeclarInfo) Error!void {
    try f.print(
        "DeclarInfo {{ name: {f}, ty: {f}, uparams: {f} }}",
        .{ d(elem.name), d(elem.ty), d(elem.uparams) },
    );
}

fn debugRecRule(f: *Writer, elem: RecRule) Error!void {
    try f.print(
        "RecRule {{ ctor_name: {f}, ctor_telescope_size_wo_params: {d}, val: {f} }}",
        .{ d(elem.ctor_name), elem.ctor_telescope_size_wo_params, d(elem.val) },
    );
}

fn debugReducibilityHint(f: *Writer, elem: ReducibilityHint) Error!void {
    switch (elem) {
        .opaque_ => try f.writeAll("Opaque"),
        .regular => |h| try f.print("Regular({d})", .{h}),
        .abbrev => try f.writeAll("Abbrev"),
    }
}

test {
    _ = &debugName;
    _ = &debugLevel;
    _ = &debugExpr;
    _ = &debugLevels;
    _ = &debugString;
    _ = &debugBignum;
    _ = &debugDeclarInfo;
    _ = &debugRecRule;
    _ = &debugReducibilityHint;
}
