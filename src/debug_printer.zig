const std = @import("std");
const name = @import("name.zig");
const level = @import("level.zig");
const expr = @import("expr.zig");
const env = @import("env.zig");

const NamePtr = @import("ptr.zig").NamePtr;
const LevelPtr = @import("ptr.zig").LevelPtr;
const ExprPtr = @import("ptr.zig").ExprPtr;
const LevelsPtr = @import("ptr.zig").LevelsPtr;
const StringPtr = @import("ptr.zig").StringPtr;
const BigUintPtr = @import("ptr.zig").BigUintPtr;
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
                try f.writeAll("Some(");
                try debugPrint(f, x);
                try f.writeAll(")");
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
                else => {
                    try debugName(f, s.pfx);
                    try f.print(".{s}", .{sfx});
                },
            }
        },
        .num => |n| switch (n.pfx.asRef().kind) {
            .anon => try f.print("{d}", .{n.n}),
            else => {
                try debugName(f, n.pfx);
                try f.print(".{d}", .{n.n});
            },
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
                try debugLevel(f, val);
                try f.print(" + {d}", .{n});
            }
        },
        .max => |m| {
            try f.writeAll("max(");
            try debugLevel(f, m.l);
            try f.writeAll(", ");
            try debugLevel(f, m.r);
            try f.writeAll(")");
        },
        .imax => |m| {
            try f.writeAll("imax(");
            try debugLevel(f, m.l);
            try f.writeAll(", ");
            try debugLevel(f, m.r);
            try f.writeAll(")");
        },
        .param => |p| try debugName(f, p),
    }
}

fn debugExpr(f: *Writer, elem: ExprPtr) Error!void {
    switch (elem.asRef().kind) {
        .@"var" => |v| try f.print("${d}", .{v.dbj_idx}),
        .sort => |s| {
            try f.writeAll("Sort(");
            try debugLevel(f, s.level);
            try f.writeAll(")");
        },
        .@"const" => |c| {
            const levels = c.levels.asRef();
            try debugName(f, c.name);
            try f.writeAll(".");
            try debugSlice(f, levels);
        },
        .app => |a| {
            try f.writeAll("(");
            try debugExpr(f, a.fun);
            try f.writeAll(" ");
            try debugExpr(f, a.arg);
            try f.writeAll(")");
        },
        .let => |l| {
            try f.writeAll("let ");
            try debugName(f, l.data.binder_name);
            try f.writeAll(" : ");
            try debugExpr(f, l.data.binder_type);
            try f.writeAll(" := ");
            try debugExpr(f, l.data.val);
            try f.writeAll(" in ");
            try debugExpr(f, l.data.body);
        },
        .pi => |p| {
            try f.writeAll("Pi (");
            try debugName(f, p.binder_name);
            try f.writeAll(" : ");
            try debugExpr(f, p.binder_type);
            try f.writeAll("), ");
            try debugExpr(f, p.body);
        },
        .lambda => |la| {
            try f.writeAll("fun (");
            try debugName(f, la.binder_name);
            try f.writeAll(" : ");
            try debugExpr(f, la.binder_type);
            try f.writeAll(") => ");
            try debugExpr(f, la.body);
        },
        .local => |lo| {
            try f.writeAll("#(");
            try debugName(f, lo.binder_name);
            try f.writeAll(", ");
            try debugFvarId(f, lo.id);
            try f.writeAll(" : ");
            try debugExpr(f, lo.binder_type);
            try f.writeAll(")");
        },
        .proj => |pr| {
            try f.writeAll("%(");
            try debugExpr(f, pr.structure);
            try f.print(").{d}", .{pr.idx});
        },
        .nat_lit => |nl| {
            try f.print("NLit({any})", .{nl.ptr.asRef()});
        },
        .string_lit => |sl| {
            try f.print("SLit({s})", .{sl.ptr.asRef().*});
        },
    }
}

fn debugFvarId(f: *Writer, id: expr.FVarId) Error!void {
    switch (id) {
        .dbj_level => |x| try f.print("DbjLevel({d})", .{x}),
        .unique => |x| try f.print("Unique({d})", .{x}),
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
    try f.writeAll("DeclarInfo { name: ");
    try debugName(f, elem.name);
    try f.writeAll(", ty: ");
    try debugExpr(f, elem.ty);
    try f.writeAll(", uparams: ");
    try debugSlice(f, elem.uparams.asRef());
    try f.writeAll(" }");
}

fn debugRecRule(f: *Writer, elem: RecRule) Error!void {
    try f.writeAll("RecRule { ctor_name: ");
    try debugName(f, elem.ctor_name);
    try f.print(", ctor_telescope_size_wo_params: {d}, val: ", .{elem.ctor_telescope_size_wo_params});
    try debugExpr(f, elem.val);
    try f.writeAll(" }");
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
    _ = &debugFvarId;
    _ = &debugDeclarInfo;
    _ = &debugRecRule;
    _ = &debugReducibilityHint;
}
