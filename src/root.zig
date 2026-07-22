const std = @import("std");

pub const Arena = @import("Arena.zig");
pub const Dag = @import("Dag.zig");
pub const TcCtx = @import("TcCtx.zig");
pub const conv = @import("conv.zig");
pub const debug_printer = @import("debug_printer.zig");
pub const env = @import("env.zig");
pub const eval = @import("eval.zig");
pub const export_file = @import("export_file.zig");
pub const expr = @import("expr.zig");
pub const hash = @import("hash.zig");
pub const inductive = @import("inductive.zig");
pub const interner = @import("interner.zig");
pub const level = @import("level.zig");
pub const name = @import("name.zig");
pub const nat = @import("nat.zig");
pub const ptr = @import("ptr.zig");
pub const quot = @import("quot.zig");
pub const swiss_map = @import("swiss_map.zig");
pub const tc = @import("tc.zig");
pub const union_find = @import("union_find.zig");
pub const util = @import("util.zig");
pub const value = @import("value.zig");

pub const stack_size: usize = 2 * 1024 * 1024 * 1024;

test {
    const modules = .{
        Arena,
        Dag,
        TcCtx,
        conv,
        debug_printer,
        env,
        eval,
        export_file,
        export_file.parser,
        expr,
        hash,
        inductive,
        interner,
        level,
        name,
        nat,
        ptr,
        quot,
        swiss_map,
        tc,
        union_find,
        util,
        value,
    };
    inline for (modules) |m| {
        std.testing.refAllDecls(m);
    }
}
