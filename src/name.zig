const util = @import("util.zig");
const std = @import("std");

const NamePtr = @import("ptr.zig").NamePtr;
const StringPtr = @import("ptr.zig").StringPtr;
const TcCtx = @import("TcCtx.zig");

const kindHash = @import("hash.zig").kindHash;

pub const Name = struct {
    hash: u64,
    kind: Kind,

    pub const Kind = union(enum) {
        anon,
        str: struct { pfx: NamePtr, sfx: StringPtr },
        num: struct { pfx: NamePtr, n: u64 },
    };

    pub inline fn mk(kind: Kind) Name {
        return .{ .hash = kindHash(kind), .kind = kind };
    }

    pub const anon: Name = mk(.anon);

    pub fn getHash(self: *const Name) u64 {
        return self.hash;
    }
};

pub fn concatName(self: *TcCtx, n1: NamePtr, n2: NamePtr) NamePtr {
    switch (n2.asRef().kind) {
        .anon => return n1,
        .str => |s| {
            const pfx = concatName(self, n1, s.pfx);
            return TcCtx.str(self, pfx, s.sfx);
        },
        .num => |n| {
            const pfx = concatName(self, n1, n.pfx);
            return TcCtx.num(self, pfx, n.n);
        },
    }
}

pub fn appendIndexAfter(self: *TcCtx, n: NamePtr, idx: u64) NamePtr {
    switch (n.asRef().kind) {
        .str => |st| {
            const s = st.sfx.asRef().*;
            const formatted = std.fmt.allocPrint(self.arena.child, "{s}_{d}", .{ s, idx }) catch util.oom();
            const sp = TcCtx.allocString(self, formatted);
            return TcCtx.str(self, st.pfx, sp);
        },
        else => {
            const formatted = std.fmt.allocPrint(self.arena.child, "_{d}", .{idx}) catch util.oom();
            const sp = TcCtx.allocString(self, formatted);
            return TcCtx.str(self, n, sp);
        },
    }
}

pub fn replacePfx(self: *TcCtx, n: NamePtr, outgoing: NamePtr, incoming: NamePtr) NamePtr {
    switch (n.asRef().kind) {
        .anon => switch (outgoing.asRef().kind) {
            .anon => return incoming,
            else => return TcCtx.anonymous(self),
        },
        .str => |s| {
            if (n == outgoing) return incoming;
            const pfx = replacePfx(self, s.pfx, outgoing, incoming);
            return TcCtx.str(self, pfx, s.sfx);
        },
        .num => |nm| {
            if (n == outgoing) return incoming;
            const pfx = replacePfx(self, nm.pfx, outgoing, incoming);
            return TcCtx.num(self, pfx, nm.n);
        },
    }
}
