const std = @import("std");
const FxContext = @import("hash.zig").FxContext;
const util = @import("util.zig");

const UFNode = struct {
    parent: usize,
    rank: usize,
};

pub fn UnionFind(comptime A: type) type {
    return struct {
        const Self = @This();

        const Entry = struct {
            key: A,
            node: UFNode,
        };

        const IndexMap = std.HashMapUnmanaged(A, usize, FxContext(A), 80);

        entries: std.ArrayList(Entry),
        index_of: IndexMap,

        pub const empty: Self = .{ .entries = .empty, .index_of = .empty };

        pub fn deinit(self: *Self) void {
            self.entries.deinit(util.smp_allocator);
            self.index_of.deinit(util.smp_allocator);
        }

        pub fn clear(self: *Self) void {
            self.entries.clearRetainingCapacity();
            self.index_of.clearRetainingCapacity();
        }

        fn getOrPush(self: *Self, e: A) usize {
            const gop = self.index_of.getOrPut(util.smp_allocator, e) catch util.oom();
            if (gop.found_existing) return gop.value_ptr.*;
            const idx = self.entries.items.len;
            gop.value_ptr.* = idx;
            self.entries.append(util.smp_allocator, .{ .key = e, .node = .{ .parent = idx, .rank = 0 } }) catch util.oom();
            return idx;
        }

        fn findParentIdx(self: *Self, idx: usize) usize {
            const parent_idx = self.entries.items[idx].node.parent;
            if (parent_idx == idx) {
                return idx;
            } else {
                const root = self.findParentIdx(parent_idx);
                self.entries.items[idx].node.parent = root;
                return root;
            }
        }

        fn linkRoots(self: *Self, x_root: usize, y_root: usize) void {
            if (x_root != y_root) {
                const x_root_rank = self.entries.items[x_root].node.rank;
                const y_root_rank = self.entries.items[y_root].node.rank;
                if (y_root_rank < x_root_rank) {
                    self.entries.items[y_root].node.parent = x_root;
                } else {
                    self.entries.items[x_root].node.parent = y_root;
                }
                if (x_root_rank == y_root_rank) {
                    self.entries.items[y_root].node.rank += 1;
                }
            }
        }

        pub fn unite(self: *Self, a: A, b: A) void {
            const ai = self.getOrPush(a);
            const bi = self.getOrPush(b);
            const a_root = self.findParentIdx(ai);
            const b_root = self.findParentIdx(bi);
            self.linkRoots(a_root, b_root);
        }

        pub fn checkUfEq(self: *Self, e1: A, e2: A) bool {
            const idx1 = self.getOrPush(e1);
            const idx2 = self.getOrPush(e2);
            return self.findParentIdx(idx1) == self.findParentIdx(idx2);
        }
    };
}
