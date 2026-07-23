const std = @import("std");
const util = @import("util.zig");
const tc = @import("tc.zig");
const Arena = @import("Arena.zig");
const Config = @import("export_file.zig").Config;
const parser = @import("export_file.zig").parser;

pub const Options = struct {
    source: Source,
    parse_only: bool = false,
    print_success_message: bool = false,
    config: Config = .{},

    pub const Source = union(enum) {
        path: []const u8,
        stdin,
    };
};

const Input = union(enum) {
    mapped: []align(std.heap.page_size_min) u8,
    owned: []u8,
    empty,

    fn bytes(self: Input) []const u8 {
        return switch (self) {
            .mapped => |m| m,
            .owned => |o| o,
            .empty => "",
        };
    }

    fn release(self: Input, gpa: std.mem.Allocator) void {
        switch (self) {
            .mapped => |m| std.posix.munmap(m),
            .owned => |o| gpa.free(o),
            .empty => {},
        }
    }
};

fn readInput(io: std.Io, gpa: std.mem.Allocator, source: Options.Source) !Input {
    switch (source) {
        .stdin => {
            const read_buf = try gpa.alloc(u8, 1 << 20);
            defer gpa.free(read_buf);
            var stdin_reader = std.Io.File.stdin().readerStreaming(io, read_buf);
            return .{ .owned = try stdin_reader.interface.allocRemaining(gpa, .unlimited) };
        },
        .path => |path| {
            const export_handle = try std.Io.Dir.cwd().openFile(io, path, .{});
            defer export_handle.close(io);
            const size: usize = @intCast(try export_handle.length(io));
            if (size == 0) return .empty;
            const mapped = try std.posix.mmap(null, size, .{ .READ = true }, .{ .TYPE = .PRIVATE }, export_handle.handle, 0);
            std.posix.madvise(mapped.ptr, mapped.len, std.posix.MADV.SEQUENTIAL) catch {};
            return .{ .mapped = mapped };
        },
    }
}

pub fn run(io: std.Io, gpa: std.mem.Allocator, options: Options) !void {
    var input = try readInput(io, gpa, options.source);
    errdefer input.release(gpa);
    var global_arena = Arena.init(util.smp_allocator);
    defer global_arena.deinit();

    const export_file, const skipped_axioms = try parser.parseExportFile(&global_arena, input.bytes(), options.config);
    input.release(gpa);
    input = .empty;
    if (options.parse_only) return;

    tc.checkAllDeclars(&export_file);

    if (tc.checkingFailed()) {
        return error.CheckFailed;
    }

    if (!options.print_success_message and skipped_axioms.len == 0) return;

    var buf: [4096]u8 = undefined;
    var writer = std.Io.File.stdout().writer(io, &buf);
    const w = &writer.interface;
    if (!options.print_success_message) {
        try w.print("Skipped exported but unpermitted axioms {any}\n", .{skipped_axioms});
    } else if (skipped_axioms.len == 0) {
        try w.print("Checked {d} declarations with no errors\n", .{export_file.declars.count()});
    } else {
        try w.print("Checked {d} declarations with no errors, skipping exported but unpermitted axioms {any}\n", .{ export_file.declars.count(), skipped_axioms });
    }
    try w.flush();
}
