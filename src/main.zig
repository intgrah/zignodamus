const std = @import("std");
const M_TRIM_THRESHOLD: c_int = -1;
const M_MMAP_THRESHOLD: c_int = -3;
const M_ARENA_MAX: c_int = -8;
extern fn mallopt(param: c_int, value: c_int) c_int;
const clap = @import("clap");
const zignodamus = @import("zignodamus");
const util = zignodamus.util;
const Config = zignodamus.export_file.Config;
const parser = zignodamus.parser;
const tc = zignodamus.tc;

const params = clap.parseParamsComptime(
    \\-h, --help                            Display this help and exit.
    \\-j, --threads <usize>                 Number of checker threads.
    \\    --nat-extension                   Enable the Nat literal extension.
    \\    --string-extension                Enable the String literal extension.
    \\    --unsafe-permit-all-axioms        Permit all axioms (unsafe).
    \\    --permit-axiom <str>...           Permit an axiom by name (repeatable).
    \\    --no-unpermitted-axiom-hard-error Do not hard-error on unpermitted axioms.
    \\    --print-success                   Print a success message.
    \\    --use-stdin                       Read the export file from stdin.
    \\<str>                                 Path to the export file.
    \\
);

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

fn readInput(io: std.Io, gpa: std.mem.Allocator, export_file_path: ?[]const u8) !Input {
    const path = export_file_path orelse {
        const read_buf = try gpa.alloc(u8, 1 << 20);
        defer gpa.free(read_buf);
        var stdin_reader = std.Io.File.stdin().readerStreaming(io, read_buf);
        return .{ .owned = try stdin_reader.interface.allocRemaining(gpa, .unlimited) };
    };
    const export_handle = try std.Io.Dir.cwd().openFile(io, path, .{});
    defer export_handle.close(io);
    const size: usize = @intCast(try export_handle.length(io));
    if (size == 0) return .empty;
    const mapped = try std.posix.mmap(null, size, .{ .READ = true }, .{ .TYPE = .PRIVATE }, export_handle.handle, 0);
    std.posix.madvise(mapped.ptr, mapped.len, std.posix.MADV.SEQUENTIAL) catch {};
    return .{ .mapped = mapped };
}

pub fn main(init: std.process.Init) void {
    mainInner(init) catch |err| switch (err) {
        error.ParseFailed => std.process.exit(1),
        else => {
            std.debug.print("error: {s}\n", .{@errorName(err)});
            std.process.exit(2);
        },
    };
}

fn mainInner(init: std.process.Init) !void {
    const io = init.io;
    const gpa = init.gpa;

    var diag = clap.Diagnostic{};
    var res = clap.parse(clap.Help, &params, clap.parsers.default, init.minimal.args, .{
        .diagnostic = &diag,
        .allocator = gpa,
        .assignment_separators = "=:",
    }) catch |err| {
        try diag.reportToFile(io, .stderr(), err);
        return err;
    };
    defer res.deinit();

    if (res.args.help != 0) {
        return clap.helpToFile(io, .stdout(), clap.Help, &params, .{});
    }

    const num_threads: usize = res.args.threads orelse 0;
    if (num_threads <= 1) {
        _ = mallopt(M_TRIM_THRESHOLD, -1);
        _ = mallopt(M_MMAP_THRESHOLD, 256 * 1024 * 1024);
        _ = mallopt(M_ARENA_MAX, 1);
    }
    const use_stdin = res.args.@"use-stdin" != 0;
    const nat_extension = res.args.@"nat-extension" != 0;
    const string_extension = res.args.@"string-extension" != 0;
    const unsafe_permit_all_axioms = res.args.@"unsafe-permit-all-axioms" != 0;
    const unpermitted_axiom_hard_error = res.args.@"no-unpermitted-axiom-hard-error" == 0;
    const print_success_message = res.args.@"print-success" != 0;

    const export_file_path = res.positionals[0];

    const permitted_axioms: ?[]const []const u8 =
        if (res.args.@"permit-axiom".len > 0) res.args.@"permit-axiom" else null;

    if (export_file_path == null and !use_stdin) {
        return error.MissingExportFile;
    }
    if (export_file_path != null and use_stdin) {
        return error.ConflictingExportSource;
    }
    if (unsafe_permit_all_axioms) {
        if (unpermitted_axiom_hard_error) {
            return error.ConflictingAxiomOptions;
        }
        if (permitted_axioms != null) {
            return error.ConflictingAxiomOptions;
        }
    }

    const config = Config{
        .export_file_path = export_file_path,
        .use_stdin = use_stdin,
        .permitted_axioms = permitted_axioms,
        .unpermitted_axiom_hard_error = unpermitted_axiom_hard_error,
        .num_threads = num_threads,
        .nat_extension = nat_extension,
        .string_extension = string_extension,
        .print_success_message = print_success_message,
        .print_axioms = true,
        .unsafe_permit_all_axioms = unsafe_permit_all_axioms,
    };

    const input = try readInput(io, gpa, export_file_path);
    errdefer input.release(gpa);
    var global_arena = zignodamus.Arena.init(util.smp_allocator);
    defer global_arena.deinit();

    const export_file, const skipped_axioms = try parser.parseExportFile(&global_arena, input.bytes(), config);
    input.release(gpa);
    if (init.minimal.environ.getPosix("PARSE_ONLY") != null) {
        std.process.exit(0);
    }

    tc.checkAllDeclars(&export_file);

    if (tc.checkingFailed()) {
        std.process.exit(1);
    }

    if (export_file.config.print_success_message) {
        var buf: [4096]u8 = undefined;
        var writer = std.Io.File.stdout().writer(io, &buf);
        const w = &writer.interface;
        if (skipped_axioms.len == 0) {
            try w.print("Checked {d} declarations with no errors\n", .{export_file.declars.count()});
        } else {
            try w.print("Checked {d} declarations with no errors, skipping exported but unpermitted axioms {any}\n", .{ export_file.declars.count(), skipped_axioms });
        }
        try w.flush();
    } else if (skipped_axioms.len != 0) {
        var buf: [4096]u8 = undefined;
        var writer = std.Io.File.stdout().writer(io, &buf);
        const w = &writer.interface;
        try w.print("Skipped exported but unpermitted axioms {any}\n", .{skipped_axioms});
        try w.flush();
    }
}
