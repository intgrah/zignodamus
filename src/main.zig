const std = @import("std");
const clap = @import("clap");
const zignodamus = @import("zignodamus");

const M_TRIM_THRESHOLD: c_int = -1;
const M_MMAP_THRESHOLD: c_int = -3;
const M_ARENA_MAX: c_int = -8;
extern fn mallopt(param: c_int, value: c_int) c_int;

const params = clap.parseParamsComptime(
    \\-h, --help                            Display this help and exit.
    \\-j, --threads <usize>                 Number of checker threads.
    \\    --nat-extension                   Enable the Nat literal extension.
    \\    --string-extension                Enable the String literal extension.
    \\    --unsafe-permit-all-axioms        Permit all axioms (unsafe).
    \\    --permit-axiom <str>...           Permit an axiom by name (repeatable).
    \\    --no-unpermitted-axiom-hard-error Do not hard-error on unpermitted axioms.
    \\    --print-success                   Print a success message.
    \\    --parse-only                      Exit after parsing, without checking.
    \\    --use-stdin                       Read the export file from stdin.
    \\<str>                                 Path to the export file.
    \\
);

pub fn main(init: std.process.Init) void {
    mainInner(init) catch |err| switch (err) {
        error.ParseFailed, error.CheckFailed => std.process.exit(1),
        else => {
            std.debug.print("error: {s}\n", .{@errorName(err)});
            std.process.exit(2);
        },
    };
}

fn mainInner(init: std.process.Init) !void {
    var diag = clap.Diagnostic{};
    var res = clap.parse(clap.Help, &params, clap.parsers.default, init.minimal.args, .{
        .diagnostic = &diag,
        .allocator = init.gpa,
        .assignment_separators = "=:",
    }) catch |err| {
        try diag.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer res.deinit();

    if (res.args.help != 0) {
        return clap.helpToFile(init.io, .stdout(), clap.Help, &params, .{});
    }

    const source: zignodamus.RunOptions.Source = blk: {
        if (res.args.@"use-stdin" != 0) {
            if (res.positionals[0] != null) return error.ConflictingExportSource;
            break :blk .stdin;
        }
        break :blk .{ .path = res.positionals[0] orelse return error.MissingExportFile };
    };

    const axiom_policy: zignodamus.export_file.AxiomPolicy = blk: {
        const hard_error = res.args.@"no-unpermitted-axiom-hard-error" == 0;
        if (res.args.@"unsafe-permit-all-axioms" != 0) {
            if (hard_error) return error.ConflictingAxiomOptions;
            if (res.args.@"permit-axiom".len > 0) return error.ConflictingAxiomOptions;
            break :blk .unsafe_permit_all;
        }
        break :blk .{ .permitted = .{
            .axioms = res.args.@"permit-axiom",
            .on_unpermitted = if (hard_error) .hard_error else .skip,
        } };
    };

    const options = zignodamus.RunOptions{
        .source = source,
        .parse_only = res.args.@"parse-only" != 0,
        .print_success_message = res.args.@"print-success" != 0,
        .config = .{
            .axiom_policy = axiom_policy,
            .num_threads = res.args.threads orelse 0,
            .nat_extension = res.args.@"nat-extension" != 0,
            .string_extension = res.args.@"string-extension" != 0,
        },
    };

    if (options.config.num_threads <= 1) {
        _ = mallopt(M_TRIM_THRESHOLD, -1);
        _ = mallopt(M_MMAP_THRESHOLD, 256 * 1024 * 1024);
        _ = mallopt(M_ARENA_MAX, 1);
    }

    try zignodamus.run(init.io, init.gpa, options);
}
