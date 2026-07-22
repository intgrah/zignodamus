pub const parser = @import("export_file/parser.zig");

const env = @import("env.zig");
const ptr = @import("ptr.zig");
const Dag = @import("Dag.zig");
const FxHashMap = @import("swiss_map.zig").FxHashMap;
const NamePtr = ptr.NamePtr;
const LevelPtr = ptr.LevelPtr;

pub const ExportFile = struct {
    dag: Dag,
    anon: NamePtr,
    zero: LevelPtr,
    declars: env.DeclarMap,
    name_cache: Dag.NameCache,
    config: Config,
    mutual_block_sizes: FxHashMap(NamePtr, struct { usize, usize }),

    pub fn newEnv(self: *const ExportFile, env_limit: env.EnvLimit) env.Env {
        return env.Env.init(&self.declars, env_limit);
    }
};

pub const Config = struct {
    export_file_path: ?[]const u8 = null,
    use_stdin: bool = false,
    permitted_axioms: ?[]const []const u8 = null,
    unpermitted_axiom_hard_error: bool = true,
    num_threads: usize = 0,
    nat_extension: bool = false,
    string_extension: bool = false,
    print_success_message: bool = false,
    print_axioms: bool = true,
    unsafe_permit_all_axioms: bool = false,
};
