pub const parser = @import("export_file/parser.zig");

const env = @import("env.zig");
const util = @import("util.zig");
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

    pub fn deinit(self: *ExportFile) void {
        self.dag.deinit();
        self.declars.deinit(util.smp_allocator);
        self.mutual_block_sizes.deinit(util.smp_allocator);
        self.name_cache.nat_red.deinit(util.smp_allocator);
    }
};

pub const standard_axioms: []const []const u8 = &.{ "propext", "Classical.choice", "Quot.sound" };

pub const AxiomPolicy = union(enum) {
    unsafe_permit_all,
    permitted: Permitted,

    pub const Permitted = struct {
        axioms: []const []const u8 = &.{},
        on_unpermitted: enum { hard_error, skip } = .hard_error,
    };
};

pub const Config = struct {
    axiom_policy: AxiomPolicy = .{ .permitted = .{} },
    num_threads: usize = 0,
    nat_extension: bool = false,
    string_extension: bool = false,
};
