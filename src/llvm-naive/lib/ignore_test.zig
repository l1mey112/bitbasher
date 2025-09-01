const std = @import("std");
const builtin = @import("builtin");

pub fn hasTestFunction(name: []const u8) bool {
    // see `lib/compiler/test_runner.zig` in `mainTerminal`

    const test_fn_list = builtin.test_functions;
    for (test_fn_list) |test_fn| {
        if (std.mem.eql(u8, test_fn.name, name)) {
            return true;
        }
    }
    return false;
}
