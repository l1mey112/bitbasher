const std = @import("std");
const Lexer = @import("Lexer.zig");
const llvm_types = @import("llvm_types.zig");

const Allocator = std.mem.Allocator;
const TypeId = llvm_types.TypeId;
const TypeAttribute = llvm_types.TypeAttribute;
const Token = Lexer.Token;

pub const Function = struct {
    name: Token,

    // contains argument types and their attributes
    type_id: TypeId,
    arg_names: []const Token,

    function_attrs: []const TypeAttribute,
};

pub const ModuleObject = union(enum) {
	function: Function,

    pub fn deinit(self: *ModuleObject, allocator: Allocator) void {
        switch (self.*) {
            .function => |*v| {
                allocator.free(v.arg_names);
                allocator.free(v.function_attrs);
            },
        }
        allocator.destroy(self);
    }
};
