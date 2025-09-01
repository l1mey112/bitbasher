const std = @import("std");
const Lexer = @import("Lexer.zig");
const Parser = @import("Parser.zig");
const llvm_types = @import("llvm_types.zig");

const Writer = std.Io.Writer;
const Allocator = std.mem.Allocator;
const TypeId = llvm_types.TypeId;
const TypeAttribute = llvm_types.TypeAttribute;
const Token = Lexer.Token;

pub const AttributeSet = struct {
    attrs: []const TypeAttribute,

    const _Fmt = struct {
        set: *const AttributeSet,
        parser: *const Parser,

        pub fn format(self: _Fmt, writer: *Writer) Writer.Error!void {
            for (self.set.attrs, 0..) |attr, i| {
                const str = attr.loc.slice(self.parser.lexer.b);
                if (attr.kind == .attr_grp_id) {
                    try writer.print("#{s}", .{str});
                } else {
                    try writer.print("{s}", .{str});
                }
                if (i + 1 < self.set.attrs.len) {
                    try writer.print(" ", .{});
                }
            }
            try writer.flush();
        }
    };

    pub fn Fmt(set: *const AttributeSet, parser: *const Parser) _Fmt {
        return .{
            .parser = parser,
            .set = set,
        };
    }
};

pub const Function = struct {
    name: []const u8,

    // contains argument types and their attributes
    type_id: TypeId,
    arg_names: [][]const u8,

    function_attrs: AttributeSet,

    bbs: std.StringArrayHashMapUnmanaged(BasicBlock),

    pub fn deinit(self: *Function, allocator: Allocator) void {
        allocator.free(self.name);
        for (self.arg_names) |xs| {
            allocator.free(xs);
        }
        allocator.free(self.arg_names);
        allocator.free(self.function_attrs.attrs);

        var iter = self.bbs.iterator();
        while (iter.next()) |data| {
            const bb = data.value_ptr;                
            allocator.free(bb.name);
            for (bb.insts.items) |inst| {
                inst.deinit(allocator);
            }
            bb.insts.deinit(allocator);
        }

        self.bbs.deinit(allocator);
    }

    pub fn formatWriter(self: Function, writer: *Writer, parser: *const Parser) Writer.Error!void {
        const function_type = parser.type_table.extra(self.type_id).function;

        try function_type.formatWriter(writer, self.name, parser);

        if (self.bbs.count() != 0) {
            try writer.print(" {{\n", .{});
            var bb_iter = self.bbs.iterator();
            while (bb_iter.next()) |entry| {
                const bb = entry.value_ptr;

                try writer.print("{s}:\n", .{bb.name});

                for (bb.insts.items) |inst| {
                    try writer.print("  ", .{});
                    try inst.formatWriter(writer, parser);
                    try writer.print("\n", .{});
                }
            }
            try writer.print("}}\n", .{});
        } else {
            try writer.print("\n", .{});
        }
        try writer.flush();
    }
};

pub const PseudoArgument = union(enum) {
    token: Token.Kind,
    local_var: []const u8,
    global_var: []const u8,
    label: []const u8,
    type_id: TypeId,

    integer_literal: []const u8,
    float_literal: []const u8,
    hex_float_literal: []const u8,
    struct_literal: []const PseudoPair,
    vector_literal: []const PseudoPair,
    array_literal: []const PseudoPair,

    list: []const PseudoArgument, // [ ... ]

    // c"Hello World\0A\00"
    string_array_literal: []const u8,

    // call i32 @sqlite3PagerWrite(ptr noundef %169)
    // this is ignoring all the attributes
    call_list: []const PseudoPair,

    @"null",
    undef,
    poison,
    zeroinitializer,

    // parsing a constant instruction in a global decl isn't supported for example
    invalid,

    pub const PseudoPair = struct { type_id: TypeId, arg: PseudoArgument };

    pub fn deinit(self: PseudoArgument, allocator: Allocator) void {
        switch (self) {
            .local_var, .global_var, .label, .integer_literal, .float_literal, .hex_float_literal, .string_array_literal => |v| allocator.free(v),
            .list => |v| allocator.free(v),
            .struct_literal, .vector_literal, .array_literal, .call_list => |v| {
                for (v) |pair| {
                    pair.arg.deinit(allocator);
                }
                allocator.free(v);
            },
            .type_id, .token, .@"null", .undef, .poison, .zeroinitializer, .invalid => {}
        }
    }

    pub fn formatWriter(self: PseudoArgument, writer: *Writer, parser: *const Parser) Writer.Error!void {
        try self.formatInner(writer, parser);
        try writer.flush();
    }
    fn formatPseudoPair(open: u8, close: u8, v: []const PseudoPair, writer: *Writer, parser: *const Parser) Writer.Error!void {
        try writer.print("{c}", .{open});
        if (open != '(' and open != '[') try writer.print(" ", .{});
        for (v, 0..) |pair, i| {
            try writer.print("{f} ", .{pair.type_id.Fmt(parser)});
            try pair.arg.formatInner(writer, parser);
            if (i + 1 < v.len) {
                try writer.print(", ", .{});
            }
        }
        if (open != '(' and open != '[') try writer.print(" ", .{});
        try writer.print("{c}", .{close});
    }
    fn formatInner(self: PseudoArgument, writer: *Writer, parser: *const Parser) Writer.Error!void {
        switch (self) {
            .token => |v| {
                try writer.print("{s}", .{parser.lexer.token_map.get(v)});
            },
            .integer_literal, .float_literal, .hex_float_literal => |v| {
                try writer.print("{s}", .{v});
            },
            .string_array_literal => |v| {
                try writer.print("c\"{s}\"", .{v});
            },
            .list => |v| {
                try writer.print("[", .{});
                for (v, 0..) |arg, i| {
                    try arg.formatInner(writer, parser);
                    if (i + 1 < v.len) {
                        try writer.print(", ", .{});
                    }
                }
                try writer.print("]", .{});
            },
            .struct_literal => |v| {
                try formatPseudoPair('{', '}', v, writer, parser);
            },
            .vector_literal => |v| {
                try formatPseudoPair('<', '>', v, writer, parser);
            },
            .array_literal => |v| {
                try formatPseudoPair('[', ']', v, writer, parser);
            },
            .call_list => |v| {
                try formatPseudoPair('(', ')', v, writer, parser);
            },
            .local_var => |v| try writer.print("%{s}", .{v}),
            .global_var => |v| try writer.print("@{s}", .{v}),
            .label => |v| try writer.print("label %{s}", .{v}),
            .type_id => |v| try writer.print("[type {f}]", .{v.Fmt(parser)}),
            .@"null" => try writer.print("null", .{}),
            .undef => try writer.print("undef", .{}),
            .poison => try writer.print("poison", .{}),
            .zeroinitializer => try writer.print("zeroinitializer", .{}),
            .invalid => try writer.print("<INVALID>", .{}),
        }
    }

    const _Fmt = struct {
        arg: *const PseudoArgument,
        parser: *const Parser,

        pub fn format(self: _Fmt, writer: *Writer) Writer.Error!void {
            try self.arg.formatWriter(writer, self.parser);
        }
    };

    pub fn Fmt(arg: *const PseudoArgument, parser: *const Parser) _Fmt {
        return .{
            .arg = arg,
            .parser = parser,
        };
    }
};

pub const Inst = struct {
    // %var or %0, owned
    //  ^^^     ^
    lhs: ?[]const u8,
    kind: Token.Kind,

    args: []const PseudoArgument,

    pub fn formatWriter(self: Inst, writer: *Writer, parser: *const Parser) Writer.Error!void {
        if (self.lhs) |lhs| {
            try writer.print("%{s} = ", .{lhs});
        }
        try writer.print("{s} ", .{parser.lexer.token_map.get(self.kind)});
        for (self.args, 0..) |arg, i| {
            try arg.formatWriter(writer, parser);
            if (i + 1 < self.args.len) {
                try writer.print(", ", .{});
            }
        }
        try writer.flush();
    }

    pub fn deinit(self: Inst, allocator: Allocator) void {
        if (self.lhs) |lhs| {
            allocator.free(lhs);
        }
        
        for (self.args) |arg| {
            arg.deinit(allocator);
        }
        allocator.free(self.args);
    }
};

pub const BasicBlock = struct {
    name: []const u8,
    insts: std.ArrayList(Inst),
};

pub const Global = struct {
    name: []const u8,

    type_id: TypeId,
    value: ?PseudoArgument,

    is_constant: bool,
    alignment: ?u64,

    pub fn deinit(self: *Global, allocator: Allocator) void {
        allocator.free(self.name);
        if (self.value) |*value| {
            value.deinit(allocator);
        }
    }

    pub fn formatWriter(self: Global, writer: *Writer, parser: *const Parser) Writer.Error!void {
        try writer.print("@{s} = ", .{self.name});
        if (self.is_constant) {
            try writer.print("constant ", .{});
        } else {
            try writer.print("global ", .{});
        }
        try writer.print("{f}", .{self.type_id.Fmt(parser)});
        if (self.value) |value| {
            try writer.print(" {f}", .{value.Fmt(parser)});
        }
        if (self.alignment) |alignment| {
            try writer.print(", align {}", .{alignment});
        }
        try writer.print("\n", .{});
        try writer.flush();
    }
    
    const _Fmt = struct {
        global: *const Global,
        parser: *const Parser,

        pub fn format(self: _Fmt, writer: *Writer) Writer.Error!void {
            try self.global.formatWriter(writer, self.parser);
        }
    };

    pub fn Fmt(global: *const Global, parser: *const Parser) _Fmt {
        return .{
            .global = global,
            .parser = parser,
        };
    }
};

pub const ModuleObject = union(enum) {
	function: Function,
    global: Global,

    pub fn deinitSelf(self: *ModuleObject, allocator: Allocator) void {
        switch (self.*) {
            .function => |*v| {
                v.deinit(allocator);
            },
            .global => |*v| {
                v.deinit(allocator);
            },
        }
        allocator.destroy(self);
    }
};
