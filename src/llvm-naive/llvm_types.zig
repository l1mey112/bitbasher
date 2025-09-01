const std = @import("std");
const Lexer = @import("Lexer.zig");
const Parser = @import("Parser.zig");
const deep_equal = @import("lib/deep_equal.zig");

const Writer = std.Io.Writer;
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const ArenaAllocator = std.heap.ArenaAllocator;
const Token = Lexer.Token;
const deepEql = deep_equal.deepEql;

pub const TypeId = enum(usize) {
    invalid_type,

    @"void",
    half,
    bfloat,
    float,
    double,
    x86_fp80,
    fp128,
    ppc_fp128,
    x86_amx,
    ptr, // ignore addrspace

    _,

    const _Fmt = struct {
        parser: *const Parser,
        type_id: TypeId,

        pub fn format(self: _Fmt, writer: *Writer) Writer.Error!void {
            try self.formatInner(writer, self.type_id);
            try writer.flush();
        }

        fn formatInner(self: _Fmt, writer: *Writer, type_id: TypeId) Writer.Error!void {
            if (@intFromEnum(type_id) < TypeTable.index_offset) {
                // writes the enum without the leading dot
                try writer.print("{s}", .{std.enums.tagName(TypeId, type_id) orelse unreachable});
                return;
            }

            const extra = self.parser.type_table.extra(type_id);
            switch (extra) {
                .integer => |v| try writer.print("i{}", .{v.bits}),
                .@"struct" => |v| {
                    try writer.print("{{ ", .{});
                    for (v.xs, 0..) |x, i| {
                        try self.formatInner(writer, x);
                        if (i + 1 < v.xs.len) {
                            try writer.print(", ", .{});
                        }
                    }
                    try writer.print(" }}", .{});
                },
                .vector => |v| {
                    try writer.print("<{} x ", .{v.elements});
                    try self.formatInner(writer, v.x);
                    try writer.print(">", .{});
                },
                .array => |v| {
                    try writer.print("[{} x ", .{v.elements});
                    try self.formatInner(writer, v.x);
                    try writer.print("]", .{});
                },
                .named => |v| try writer.print("%{s}", .{v.name}),
                .function => |v| try v.formatWriter(writer, null, self.parser),
            }
        }
    };

    pub fn Fmt(type_id: TypeId, parser: *const Parser) _Fmt {
        return .{
            .parser = parser,
            .type_id = type_id,
        };
    }
};

/// Just a `Token`, extract names from the source if necessary.
pub const TypeAttribute = Token;
// TODO change this into a `Token.Kind`

pub const IntegerType = struct {
    bits: u32,
};

pub const FunctionType = struct {
    ret: TypeId,
    ret_attr: []const TypeAttribute,
    
    args: []const TypeId,
    attrs: [][]const TypeAttribute,

    is_vararg: bool,

    pub fn formatWriter(self: FunctionType, writer: *Writer, optional_name: ?[]const u8, parser: *const Parser) Writer.Error!void {
        try writer.print("define ", .{});
        for (self.ret_attr) |attr| {
            try writer.print("{s}", .{attr.loc.slice(parser.lexer.b)});
            try writer.print(" ", .{});
        }
        try writer.print("{f}", .{self.ret.Fmt(parser)});

        if (optional_name) |name| {
            try writer.print(" @{s}(", .{name});
        } else {
            try writer.print(" (", .{});
        }
        for (self.args, self.attrs, 0..) |arg, attrs, i| {
            try writer.print("{f}", .{arg.Fmt(parser)});
            for (attrs) |attr| {
                try writer.print(" ", .{});
                try writer.print("{s}", .{attr.loc.slice(parser.lexer.b)});
            }
            try writer.print(" %{}", .{i});
            if (i + 1 < self.args.len) {
                try writer.print(", ", .{});
            }
        }
        if (self.is_vararg) {
            try writer.print(", ...", .{});
        }
        try writer.print(")", .{});
        try writer.flush();
    }
};

/// `name` is owned by TypeTable.
pub const NamedType = struct {
    // local var
    name: []const u8,
};

// the introduction of `NamedType` (and forward declarations) breaks TypeId equality,
// you can't rely on it

// TODO method to normalise types to allow equality

/// `xs` is owned by TypeTable.
pub const StructType = struct {
    xs: []const TypeId,
};

pub const VectorType = struct {
    x: TypeId,
    elements: usize,
};

pub const ArrayType = struct {
    x: TypeId,
    elements: usize,
};

pub const TypeExtra = union(enum) {
    integer: IntegerType,
    @"struct": StructType,
    vector: VectorType,
    array: ArrayType,
    named: NamedType,
    function: FunctionType,

    fn makeOwned(extra: *TypeExtra, allocator: Allocator) !void {
        switch (extra.*) {
            .@"struct" => |*v| {
                v.xs = try allocator.dupe(TypeId, v.xs);
            },
            .named => |*v| {
                v.name = try allocator.dupe(u8, v.name);
            },
            .function => |*v| {
                v.ret_attr = try allocator.dupe(TypeAttribute, v.ret_attr);

                v.args = try allocator.dupe(TypeId, v.args);
                const new_attrs = try allocator.alloc([]const TypeAttribute, v.attrs.len);
                for (v.attrs, 0..) |xs, i| {
                    new_attrs[i] = try allocator.dupe(TypeAttribute, xs);
                }
                v.attrs = new_attrs;
            },
            else => {},
        }
    }
};

const TypeExtraContext = struct {  
    pub fn hash(self: @This(), key: TypeExtra) u32 {  
        _ = self;  
        var hasher = std.hash.Wyhash.init(0);  
        std.hash.autoHashStrat(&hasher, key, .Deep);  
        return @truncate(hasher.final());  
    }  
      
    pub fn eql(self: @This(), a: TypeExtra, b: TypeExtra, b_index: usize) bool {  
        _ = self;
        _ = b_index;
        return deepEql(a, b, .DeepRecursive);
    }
};

pub const TypeTable = struct {
    // `true` => store the hash, equality is a bit slow here
    map: std.ArrayHashMapUnmanaged(TypeExtra, void, TypeExtraContext, true),

    // note that `StringHashMap` does NOT own the keys
    named_types: std.StringHashMapUnmanaged(?TypeId),

    const index_offset = @typeInfo(TypeId).@"enum".fields.len;

    pub const init: TypeTable = .{
        .map = .empty,
        .named_types = .empty,
    };    

    /// Memory inside `entry` is copied safely.
    pub fn intern(self: *TypeTable, allocator: Allocator, entryv: TypeExtra) !TypeId {
        if (self.map.getIndex(entryv)) |idx| {
            return @enumFromInt(idx + index_offset);
        }

        var entry = entryv;

        // `entry` definitely does not exist
        try entry.makeOwned(allocator);

        const idx = self.map.count();
        try self.map.put(allocator, entry, {});
        const type_id: TypeId = @enumFromInt(idx + index_offset);

        switch (entry) {
            .named => |v| {
                // insert `null` (forward declaration) if it doesn't exist
                const gop = try self.named_types.getOrPut(allocator, v.name);
                if (!gop.found_existing) {
                    gop.value_ptr.* = null;
                }
            },
            else => {},
        }

        return type_id;
    }

    pub fn defineNamed(self: *TypeTable, named_type: TypeId, type_id: TypeId) void {
        const extra_part = self.extra(named_type);
        const name = extra_part.named.name;
        // this must already exist from `internExtra`
        self.named_types.putAssumeCapacity(name, type_id);
    }

    pub fn getNamed(self: *TypeTable, named_type: TypeId) ?TypeId {
        const extra_part = self.extra(named_type);
        const name = extra_part.named.name;
        return self.getNamedDirect(name);
    }

    pub fn getNamedDirect(self: *TypeTable, name: []const u8) ?TypeId {
        return self.named_types.get(name)
            orelse unreachable; // exists in `self.named_type`,
    }

    /// Will fail assert if `typeId` is a primitive.
    pub fn extra(self: *const TypeTable, type_id: TypeId) TypeExtra {
        var idx = @intFromEnum(type_id);
        assert(idx >= index_offset);
        idx -= index_offset;
        return self.map.entries.get(idx).key;
    }

    pub fn deinit(self: *TypeTable, allocator: Allocator) void {
        for (0..self.map.count()) |i| {
            const data = self.map.entries.get(i);
            switch (data.key) {
                .integer => {},
                .@"struct" => |v| allocator.free(v.xs),
                .vector => {},
                .array => {},
                .named => |v| allocator.free(v.name), // (1)
                .function => |v| {
                    allocator.free(v.args);
                    allocator.free(v.ret_attr);
                    for (v.attrs) |xs| {
                        allocator.free(xs);
                    }
                    allocator.free(v.attrs);
                },
            }
        }

        // the owned memory for NamedType is referenced in two places,
        // 1. the `self.map` entries, exactly once,
        // 2. the `self.named_types` map, exactly once.

        // hence, there is no need to free the keys, as we did it above in (1)

        self.map.deinit(allocator);
        self.named_types.deinit(allocator);
    }
};
