const std = @import("std");
const Lexer = @import("Lexer.zig");
const llvm_types = @import("llvm_types.zig");
const llvm_module = @import("llvm_module.zig");

const assert = std.debug.assert;
const TypeTable = llvm_types.TypeTable;
const TypeId = llvm_types.TypeId;
const TypeAttribute = llvm_types.TypeAttribute;
const Token = Lexer.Token;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const FmtContext = llvm_types.FmtContext;

const Function = llvm_module.Function;
const ModuleObject = llvm_module.ModuleObject;

const Parser = @This();

allocator: Allocator,
lexer: Lexer,

tok: Token,
peek: Token,

type_table: TypeTable,

// owned keys
module_objects: std.StringHashMapUnmanaged(*ModuleObject),

has_init: bool,

pub fn init(buffer: [:0]const u8, allocator: Allocator) Parser {
    return .{
        .lexer = Lexer.init(buffer),
        .allocator = allocator,

        .tok = undefined,
        .peek = undefined,
        
        .type_table = .init,
        .module_objects = .empty,
        
        .has_init = false,
    };
}

pub fn deinit(self: *Parser) void {
    self.lexer.deinit(self.allocator);
    self.type_table.deinit(self.allocator);

    var iter = self.module_objects.iterator();
    while (iter.next()) |ent| {
        self.allocator.free(ent.key_ptr.*);
        ent.value_ptr.*.deinit(self.allocator);
    }
    self.module_objects.deinit(self.allocator);
}

const ParserError = error{
    // unrecoverable errors

    // TODO most of these are perfectly recoverable,
    // but you'd need to throw away the function for some
    LexerError,
    NoSummaryEntry,
    NoMetadataInDeclare,
    NoTypedPointers,
    NoStringAttribute,
    NoPrefixOrPrologue,
    NoPersonality,
    NoGC,
    
    ExpectedToken,
    UnExpectedToken,
};

fn nextTok(self: *Parser) !void {
    self.tok = self.peek;
    self.peek = try self.lexer.next(self.allocator);

    if (self.tok.kind == .err) {
        return ParserError.LexerError;
    }
}

/// Ignores tokens right until and skips `kind`.
fn ignoreUntilSkip(self: *Parser, kind: Token.Kind) !void {
    while (true) {
        if (self.tok.kind == kind) {
            try self.nextTok();
            break;
        }
        if (self.tok.kind == .eof) {
            return ParserError.ExpectedToken;
        }
        try self.nextTok();
    }
}

/// Ignores tokens right until and skips `kind`, with respect to nesting.
/// Will consider the first token `self.tok.kind` and increment the internal nest counter if it is `lkind`.
fn ignoreUntilSkipNested(self: *Parser, nest_st: u32, lkind: Token.Kind, rkind: Token.Kind) !void {
    try self.nextTok();
    var nest: isize = -1;
    while (true) {
        if (self.tok.kind == lkind) {
            if (nest == -1) {
                nest = nest_st;
            }

            nest += 1;
        } else if (self.tok.kind == rkind) {
            if (nest == -1) {
                nest = nest_st;
            }

            if (nest == 0) {
                return error.ExpectedToken;
            }
            nest -= 1;
        }
        try self.nextTok();
        if (nest == 0) {
            break;
        }
    }
}

/// Try to incrementally parse, returns errors
pub fn next(self: *Parser) !?void {
    if (!self.has_init) {
        try self.nextTok();
        try self.nextTok();
        self.has_init = true;
    }
    
    while (true) {
        if (self.tok.kind == .eof) {
            return null;
        }

        switch (self.tok.kind) {
            // will not support or attempt to skip ThinLTO summary entries
            .summary_id => return ParserError.NoSummaryEntry,

            // ignore: target ... = 'string'
            .target => try self.ignoreUntilSkip(.string_constant),
            // ignore: source_filename ... = 'string'
            .source_filename => try self.ignoreUntilSkip(.string_constant),

            .declare => try self.parseDeclare(),

            else => return ParserError.UnExpectedToken,
        }
    }
}

fn parseDeclare(self: *Parser) !void {
    try self.nextTok();

    // TODO will not support or attempt to skip metadata attachements on declare
    if (self.tok.kind == .metadata_var) {
        return ParserError.NoMetadataInDeclare;
    }

    const func = try self.parseFunctionHeader();

    const name = try self.allocator.dupe(u8, func.name.loc.slice(self.lexer.b));
    errdefer self.allocator.free(name);

    const gop = try self.module_objects.getOrPut(self.allocator, name);
    if (!gop.found_existing) {
        const obj = try self.allocator.create(ModuleObject);
        errdefer self.allocator.free(obj);

        obj.* = .{ .function = func };
        gop.value_ptr.* = obj;
    } else {
        self.allocator.free(name);
    }
}

fn parseFunctionHeader(self: *Parser) !Function {
    // ... [linkage] [visibility] [DLLStorageClass]
    //    [cconv] [ret attrs]
    //    <ResultType> @<FunctionName> ([argument list])
    //    [(unnamed_addr|local_unnamed_addr)] [align N] [gc]
    //    [prefix Constant] [prologue Constant]

    // skip all the optional things
    while (self.tok.kind.forgettable()) {
        try self.nextTok();
        // ::= 'cc' UINT
        if (self.tok.kind == .integer_literal) {
            try self.nextTok();
        }
    }

    const ret_attr = try self.parseOptionalAttrs();
    const ret_type = try self.parseType();
    defer self.allocator.free(ret_attr);

    // ... @<FunctionName> ([argument list])
    //     ^^^^^^^^^^^^^^^
    if (!(self.tok.kind == .global_var or self.tok.kind == .global_id)) {
        return ParserError.ExpectedToken;
    }

    const name = self.tok;
    try self.nextTok();

    const type_id, const arg_names = try self.parseFunctionType(ret_type, ret_attr);

    while (self.tok.kind.forgettable()) {
        // unnamed_addr, local_unnamed_addr, gc
        try self.nextTok();
    }
    const function_attrs = try self.parseOptionalAttrs();
    while (true) {
        // [align N]
        if (self.tok.kind == .@"align") {
            try self.nextTok();
            try self.expect(.integer_literal);
        } else if (self.tok.kind == .prefix or self.tok.kind == .prologue) {
            return ParserError.NoPrefixOrPrologue;
        } else if (self.tok.kind == .personality) {
            return ParserError.NoPersonality;
        } else if (self.tok.kind == .gc) {
            return ParserError.NoGC;
        } else {
            break;
        }
    }

    return .{
        .name = name,
        .type_id = type_id,
        .arg_names = arg_names,
        .function_attrs = function_attrs,
    };
}

const AnchorErrorSet = ParserError
    || error{OutOfMemory}
    || error{Overflow, InvalidCharacter};

fn parseType(self: *Parser) AnchorErrorSet!TypeId {
    const skipReturn = struct {
        inline fn skipReturn(s: *Parser, type_id: TypeId) !TypeId {
            try s.nextTok();
            return type_id;
        }
    }.skipReturn;
    
    var result: TypeId = blk: switch (self.tok.kind) {
        // cannot and will not support
        .metadata, .token, .label => try skipReturn(self, .invalid_type),
        .@"void" => try skipReturn(self, .@"void"),
        .half => try skipReturn(self, .half),
        .bfloat => try skipReturn(self, .bfloat),
        .float => try skipReturn(self, .float),
        .double => try skipReturn(self, .double),
        .x86_fp80 => try skipReturn(self, .x86_fp80),
        .fp128 => try skipReturn(self, .fp128),
        .ppc_fp128 => try skipReturn(self, .ppc_fp128),
        .x86_amx => try skipReturn(self, .x86_amx),
        .ptr => {
            // := 'addrspace' '(' uint32 ')'
            if (self.peek.kind == .@"addrspace") {
                try self.ignoreUntilSkip(.rparen); // after ')'
            }
            try self.nextTok();
            break :blk .ptr;
        },
        .integer_type => {
            //    i32
            //    ^^^
            // skip the `i`.
            const str = self.tok.loc.slice(self.lexer.b)[1..];
            const bits = try std.fmt.parseInt(u32, str, 10);

            try self.nextTok();
            break :blk try self.type_table.intern(self.allocator, .{
                .integer = .{ .bits = bits },
            });
        },
        .target => {
            // target("label")
            // target("label", void)
            try self.ignoreUntilSkip(.rparen); // after ')'
            break :blk .invalid_type;
        },
        // Type ::= StructType
        .lbrace => break :blk try self.parseStructType(),
        // Type ::= '[' ... ']'
        .lsquare => break :blk try self.parseArrayVectorType(),
        .less => {
            // "Either vector or packed struct."
            // Type ::= '<' ... '>'

            if (self.peek.kind == .lbrace) {
                // packed struct
                try self.nextTok();
                _ = try self.parseStructType();
                try self.expect(.greater);

                // will not support packed structs, although the infrastructure is there
                break :blk .invalid_type;
            }
            break :blk try self.parseArrayVectorType();
        },
        // %name, %1 are done the same way
        .local_var, .local_var_id => {
            const str = self.tok.loc.slice(self.lexer.b);
            try self.nextTok();
            break :blk try self.type_table.intern(self.allocator, .{
                .named = .{ .name = str },
            });
        },
        else => return ParserError.ExpectedToken,
    };
    
    // parse type suffixes
    while (true) switch (self.tok.kind) {
        // will not support typed pointers, deprecated anyway
        // Type ::= Type '*'
        // Type ::= Type 'addrspace' '(' uint32 ')' '*'
        .star, .@"addrspace" => {
            return ParserError.NoTypedPointers;
        },

        // Types '(' ArgTypeListI ')' OptFuncAttrs
        .lparen => {
            result, const arg_names = try self.parseFunctionType(result, &[0]TypeAttribute{});
            self.allocator.free(arg_names); // we don't need these
        },

        // end of type
        else => break,
    };
    return result;
}

/// The return value is owned.
fn parseOptionalAttrs(self: *Parser) ![]const TypeAttribute {
    // parseOptionalParamOrReturnAttrs
    // "Parse a potentially empty list of parameter or return attributes."

    // this is supposed to be a set, but it doesn't matter and unlikely has duplicated elements
    var xs: std.ArrayList(Token.Kind) = .empty;
    defer xs.deinit(self.allocator);

    // https://llvm.org/docs/LangRef.html#parameter-attributes
    //
    //     ; On function declarations/definitions:
    //     declare i32 @printf(ptr noalias captures(none), ...)
    //     declare i32 @atoi(i8 zeroext)
    //     declare signext i8 @returns_signed_char()
    //     define void @baz(i32 "amdgpu-flat-work-group-size"="1,256" %x)
    //
    //     ; On call-sites:
    //     call i32 @atoi(i8 zeroext %x)
    //     call signext i8 @returns_signed_char()
    //
    while (true) {
        // will ignore string attributes
        if (self.tok.kind == .string_constant) {
            // parseStringAttribute
            //   := StringConstant
            //   := StringConstant '=' StringConstant
            try self.nextTok();
            if (self.tok.kind == .equal) {
                try self.nextTok();
                try self.expect(.string_constant);
            }
            continue;
        }

        // skip all of the attributes that take parameters, they're pretty useless
        if (self.tok.kind.isAttributeParen()) {
            try self.ignoreUntilSkipNested(0, .lparen, .rparen);
            continue;
        } else if (self.tok.kind == .@"align") {
            try self.nextTok();
            if (self.tok.kind == .integer_literal) {
                try self.nextTok();
            } else {
                try self.expect(.lparen);
                try self.expect(.integer_literal);
                try self.expect(.rparen);
            }
            continue;
        }

        // this is _probably_ not an attribute
        if (!(self.tok.kind.isAttributesAndBeyond() or self.tok.kind == .attr_grp_id)) {
            break;
        }
        
        // identifiers and group ids #1
        try xs.append(self.allocator, self.tok.kind);
        try self.nextTok();
    }

    return try xs.toOwnedSlice(self.allocator);
}

/// Parse the function type, given the return type is already parsed.
fn parseFunctionType(self: *Parser, ret_type: TypeId, ret_attr: []const TypeAttribute) !struct { TypeId, []const Token } {
    // Types '(' ArgTypeListI ')' OptFuncAttrs
    //       ^^^
    assert(self.tok.kind == .lparen);
    try self.nextTok();

    // the function type will store the return, parameter types and attributes.
    // separately, the argument names will be returned

    // (type, attribute) pair
    var args: ArrayList(TypeId) = try .initCapacity(self.allocator, 4);
    defer args.deinit(self.allocator);

    var arg_attrs: ArrayList([]const TypeAttribute) = try .initCapacity(self.allocator, 4);
    defer {
        for (arg_attrs.items) |xs| {
            self.allocator.free(xs);
        }
        arg_attrs.deinit(self.allocator);
    }

    var arg_names: ArrayList(Token) = .empty;
    defer arg_names.deinit(self.allocator);

    var is_invalid_type = false;
    var is_vararg = false;

    // "parseArgumentList - parse the argument list for a function type or function
    // prototype."
    //   ::= '(' ArgTypeListI ')'
    // ArgTypeListI
    //   ::= /*empty*/
    //   ::= '...'
    //   ::= ArgTypeList ',' '...'
    //   ::= ArgType (',' ArgType)*
    //
    while (self.tok.kind != .rparen) {
        if (args.items.len > 0) {
            try self.expect(.comma);
        }

        if (self.tok.kind == .dotdotdot) {
            try self.nextTok();
            is_vararg = true;
            break;
        }

        const type_id = try self.parseType();
        const attributes = try self.parseOptionalAttrs();

        if (type_id == .invalid_type) {
            is_invalid_type = true;
        }

        // call i32 @atoi(i8 zeroext %x)
        //                           ^^
        if (self.tok.kind == .local_var or self.tok.kind == .local_var_id) {
            // we assume that a function type either has all arguments, or none at all
            try arg_names.append(self.allocator, self.tok);
        }

        try args.append(self.allocator, type_id);
        try arg_attrs.append(self.allocator, attributes);
    }
    try self.expect(.rparen); // skip past ')'

    if (arg_names.items.len > 0) {
        assert(args.items.len == arg_names.items.len);
    }

    if (is_invalid_type) {
        return .{ .invalid_type, &[0]Token{} };
    }

    const function_type = try self.type_table.intern(self.allocator, .{
        .function = .{
            .ret = ret_type,
            .ret_attr = ret_attr,

            .args = args.items,
            .attrs = arg_attrs.items,

            .is_vararg = is_vararg,
        }
    });
    const arg_names_owned = try arg_names.toOwnedSlice(self.allocator);
    return .{ function_type, arg_names_owned };
}

fn parseStructType(self: *Parser) !TypeId {
    // "parseStructType: Handles packed and unpacked types.  </> parsed elsewhere."
    //   StructType
    //     ::= '{' '}'
    //     ::= '{' Type (',' Type)* '}'
    //     ::= '<' '{' '}' '>'
    //     ::= '<' '{' Type (',' Type)* '}' '>'

    assert(self.tok.kind == .lbrace);
    var xs: ArrayList(TypeId) = try .initCapacity(self.allocator, 4);
    defer xs.deinit(self.allocator);

    try self.nextTok();
    if (self.tok.kind != .rbrace) {
        // not {}
        const type_id0 = try self.parseType();
        try xs.append(self.allocator, type_id0);

        // usually we would short ciruit on invalid type and return invalid type,
        // but struct types can't have anything invalid by default.

        // we don't validate the types for a struct.
        // StructType::isValidElementType

        while (self.tok.kind == .comma) {
            try self.nextTok();
            const type_id = try self.parseType();
            try xs.append(self.allocator, type_id);
        }
    }

    try self.expect(.rbrace);
    try self.nextTok();

    const struct_type_id = try self.type_table.intern(self.allocator, .{
        .@"struct" = .{
            .xs = xs.items,
        },
    });

    return struct_type_id;
}

fn expect(self: *Parser, kind: Token.Kind) !void {
    if (self.tok.kind != kind) {
        return ParserError.ExpectedToken;
    }
    try self.nextTok();
}

fn expectNoNext(self: *Parser, kind: Token.Kind) !void {
    if (self.tok.kind != kind) {
        return ParserError.ExpectedToken;
    }
}

fn parseArrayVectorType(self: *Parser) !TypeId {
    // "parseArrayVectorType - parse an array or vector type, assuming the first
    // token has already been consumed."
    //   Type
    //     ::= '[' APSINTVAL 'x' Types ']'
    //     ::= '<' APSINTVAL 'x' Types '>'
    //     ::= '<' 'vscale' 'x' APSINTVAL 'x' Types '>'

    // we do not assume the first token has been consumed
    assert(self.tok.kind == .less or self.tok.kind == .lsquare);

    const is_vector = self.tok.kind == .less;
    try self.nextTok();

    if (self.tok.kind == .vscale) {
        // will not support vscale
        try self.ignoreUntilSkip(.greater);
        return .invalid_type;
    }

    const iloc = self.tok.loc;
    try self.expect(.integer_literal);
    const elements = try iloc.unsigned(self.lexer.b);
    try self.expect(.x);

    const elm_type_id = try self.parseType();
    try self.expect(if (is_vector) .greater else .rsquare);

    // vectors can store our invalid types
    if (elm_type_id == .invalid_type) {
        return .invalid_type;
    }

    if (is_vector) {
        return try self.type_table.intern(self.allocator, .{
            .vector = .{
                .x = elm_type_id,
                .elements = elements,
            },
        });
    } else {
        return try self.type_table.intern(self.allocator, .{
            .array = .{
                .x = elm_type_id,
                .elements = elements,
            },
        });
    }
}

test "declare" {
    const allocator = std.testing.allocator;
    const expectEqualStrings = std.testing.expectEqualStrings;
    const expectEqualSlices = std.testing.expectEqualSlices;

    const buffer =
        \\declare signext i8 @puts(ptr noalias captures(none), ...) nounwind
    ;

    var parser = Parser.init(buffer, allocator);
    defer parser.deinit();

    errdefer {
        std.debug.print("{s}\n", .{buffer});
        std.debug.print("curr {}\n", .{parser.tok});
        std.debug.print("peek {}\n", .{parser.peek});
    }

    while (try parser.next()) |_| {
        // something
    }

    const obj = parser.module_objects.get("puts") orelse unreachable;
    const function = &obj.function;

    const nounwind_ident = try parser.lexer.token_map.intern(allocator, "nounwind");

    try expectEqualStrings("puts", function.name.loc.slice(buffer));
    try expectEqualSlices(TypeAttribute, &[_]TypeAttribute{ nounwind_ident }, function.function_attrs);

    const function_repr = try std.fmt.allocPrint(allocator, "{f}", .{FmtContext(&parser, function.type_id)});
    defer allocator.free(function_repr);

    try expectEqualStrings("define signext i8 (ptr noalias %0, ...)", function_repr);
}
