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

const Function = llvm_module.Function;
const Global = llvm_module.Global;
const PseudoArgument = llvm_module.PseudoArgument;
const Inst = llvm_module.Inst;
const BasicBlock = llvm_module.BasicBlock;
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
lf_aware: bool,

pub fn init(buffer: [:0]const u8, allocator: Allocator) Parser {
    return .{
        .lexer = Lexer.init(buffer),
        .allocator = allocator,

        .tok = undefined,
        .peek = undefined,
        
        .type_table = .init,
        .module_objects = .empty,
        
        .has_init = false,
        .lf_aware = false,
    };
}

pub fn deinit(self: *Parser) void {
    self.lexer.deinit(self.allocator);
    self.type_table.deinit(self.allocator);

    var iter = self.module_objects.iterator();
    while (iter.next()) |ent| {
        // no need to free the key, because the memory is shared with the Function
        // self.allocator.free(ent.key_ptr.*);
        ent.value_ptr.*.deinitSelf(self.allocator);
    }
    self.module_objects.deinit(self.allocator);
}

const ParserError = error{
    // unrecoverable errors

    // TODO most of these are perfectly recoverable,
    // but you'd need to throw away the function for some
    LexerError,
    NoSummaryEntry,
    NoTypedPointers,
    NoStringAttribute,
    NoPrefixOrPrologue,
    NoPersonality,
    NoGC,
    NoHashDebugRecords,
    NoAliasOrIFunc,
    
    ExpectedToken,
    UnexpectedToken,
};

fn nextTokInner(self: *Parser, emit_newline: bool) !void {

    self.tok = self.peek;
    self.peek = try self.lexer.nextInner(self.allocator, emit_newline);

    // will remove newlines
    if (self.tok.kind == .newline and !emit_newline) {
        self.tok = self.peek;
        self.peek = try self.lexer.nextInner(self.allocator, false);
    }
    if (!emit_newline) {
        assert(self.tok.kind != .newline);
    }

    if (self.tok.kind == .err) {
        return ParserError.LexerError;
    }
}

fn nextTok(self: *Parser) !void {
    return self.nextTokInner(self.lf_aware);
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
            .define => try self.parseDefine(),

            .local_var, .local_var_id => try self.parseTypeDecl(),
            .global_var, .global_id => try self.parseGlobalDecl(),

            else => return ParserError.UnexpectedToken,
        }
    }
}

fn parseDeclare(self: *Parser) !void {
    try self.nextTok();

    // "parseOptionalFunctionMetadata"
    try self.skipMetadata();
    var f = try self.parseFunctionHeader();
    errdefer f.deinit(self.allocator);

    const gop = try self.module_objects.getOrPut(self.allocator, f.name);
    if (!gop.found_existing) {
        const obj = try self.allocator.create(ModuleObject);
        errdefer self.allocator.free(obj);

        obj.* = .{ .function = f };
        gop.value_ptr.* = obj;
    }
}

fn parseDefine(self: *Parser) !void {
    try self.nextTok();

    var f = try self.parseFunctionHeader();
    errdefer f.deinit(self.allocator);
    
    // "parseOptionalFunctionMetadata"
    try self.skipMetadata();

    // "parseFunctionBody"
    //   ::= '{' BasicBlock+ UseListOrderDirective* '}'
    //       ^^^
    try self.expect(.lbrace);
    self.lf_aware = true;

    var first = true;
    while (self.tok.kind != .rbrace) {
        try self.parseBasicBlock(&f, first);
        first = false;
    }

    self.lf_aware = false;
    try self.nextTok();

    const gop = try self.module_objects.getOrPut(self.allocator, f.name);
    if (!gop.found_existing) {
        const obj = try self.allocator.create(ModuleObject);
        errdefer self.allocator.free(obj);

        obj.* = .{ .function = f };
        gop.value_ptr.* = obj;
    } else {
        var new_f = &gop.value_ptr.*.function;
        new_f.bbs.deinit(self.allocator);
        new_f.bbs = f.bbs.move();
        f.deinit(self.allocator);
    }
}

fn parseTypeDecl(self: *Parser) !void {
    // toplevelentity
    //   ::= LocalVar '=' 'type' type
    //   ::= LocalVarID '=' 'type' type
    assert(self.tok.kind == .local_var or self.tok.kind == .local_var_id);

    const name = self.tok.loc.slice(self.lexer.b);
    try self.nextTok();

    try self.expect(.equal);
    try self.expect(.@"type");

    const type_id = try self.parseType();
    const decl_type_id = try self.type_table.intern(self.allocator, .{ .named = .{ .name = name } });

    self.type_table.defineNamed(decl_type_id, type_id);
}

fn parseGlobalDecl(self: *Parser) !void {
    var g = try self.parseGlobal();
    errdefer g.deinit(self.allocator);
    
    const gop = try self.module_objects.getOrPut(self.allocator, g.name);
    if (!gop.found_existing) {
        const obj = try self.allocator.create(ModuleObject);
        errdefer self.allocator.free(obj);

        obj.* = .{ .global = g };
        gop.value_ptr.* = obj;
    } else {
        var new_g = &gop.value_ptr.*.global;
        assert(new_g.value == null);

        new_g.value = g.value; // move
        g.value = .poison;
        g.deinit(self.allocator);
    }
}

fn parseGlobal(self: *Parser) !Global {
    // "parseUnnamedGlobal:"
    //   GlobalID '=' OptionalVisibility (ALIAS | IFUNC) ...
    //   GlobalID '=' OptionalLinkage OptionalPreemptionSpecifier
    //   OptionalVisibility
    //                OptionalDLLStorageClass
    //                                                     ...   -> global variable
    // "parseNamedGlobal:"
    //   GlobalVar '=' OptionalVisibility (ALIAS | IFUNC) ...
    //   GlobalVar '=' OptionalLinkage OptionalPreemptionSpecifier
    //                 OptionalVisibility OptionalDLLStorageClass
    //                                                     ...   -> global variable
    assert(self.tok.kind == .global_var or self.tok.kind == .global_id);

    const name = try self.tok.loc.sliceAlloc(self.allocator, self.lexer.b);
    errdefer self.allocator.free(name);
    try self.nextTok();

    try self.expect(.equal);

    var has_initialiser = true;

    // skip all the optional things
    while (self.tok.kind.forgettable()) {
        // "If the linkage is specified and is external, then no initializer is present."
        // "isValidDeclarationLinkage"
        if (self.tok.kind == .extern_weak or self.tok.kind == .external) {
            has_initialiser = false;
        }
        // "parseOptionalThreadLocal"
        //   := /*empty*/
        //   := 'thread_local'
        //   := 'thread_local' '(' tlsmodel ')'
        if (self.tok.kind == .thread_local and self.peek.kind == .lparen) {
            try self.ignoreUntilSkip(.rparen);
            continue;
        }
        try self.nextTok();
    }

    switch (self.tok.kind) {
        .alias, .ifunc => return ParserError.NoAliasOrIFunc,
        else => {},
    }

    // := 'addrspace' '(' uint32 ')'
    if (self.peek.kind == .@"addrspace") {
        try self.ignoreUntilSkip(.rparen); // after ')'
    }
    while (self.tok.kind.forgettable()) {
        // externally_initialized
        try self.nextTok();
    }

    // "parseGlobalType"
    //   ::= 'constant'
    //   ::= 'global'
    var is_constant = false;
    switch (self.tok.kind) {
        .global => is_constant = true,
        .constant => {},
        else => return ParserError.ExpectedToken,
    }
    try self.nextTok();

    var alignment: ?u64 = null;
    var value: ?PseudoArgument = null;
    errdefer {
        if (value) |v| {
            v.deinit(self.allocator);
        }
    }

    const type_id = try self.parseType();
    if (has_initialiser) {
        value = try self.parsePseudoArgument(true, null);

        while (self.tok.kind == .comma) {
            try self.nextTok();
            if (self.tok.kind == .@"align") {
                try self.nextTok();
                const curr = self.tok;
                try self.expect(.integer_literal);
                alignment = try curr.loc.unsigned(self.lexer.b);
            }
        }
        // we should be at a newline here
    }

    return .{
        .name = name,
        .type_id = type_id,
        .value = value,
        .is_constant = is_constant,
        .alignment = alignment,
    };
}

fn skipMetadata(self: *Parser) !void {
    while (self.tok.kind == .metadata_var) {
        try self.nextTok();
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
    // "parseFnAttributeValuePairs"
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

    const dup = try name.loc.sliceAlloc(self.allocator, self.lexer.b);
    errdefer self.allocator.free(dup);

    return .{
        .name = dup,
        .type_id = type_id,
        .arg_names = arg_names,
        .function_attrs = .{ .attrs = function_attrs },
        .bbs = .empty,
    };
}

const ParseTypeAnchorErrorSet = ParserError
    || error{OutOfMemory}
    || error{Overflow, InvalidCharacter};

fn parseType(self: *Parser) ParseTypeAnchorErrorSet!TypeId {
    const skipReturn = struct {
        inline fn skipReturn(s: *Parser, type_id: TypeId) !TypeId {
            try s.nextTok();
            return type_id;
        }
    }.skipReturn;
    
    var result: TypeId = blk: switch (self.tok.kind) {
        // cannot and will not support. will support label separately
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
            for (arg_names) |xs| {
                self.allocator.free(xs);
            }
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
    var xs: std.ArrayList(TypeAttribute) = .empty;
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
        try xs.append(self.allocator, self.tok);
        try self.nextTok();
    }

    return try xs.toOwnedSlice(self.allocator);
}

/// Parse the function type, given the return type is already parsed.
fn parseFunctionType(self: *Parser, ret_type: TypeId, ret_attr: []const TypeAttribute) !struct { TypeId, [][]const u8 } {
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

    var arg_names: ArrayList([]const u8) = .empty;
    defer arg_names.deinit(self.allocator);
    errdefer {
        for (arg_names.items) |xs| {
            self.allocator.free(xs);
        }
    }

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
            const dup = try self.tok.loc.sliceAlloc(self.allocator, self.lexer.b);
            errdefer self.allocator.free(dup);
            
            try arg_names.append(self.allocator, dup);
            try self.nextTok();
        }

        try args.append(self.allocator, type_id);
        try arg_attrs.append(self.allocator, attributes);
    }
    try self.expect(.rparen); // skip past ')'

    if (arg_names.items.len > 0) {
        assert(args.items.len == arg_names.items.len);
    }

    if (is_invalid_type) {
        return .{ .invalid_type, &[0][]const u8{} };
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

// %X = call i32 asm "bswap $0", "=r,r"(i32 %Y)

// %a = load i8, ptr %x, align 1, !range !0 ; Can only be 0 or 1
// %b = load i8, ptr %y, align 1, !range !1 ; Can only be 255 (-1), 0 or 1
// %e = load <2 x i8>, ptr %x, !range 0 ; Can only be <0 or 1, 0 or 1>

// ret i32 5                       ; Return an integer value of 5
// ret void                        ; Return from a void function
// ret { i32, i8 } { i32 4, i8 2 } ; Return a struct of values 4 and 2

// <result> = add <ty> <op1>, <op2>          ; yields ty:result
// <result> = add nuw <ty> <op1>, <op2>      ; yields ty:result
// <result> = add nsw <ty> <op1>, <op2>      ; yields ty:result
// <result> = add nuw nsw <ty> <op1>, <op2>  ; yields ty:result

// switch <intty> <value>, label <defaultdest> [ <intty> <val>, label <dest> ... ]
// <result> = phi [fast-math-flags] <ty> [ <val0>, <label0>], ...
//
//                ^^^^^ check if this is a type first, then eat random tokens until this is a type

// ; Function Attrs: noinline nounwind optnone sspstrong uwtable
// define internal ptr @sqlite3Pcache1Mutex() #0 {
//     %1 = load ptr, ptr getelementptr inbounds nuw (%struct.PCacheGlobal, ptr @pcache1_g, i32 0, i32 9), align 8
//     ret ptr %1
// }

// <result> = udiv exact <ty> <op1>, <op2>   ; yields ty:result

// TODO
// (type, constant), then after that, many constants
// assume [ ... ] isn't an array constant. the only instruction that uses this is landingpad
//        ^^^^^^^ turn this into a proper pseudo argument

const PseudoParserContext = struct {
    // %const.0 for unwrapping constant expressions
    reserved_counter: u32,
    insts: std.ArrayList(Inst),
};

fn pseudoIsTypeBegin(kind: Token.Kind) bool {
    // `label %0` parsed separately, [ ... ] is never parsed as types
    
    return switch (kind) {
        .integer_type => true,
        .lbrace, .less, .lsquare => true,
        else => kind.isType(),
    };
}

/// This will parse arrays into literal LLVM arrays, not fake lists.
fn parseAllListsLiteral(self: *Parser, ctx: ?*PseudoParserContext) !PseudoArgument {
    const begin = self.tok.kind;
    const gate: Token.Kind = switch (begin) {
        .lbrace => .rbrace,
        .less => .greater,
        .lparen => .rparen,
        .lsquare => .rsquare,
        else => unreachable,
    };

    var args: std.ArrayList(PseudoArgument.PseudoPair) = try .initCapacity(self.allocator, 2);
    defer args.deinit(self.allocator);
    errdefer {
        for (args.items) |pair| {
            pair.arg.deinit(self.allocator);
        }
    }

    try self.nextTok();
    while (true) {
        const type_id = try self.parseType();

        // eat the attributes we don't care about
        // (ptr noundef %169)
        // (ptr align 8 @alloc_669)
        if (self.tok.kind.isAttributesAndBeyond()) {
            const attrs = try self.parseOptionalAttrs();
            self.allocator.free(attrs); // we don't need these
        }
        
        {
            const arg = try self.parsePseudoArgument(true, ctx);

            // we have something invalid, quick! skip to the end
            if (arg == .invalid) {
                for (args.items) |pair| {
                    pair.arg.deinit(self.allocator);
                }
                try self.ignoreUntilSkipNested(1, begin, gate);
                return .invalid;
            } else {
                // errdefer shouldn't apply after the append
                errdefer arg.deinit(self.allocator);
                try args.append(self.allocator, .{ .type_id = type_id, .arg = arg });
            }
        }
        if (self.tok.kind == gate) {
            try self.nextTok();
            break;
        } else {
            try self.expect(.comma);
        }
    }

    const args_owned = try args.toOwnedSlice(self.allocator);

    if (gate == .rbrace) {
        // struct    
        return .{ .struct_literal = args_owned };
    } else if (gate == .greater) {
        // vector
        return .{ .vector_literal = args_owned };
    } else if (gate == .rsquare) {
        // array
        return .{ .array_literal = args_owned };
    } else {
        // call list
        return .{ .call_list = args_owned };
    }
}

fn parseListLiteral(self: *Parser, ctx: *PseudoParserContext) !PseudoArgument {
    assert(self.tok.kind == .lsquare);

    var args: std.ArrayList(PseudoArgument) = try .initCapacity(self.allocator, 2);
    defer args.deinit(self.allocator);
    errdefer {
        for (args.items) |arg| {
            arg.deinit(self.allocator);
        }
    }

    while (self.tok.kind != .rsquare) {
        var next_type = true;

        while (self.tok.kind != .comma and self.tok.kind != .rsquare) {
            const is_type = pseudoIsTypeBegin(self.tok.kind);

            const arg = try self.parsePseudoArgument(!next_type, ctx);
            errdefer arg.deinit(self.allocator);
            try args.append(self.allocator, arg);

            if (is_type) {
                next_type = false;
            }
        }
        if (self.tok.kind == .comma) {
            try self.nextTok();
        }
    }
    try self.nextTok();

    return .{ .list = try args.toOwnedSlice(self.allocator) };
}

const ParsePseudoArgumentAnchorErrorSet = ParserError
    || error{Overflow, InvalidCharacter}
    || error{OutOfMemory};

/// When `ctx == null`, this function parses array literals properly as it is assumed to not parse instructions.
fn parsePseudoArgument(self: *Parser, not_type: bool, ctx: ?*PseudoParserContext) ParsePseudoArgumentAnchorErrorSet!PseudoArgument {
    if (self.tok.kind.isConstantInstruction()) {
        if (ctx == null) {
            return .invalid;
        }
        const idx = ctx.?.reserved_counter;
        ctx.?.reserved_counter += 1;

        const inner_lhs = try std.fmt.allocPrint(self.allocator, "const.{}", .{idx});
        errdefer self.allocator.free(inner_lhs);
        
        try self.parseInstruction(inner_lhs, ctx.?);
        return .{ .local_var = inner_lhs };
    }

    if (self.tok.kind == .lparen) {
        return try self.parseAllListsLiteral(ctx.?);
    }

    // "As a special case, character array constants may also be represented as a double-quoted
    // string using the c prefix. For example: c"Hello World\0A\00"."
    if (self.tok.kind == .c) {
        try self.nextTok();
        const str_lit = try self.tok.loc.sliceAlloc(self.allocator, self.lexer.b);
        errdefer self.allocator.free(str_lit);

        try self.expect(.string_constant);
        return .{ .string_array_literal = str_lit };
    }

    // structs or vector literals, but only after a type has been parsed
    if (not_type and (self.tok.kind == .lbrace or self.tok.kind == .less or self.tok.kind == .lsquare)) {
        // are we in instruction parsing mode?
        if (ctx != null and self.tok.kind == .lsquare) {
            return try self.parseListLiteral(ctx.?);
        } else {
            return try self.parseAllListsLiteral(ctx);
        }
    } else if (pseudoIsTypeBegin(self.tok.kind)) {
        const type_id = try self.parseType();
        return .{ .type_id = type_id };
    }

    if (self.tok.kind == .local_var or self.tok.kind == .local_var_id) {
        const str = self.tok.loc.slice(self.lexer.b);

        // this is a type, assuming that `llvm-dis` puts all the types at the top, functions at the bottom
        const arg: PseudoArgument = if (self.type_table.named_types.get(str)) |type_entry| blk: {
            // at this point, no type should be an empty forward declaration
            _ = type_entry orelse unreachable;
            const type_id = try self.type_table.intern(self.allocator, .{ .named = .{ .name = str } });
            break :blk .{ .type_id = type_id };
        } else blk: {
            // this is a normal variable
            const dup = try self.allocator.dupe(u8, str);
            break :blk .{ .local_var = dup };
        };
        errdefer arg.deinit(self.allocator);
        try self.nextTok();
        return arg;
    }

    // label %0
    if (self.tok.kind == .label) {
        try self.nextTok();
        const token = self.tok;
        if (self.tok.kind != .local_var and self.tok.kind != .local_var_id) {
            return ParserError.ExpectedToken;
        }

        const dup = try token.loc.sliceAlloc(self.allocator, self.lexer.b);
        errdefer self.allocator.free(dup);
        try self.nextTok();
        return .{ .label = dup };
    }

    const final_pseudo: PseudoArgument = switch (self.tok.kind) {
        .undef => .undef,
        .poison => .poison,
        .zeroinitializer => .zeroinitializer,
        .@"null" => .@"null",
        .integer_literal => blk: {
            const dup = try self.tok.loc.sliceAlloc(self.allocator, self.lexer.b);
            break :blk .{ .integer_literal = dup };
        },
        .float_literal => blk: {
            const dup = try self.tok.loc.sliceAlloc(self.allocator, self.lexer.b);
            break :blk .{ .float_literal = dup };
        },
        .hex_float_literal => blk: {
            const dup = try self.tok.loc.sliceAlloc(self.allocator, self.lexer.b);
            break :blk .{ .hex_float_literal = dup };
        },
        .global_id, .global_var => blk: {
            const dup = try self.tok.loc.sliceAlloc(self.allocator, self.lexer.b);
            break :blk .{ .global_var = dup };
        },
        else => .{ .token = self.tok.kind },
    };
    errdefer final_pseudo.deinit(self.allocator);
    try self.nextTok();
    return final_pseudo;
}

fn parseInstruction(self: *Parser, lhs: ?[]const u8, ctx: *PseudoParserContext) !void {
    const inst_kind = self.tok.kind;
    try self.nextTok();

    var pseudos: std.ArrayList(PseudoArgument) = try .initCapacity(self.allocator, 3);
    defer pseudos.deinit(self.allocator);
    errdefer {
        for (pseudos.items) |arg| {
            arg.deinit(self.allocator);
        }
    }

    // %x = i32 0 is not possible, it is always instruction first

    // <result> = mul <ty> <op1>, <op2>
    // getelementptr inbounds nuw (%struct.PCacheGlobal, ptr @pcache1_g, i32 0, i32 9)
    //     ^ constant expression

    // walk and collect tokens
    while (self.tok.kind.isAttributesAndBeyond()) {
        try pseudos.append(self.allocator, .{ .token = self.tok.kind });
        try self.nextTok();
    }

    // inside constant expression
    // https://llvm.org/docs/LangRef.html#constant-expressions
    const is_inner = self.tok.kind == .lparen;
    if (is_inner) {
        // we need a result location
        assert(lhs != null);
        try self.nextTok();
    }

    var first_type = true;
    
    while (true) {
        if (is_inner and self.tok.kind == .rparen) {
            try self.nextTok();
            break;
        } else if (!is_inner and self.tok.kind == .newline) {
            try self.nextTok();
            break;
        }
        assert(self.tok.kind != .eof);

        if (self.tok.kind == .comma) {
            try self.nextTok();
        }

        const was_type = pseudoIsTypeBegin(self.tok.kind);

        const arg = try self.parsePseudoArgument(!first_type, ctx);
        errdefer arg.deinit(self.allocator);
        try pseudos.append(self.allocator, arg);

        if (was_type) {
            // <ty> <op>
            first_type = false;
        }
    }

    const inst: Inst = .{
        .lhs = lhs,
        .kind = inst_kind,
        .args = try pseudos.toOwnedSlice(self.allocator),
    };
    errdefer inst.deinit(self.allocator);
    try ctx.insts.append(self.allocator, inst);
}

fn parseBasicBlock(self: *Parser, f: *Function, first: bool) !void {
    // "parseBasicBlock"
    //   ::= (LabelStr|LabelID)? Instruction*

    // the first basic block cannot have precedessors
    var label_name: []const u8 = undefined;
    if (first and self.tok.kind != .label_literal) {
        label_name = try self.allocator.dupe(u8, "start");
    } else {
        label_name = try self.tok.loc.sliceAlloc(self.allocator, self.lexer.b);
        errdefer self.allocator.free(label_name);
        try self.expect(.label_literal);
    }
    errdefer self.allocator.free(label_name);

    var ctx: PseudoParserContext = .{
        .insts = try .initCapacity(self.allocator, 4),
        .reserved_counter = 0,
    };
    errdefer ctx.insts.deinit(self.allocator);
    errdefer {
        for (ctx.insts.items) |inst| {
            inst.deinit(self.allocator);
        }
    }

    while (true) {
        // https://llvm.org/docs/LangRef.html#debugrecords
        //
        //     %inst1 = op1 %a, %b
        //       #dbg_value(%inst1, !10, !DIExpression(), !11)
        //     %inst2 = op2 %inst1, %c
        //
        if (self.tok.kind == .hash) {
            return ParserError.NoHashDebugRecords;
        }

        while (self.tok.kind == .newline) {
            try self.nextTok();
        }

        // ?[]const u8
        const lhs = if (self.tok.kind == .local_var or self.tok.kind == .local_var_id) blk: {
            const curr = self.tok;

            const dup = try curr.loc.sliceAlloc(self.allocator, self.lexer.b);
            errdefer self.allocator.free(dup);
            
            try self.nextTok();
            try self.expect(.equal);
            break :blk dup;
        } else null;
        // we want `.newline` tokens from now on, hence the usage of `*Lf` functions.
        // LLVM has many instructions, i value my time, so im just going to use a
        // newline aware lazy way of parsing.
        //
        // note that `llvm-naive` assumes input that is the output of `llvm-dis`

        // %0 = inst
        //      ^^^^
        //
        // unreachable [\n]
        // ^^^^^^^^^^^

        // walk until we have a newline, then this is the entire instruction

        // among some of the instructions that don't terminate in a newline, like
        // switch ... [], we can just match until. instructions like `phi`, no matter
        // how long it gets, `llvm-dis` will always output it all on one line
        try self.parseInstruction(lhs, &ctx);

        while (self.tok.kind == .newline) {
            try self.nextTok();
        }
        if (self.tok.kind == .label_literal or self.tok.kind == .rbrace) {
            break;
        }
    }

    const bb: BasicBlock = .{
        .name = label_name,
        .insts = ctx.insts,
    };

    try f.bbs.put(self.allocator, bb.name, bb);
}

test "declare" {
    const allocator = std.testing.allocator;
    const expectEqualStrings = std.testing.expectEqualStrings;

    const buffer =
        \\declare signext i8 @puts(ptr noalias captures(none), ...) nounwind #0
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

    const attr_repr = try std.fmt.allocPrint(allocator, "{f}", .{function.function_attrs.Fmt(&parser)});
    defer allocator.free(attr_repr);

    try expectEqualStrings("puts", function.name);
    try expectEqualStrings("nounwind #0", attr_repr);

    const type_repr = try std.fmt.allocPrint(allocator, "{f}", .{function.type_id.Fmt(&parser)});
    defer allocator.free(type_repr);

    try expectEqualStrings("define signext i8 (ptr noalias %0, ...)", type_repr);
}

fn testPieces(pieces: []const []const u8, buf: []const u8) !void {
    for (pieces) |piece| {
        errdefer {
            std.debug.print("couldn't find \"{s}\"\n", .{piece});
        }
        try std.testing.expect(std.mem.containsAtLeast(u8, buf, 1, piece));
    }
}

test "square" {
    const allocator = std.testing.allocator;

    const buffer =
        \\define i32 @square(i32 %num) unnamed_addr {
        \\start:
        \\  %num.dbg.spill = alloca [4 x i8], align 4
        \\  store i32 %num, ptr %num.dbg.spill, align 4
        \\  %0 = call { i32, i1 } @llvm.smul.with.overflow.i32(i32 %num, i32 %num)
        \\  %_2.0 = extractvalue { i32, i1 } %0, 0
        \\  %_2.1 = extractvalue { i32, i1 } %0, 1
        \\  br i1 %_2.1, label %panic, label %bb1
        \\
        \\bb1:
        \\  ret i32 %_2.0
        \\
        \\panic:
        \\  call void @core::panicking::panic_const::panic_const_mul_overflow(ptr align 8 @alloc_669) #3
        \\  unreachable
        \\}
        \\
        \\declare { i32, i1 } @llvm.smul.with.overflow.i32(i32, i32) #1
        \\
        \\declare void @core::panicking::panic_const::panic_const_mul_overflow(ptr align 8) unnamed_addr #2
    ;

    var parser = Parser.init(buffer, allocator);
    defer parser.deinit();

    {
        errdefer {
            std.debug.print("curr {}\n", .{parser.tok});
            std.debug.print("peek {}\n", .{parser.peek});
        }
        while (try parser.next()) |_| {
            // something
        }
    }

    const pieces = [_][]const u8{
        "%num.dbg.spill = alloca [type [4 x i8]], align, 4",
        "store [type i32], %num, [type ptr], %num.dbg.spill, align, 4",
        "%0 = call [type { i32, i1 }], @llvm.smul.with.overflow.i32, (i32 %num, i32 %num)",
        "br [type i1], %_2.1, label %panic, label %bb1",
        "panic:",
        "call [type void], @core::panicking::panic_const::panic_const_mul_overflow, (ptr @alloc_669)",
        "unreachable",
        //
        "define { i32, i1 } @llvm.smul.with.overflow.i32",
    };

    var alloc_writer: std.Io.Writer.Allocating = .init(allocator);
    defer alloc_writer.deinit();
    const writer = &alloc_writer.writer;

    const square = parser.module_objects.get("square") orelse unreachable;
    try square.function.formatWriter(writer, &parser);

    const llvm0 = parser.module_objects.get("llvm.smul.with.overflow.i32") orelse unreachable;
    try llvm0.function.formatWriter(writer, &parser);

    const core0 = parser.module_objects.get("core::panicking::panic_const::panic_const_mul_overflow") orelse unreachable;
    try core0.function.formatWriter(writer, &parser);

    try testPieces(&pieces, alloc_writer.written());
}

test "decls" {
    const allocator = std.testing.allocator;
    const expectFmt = std.testing.expectFmt;


    const buffer =
        \\%struct.sqlite3StatType = type { [10 x i64], [10 x i64] }
        \\%struct.et_info = type { i8, i8, i8, i8, i8, i8 }
        \\%struct.sqlite3PrngType = type { [16 x i32], [64 x i8], i8 }
        \\%struct.VdbeOpList = type { i8, i8, i8, i8 }
        \\%struct.compareInfo = type { i8, i8, i8, i8 }
        \\%struct.FuncDefHash = type { [23 x ptr] }
        \\%struct.sqlite3_mem_methods = type { ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
        \\%struct.sqlite3_mutex_methods = type { ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr, ptr }
        \\%struct.sqlite3_mutex = type { %union.pthread_mutex_t }
        \\
        \\@.str.1246 = private unnamed_addr constant [17 x i8] c"json_group_array\00", align 1
        \\@azTempDirs = internal global [6 x ptr] [ptr null, ptr null, ptr @.str.89, ptr @.str.90, ptr @.str.91, ptr @.str.9], align 16
        \\
        \\@sqlite3RegisterJsonFunctions.aJsonFunc = internal global [34 x { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 }] [{ i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 1, [2 x i8] zeroinitializer, i32 25200641, ptr null, ptr null, ptr @jsonRemoveFunc, ptr null, ptr null, ptr null, ptr @.str.1220, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 1, [2 x i8] zeroinitializer, i32 8423425, ptr inttoptr (i64 8 to ptr), ptr null, ptr @jsonRemoveFunc, ptr null, ptr null, ptr null, ptr @.str.1221, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 26216449, ptr null, ptr null, ptr @jsonArrayFunc, ptr null, ptr null, ptr null, ptr @.str.1222, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 26216449, ptr inttoptr (i64 8 to ptr), ptr null, ptr @jsonArrayFunc, ptr null, ptr null, ptr null, ptr @.str.1223, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 1, [2 x i8] zeroinitializer, i32 8423425, ptr null, ptr null, ptr @jsonArrayLengthFunc, ptr null, ptr null, ptr null, ptr @.str.1224, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 2, [2 x i8] zeroinitializer, i32 8423425, ptr null, ptr null, ptr @jsonArrayLengthFunc, ptr null, ptr null, ptr null, ptr @.str.1224, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 1, [2 x i8] zeroinitializer, i32 8423425, ptr null, ptr null, ptr @jsonErrorFunc, ptr null, ptr null, ptr null, ptr @.str.1225, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 25200641, ptr null, ptr null, ptr @jsonExtractFunc, ptr null, ptr null, ptr null, ptr @.str.1226, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 8423425, ptr inttoptr (i64 8 to ptr), ptr null, ptr @jsonExtractFunc, ptr null, ptr null, ptr null, ptr @.str.1227, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 2, [2 x i8] zeroinitializer, i32 25200641, ptr inttoptr (i64 1 to ptr), ptr null, ptr @jsonExtractFunc, ptr null, ptr null, ptr null, ptr @.str.1228, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 2, [2 x i8] zeroinitializer, i32 8423425, ptr inttoptr (i64 2 to ptr), ptr null, ptr @jsonExtractFunc, ptr null, ptr null, ptr null, ptr @.str.1229, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 26249217, ptr null, ptr null, ptr @jsonSetFunc, ptr null, ptr null, ptr null, ptr @.str.1230, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 9472001, ptr inttoptr (i64 8 to ptr), ptr null, ptr @jsonSetFunc, ptr null, ptr null, ptr null, ptr @.str.1231, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 26216449, ptr null, ptr null, ptr @jsonObjectFunc, ptr null, ptr null, ptr null, ptr @.str.1232, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 26216449, ptr inttoptr (i64 8 to ptr), ptr null, ptr @jsonObjectFunc, ptr null, ptr null, ptr null, ptr @.str.1233, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 2, [2 x i8] zeroinitializer, i32 25200641, ptr null, ptr null, ptr @jsonPatchFunc, ptr null, ptr null, ptr null, ptr @.str.1234, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 2, [2 x i8] zeroinitializer, i32 8423425, ptr inttoptr (i64 8 to ptr), ptr null, ptr @jsonPatchFunc, ptr null, ptr null, ptr null, ptr @.str.1235, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 1, [2 x i8] zeroinitializer, i32 8423425, ptr null, ptr null, ptr @jsonPrettyFunc, ptr null, ptr null, ptr null, ptr @.str.1236, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 2, [2 x i8] zeroinitializer, i32 8423425, ptr null, ptr null, ptr @jsonPrettyFunc, ptr null, ptr null, ptr null, ptr @.str.1236, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 1, [2 x i8] zeroinitializer, i32 26216449, ptr null, ptr null, ptr @jsonQuoteFunc, ptr null, ptr null, ptr null, ptr @.str.1237, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 25200641, ptr null, ptr null, ptr @jsonRemoveFunc, ptr null, ptr null, ptr null, ptr @.str.1238, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 8423425, ptr inttoptr (i64 8 to ptr), ptr null, ptr @jsonRemoveFunc, ptr null, ptr null, ptr null, ptr @.str.1239, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 26249217, ptr null, ptr null, ptr @jsonReplaceFunc, ptr null, ptr null, ptr null, ptr @.str.1240, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 9472001, ptr inttoptr (i64 8 to ptr), ptr null, ptr @jsonReplaceFunc, ptr null, ptr null, ptr null, ptr @.str.1241, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 26249217, ptr inttoptr (i64 4 to ptr), ptr null, ptr @jsonSetFunc, ptr null, ptr null, ptr null, ptr @.str.1242, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 -1, [2 x i8] zeroinitializer, i32 9472001, ptr inttoptr (i64 12 to ptr), ptr null, ptr @jsonSetFunc, ptr null, ptr null, ptr null, ptr @.str.1243, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 1, [2 x i8] zeroinitializer, i32 8423425, ptr null, ptr null, ptr @jsonTypeFunc, ptr null, ptr null, ptr null, ptr @.str.1244, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 2, [2 x i8] zeroinitializer, i32 8423425, ptr null, ptr null, ptr @jsonTypeFunc, ptr null, ptr null, ptr null, ptr @.str.1244, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 1, [2 x i8] zeroinitializer, i32 8423425, ptr null, ptr null, ptr @jsonValidFunc, ptr null, ptr null, ptr null, ptr @.str.1245, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 2, [2 x i8] zeroinitializer, i32 8423425, ptr null, ptr null, ptr @jsonValidFunc, ptr null, ptr null, ptr null, ptr @.str.1245, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 1, [2 x i8] zeroinitializer, i32 26216449, ptr null, ptr null, ptr @jsonArrayStep, ptr @jsonArrayFinal, ptr @jsonArrayValue, ptr @jsonGroupInverse, ptr @.str.1246, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 1, [2 x i8] zeroinitializer, i32 26216449, ptr inttoptr (i64 8 to ptr), ptr null, ptr @jsonArrayStep, ptr @jsonArrayFinal, ptr @jsonArrayValue, ptr @jsonGroupInverse, ptr @.str.1247, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 2, [2 x i8] zeroinitializer, i32 26216449, ptr null, ptr null, ptr @jsonObjectStep, ptr @jsonObjectFinal, ptr @jsonObjectValue, ptr @jsonGroupInverse, ptr @.str.1248, %union.anon.10 zeroinitializer }, { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 } { i16 2, [2 x i8] zeroinitializer, i32 26216449, ptr inttoptr (i64 8 to ptr), ptr null, ptr @jsonObjectStep, ptr @jsonObjectFinal, ptr @jsonObjectValue, ptr @jsonGroupInverse, ptr @.str.1249, %union.anon.10 zeroinitializer }], align 16
    ;

    var parser = Parser.init(buffer, allocator);
    defer parser.deinit();

    {
        errdefer {
            std.debug.print("curr {}\n", .{parser.tok});
            std.debug.print("peek {}\n", .{parser.peek});
        }
        while (try parser.next()) |_| {
            // something
        }
    }

    const funcDefHash = parser.type_table.getNamedDirect("struct.FuncDefHash") orelse unreachable;
    const sqlite3PrngType = parser.type_table.getNamedDirect("struct.sqlite3PrngType") orelse unreachable;
    const sqlite3Mutex = parser.type_table.getNamedDirect("struct.sqlite3_mutex") orelse unreachable;

    const str1246 = parser.module_objects.get(".str.1246") orelse unreachable;
    const aJsonFunc = parser.module_objects.get("sqlite3RegisterJsonFunctions.aJsonFunc") orelse unreachable;
    const azTempDirs = parser.module_objects.get("azTempDirs") orelse unreachable;

    try expectFmt("[23 x ptr]", "{f}", .{parser.type_table.extra(funcDefHash).@"struct".xs[0].Fmt(&parser)});
    try expectFmt("{ [16 x i32], [64 x i8], i8 }", "{f}", .{sqlite3PrngType.Fmt(&parser)});
    try expectFmt("{ %union.pthread_mutex_t }", "{f}", .{sqlite3Mutex.Fmt(&parser)});

    try expectFmt(
        \\@.str.1246 = global [17 x i8] c"json_group_array\00", align 1
        \\
    , "{f}", .{str1246.global.Fmt(&parser)});

    try expectFmt(
        \\@sqlite3RegisterJsonFunctions.aJsonFunc = constant [34 x { i16, [2 x i8], i32, ptr, ptr, ptr, ptr, ptr, ptr, ptr, %union.anon.10 }] <INVALID>, align 16
        \\
    , "{f}", .{aJsonFunc.global.Fmt(&parser)});

    try expectFmt(
        \\@azTempDirs = constant [6 x ptr] [ptr null, ptr null, ptr @.str.89, ptr @.str.90, ptr @.str.91, ptr @.str.9], align 16
        \\
    , "{f}", .{azTempDirs.global.Fmt(&parser)});
}

// test "amalgamation" {
//     const allocator = std.testing.allocator;

//     const buffer = @embedFile("./test/sqlite3.ll");

//     var parser = Parser.init(buffer, allocator);
//     defer parser.deinit();

//     {
//         errdefer {
//             std.debug.print("curr {}\n", .{parser.tok});
//             std.debug.print("peek {}\n", .{parser.peek});
//         }
//         while (try parser.next()) |_| {
//             // something
//         }
//     }
// }
