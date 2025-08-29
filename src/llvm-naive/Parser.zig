const std = @import("std");
const Lexer = @import("Lexer.zig");
const llvm_types = @import("llvm_types.zig");

const TypeTable = llvm_types.TypeTable;
const TypeId = llvm_types.TypeId;
const Token = Lexer.Token;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;

const Parser = @This();

allocator: Allocator,
lexer: Lexer,
tok: Token,

// not owned
type_table: *TypeTable,

pub fn init(buffer: [:0]const u8, allocator: Allocator, type_table: *TypeTable) Parser {
	return .{
		.lexer = Lexer.init(buffer),
		.allocator = allocator,
		.tok = undefined,
	};
}

pub fn deinit(self: *Parser) void {
	self.lexer.deinit(self.allocator);
}

const ParserError = error{
	// unrecoverable errors
	LexerError,
	NoSummaryEntry,
	NoMetadataInDeclare,
};

fn nextTok(self: *Parser) !void {
	self.tok = try self.lexer.next(self.allocator);

	if (self.tok.kind == .err) {
		return ParserError.LexerError;
	}
}

fn ignoreUntil(self: *Parser, kind: Token.Kind) !void {
	while (true) {
		try self.nextTok();

		if (self.tok.kind == kind or self.tok.kind == .eof) {
			break;
		}
	}
}

/// Try to incrementally parse, returns errors
pub fn next(self: *Parser) !?void {
	while (true) {
		try self.nextTok();

		if (self.tok.kind == .eof) {
			return null;
		}

		switch (self.tok.kind) {
			// will not support or attempt to skip ThinLTO summary entries
			.summary_id => return ParserError.NoSummaryEntry,

			// ignore: target ... = 'string'
			.target => try self.ignoreUntil(.string_constant),
			// ignore: source_filename ... = 'string'
			.source_filename => try self.ignoreUntil(.string_constant),

			.declare => try self
		}
	}
}

fn parseDeclare(self: *Parser) !?void {
	self.nextTok();

	// STUB: will not support or attempt to skip metadata attachements on declare
	if (self.tok.kind == .metadata_var) {
		return ParserError.NoMetadataInDeclare;
	}

	return self.parseFunctionHeader();
}

fn parseFunctionHeader(self: *Parser) !?void {
	// ... [linkage] [visibility] [DLLStorageClass]
    //    [cconv] [ret attrs]
    //    <ResultType> @<FunctionName> ([argument list])
    //    [(unnamed_addr|local_unnamed_addr)] [align N] [gc]
    //    [prefix Constant] [prologue Constant]

	// skip all the optional things
	while (self.tok.kind.forgettable()) {
		self.nextTok();
		// ::= 'cc' UINT
		if (self.tok.kind == .integer_literal) {
			self.nextTok();
		}
	}
	

}

fn parseType(self: *Parser) !TypeId {
	const curr = self.tok.kind;
	switch (curr) {
		.ptr => {
			// := 'addrspace' '(' uint32 ')'
			try self.nextTok();
			if (self.tok.kind == .@"addrspace") {
				self.ignoreUntil(.rparen);
				self.nextTok(); // after ')'
			}
			return .ptr;
		},
		.target => {
			// target("label")
			// target("label", void)
			self.ignoreUntil(.rparen);
			self.nextTok(); // after ')'
			return .invalid_type;
		},
		.lbrace => return try self.parseStructType(),
	}

	try self.nextTok();
	return switch (curr) {
		// cannot and will not support
		.metadata, .token, .label => .invalid_type,
		.@"void" => .@"void",
		.half => .half,
		.bfloat => .bfloat,
		.float => .float,
		.double => .double,
		.x86_fp80 => .x86_fp80,
		.fp128 => .fp128,
		.ppc_fp128 => .ppc_fp128,
		.x86_amx => .x86_amx,
		
		// https://llvm.org/docs/LangRef.html#structure-type
		// Type ::= StructType
		
	};
}

fn parseStructType(self: *Parser) !TypeId {
	// "parseStructType: Handles packed and unpacked types.  </> parsed elsewhere."
	//   StructType
	//     ::= '{' '}'
	//     ::= '{' Type (',' Type)* '}'
	//     ::= '<' '{' '}' '>'
	//     ::= '<' '{' Type (',' Type)* '}' '>'

	const xs: ArrayList(TypeId) = .initCapacity(self.allocator, 4);

	
}
