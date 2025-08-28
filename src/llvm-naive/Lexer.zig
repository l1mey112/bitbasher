const std = @import("std");
const intern = @import("intern.zig");

const Allocator = std.mem.Allocator;
const ascii = std.ascii;
const StaticInternUnmanagedExtra = intern.StaticInternUnmanagedExtra;
const TokenMap = StaticInternUnmanagedExtra(Token.Kind, .{ .reserved_field_end = .declare });

const Lexer = @This();

b: [:0]const u8,
idx: usize,
token_map: TokenMap,
allocator: Allocator,

const Token = struct {
    kind: Kind,
    loc: Loc,

    const Kind = enum(usize) {
        err,
        eof,
        float,
        integer_type,
        label,

        global_var,
        global_id,

        local_var,
        local_var_id,

        equal,
        lsquare,
        rsquare,
        lbrace,
        rbrace,
        less,
        greater,
        lparen,
        rparen,
        comma,
        star,
        bar,
        colon,

        // begin non-reserved
        declare,
        define,
        _,
    };

    pub const Loc = struct {
        start: usize,
        end: usize,

        fn slice(self: *const Loc, buffer: [:0]const u8) []const u8 {
            return buffer[self.start..self.end];
        }
    };
};

pub fn init(buffer: [:0]const u8, allocator: Allocator) Lexer {
    // skip the UTF-8 BOM if present
    return .{
        .b = buffer,
        .allocator = allocator,
        .idx = if (std.mem.startsWith(u8, buffer, "\xEF\xBB\xBF")) 3 else 0,
        .token_map = .init,
    };
}

pub fn deinit(self: *Lexer) void {
    self.token_map.deinit(self.allocator);
}

fn adv(self: *Lexer) ?u8 {
    const char = self.b[self.idx];
    self.idx += 1;

    if (char == 0) {
        if (self.idx <= self.b.len) {
            // just whitespace
            return 0;
        }
        
        self.idx -= 1;
        return null;        
    }

    return char;
}

fn adv0(self: *Lexer) u8 {
    return self.adv() orelse 0;
}

pub fn next(self: *Lexer) !Token {
    while (true) {
        const err: Token = .{
            .kind = .err,
            .loc = .{ .start = self.idx, .end = self.idx + 1 }
        };
        
        if (self.adv()) |curr| switch (curr) {
            // [a-zA-Z_]
            '_', 'a'...'z', 'A'...'Z' => {
                return try self.lexIdentifier();
            },
            // Ignore whitespace
            0, ' ', '\t', '\n', '\r' => {
                continue;
            },
            // will not support floating point constants starting with `+`
            '+' => return err,
            '@' => return self.lexAt(),
            // will not support comdat or weird labels
            '$' => return err,
            '%' => return self.lexPercent(),
            //
            ';' => {
                self.skipLineComment();
                continue;
            },
            //
            '=' => return self.single(.equal),
            '[' => return self.single(.lsquare),
            ']' => return self.single(.rsquare),
            '{' => return self.single(.lbrace),
            '}' => return self.single(.rbrace),
            '<' => return self.single(.less),
            '>' => return self.single(.greater),
            '(' => return self.single(.lparen),
            ')' => return self.single(.rparen),
            ',' => return self.single(.comma),
            '*' => return self.single(.star),
            '|' => return self.single(.bar),
            ':' => return self.single(.colon),
            '/' => {
                if (self.adv0() != '*') {
                    return err;
                }
                if (self.skipCComment()) {
                    return err;
                }
                continue;
            },
            else => return err,
        };
        return .{ .kind = .eof, .loc = .{ .start = self.b.len, .end = self.b.len } };
    }
}

fn single(self: *Lexer, kind: Token.Kind) Token {
    return .{
        .kind = kind,
        .loc = .{ .start = self.idx - 1, .end = self.idx }
    };
}

fn skipCComment(self: *Lexer) bool {
    // "This skips C-style /**/ comments. Returns true if there
    // was an error."

    while (self.adv()) |ch| {
        if (ch == '*') {
            if (self.adv()) |nch| {
                if (nch == '/') {
                    return false;
                }
            } else {
                // unterminated comment
                return true;
            }
        }
    } else {
        // unterminated comment
        return true;
    }
}

fn skipLineComment(self: *Lexer) void {
    while (true) {
        const ch = self.b[self.idx];
        if (ch == '\n' or ch == '\r' or self.adv() == null) {
            return;
        }
    }
}

fn isLabelChar(ch : u8) bool {
    return switch (ch) {
        '-', '$', '.', '_' => true,
        else => ascii.isAlphanumeric(ch),
    };
}

fn lexIdentifier(self: *Lexer) !Token {
    // "Lex a label, integer type, keyword, or hexadecimal integer constant."
    //    Label           [-a-zA-Z$._0-9]+:
    //    IntegerType     i[0-9]+
    //    Keyword         sdiv, float, ...
    //    HexIntConstant  [us]0x[0-9A-Fa-f]+

    var loc: Token.Loc = .{
        .start = self.idx - 1,
        .end = undefined,
    };

    // "Check for [us]0x[0-9A-Fa-f]+ which are Hexadecimal constant generated by
    // the CFE to avoid forcing it to deal with 64-bit numbers."

    // we can safely ignore these hex constants, as it is assumed the textual format
    // comes from "llvm-dis"

    if (self.b[self.idx - 1] == 'i' and ascii.isDigit(self.b[self.idx])) {
        const after_i = self.idx;
        var int_start = after_i;
        while (ascii.isDigit(self.b[int_start])) {
            int_start += 1;
        }

        if (!isLabelChar(self.b[int_start])) {
            loc.end = int_start;
            self.idx = int_start;
            // we don't validate bitwidth...
            return .{ .kind = .integer_type, .loc = loc };
        }
    }

    while (isLabelChar(self.b[self.idx])) {
        self.idx += 1;
    }

    // "When false (default), an identifier ending in ':' is a label token."
    // "When true, the ':' is treated as a separate token."
    // bool IgnoreColonInIdentifiers = false;

    // we can just assume the default, we don't need to be too compliant

    if (self.b[self.idx] == ':') {
        loc.end = self.idx + 1;
        return .{ .kind = .label, .loc = loc };
    }

    loc.end = self.idx;

    // catch all Keywords
    const ident = try self.token_map.intern(self.allocator, loc.slice(self.b));
    return .{ .kind = ident, .loc = loc };
}

fn lexAt(self: *Lexer) Token {
    // "Lex all tokens that start with an @ character."
    //   GlobalVar   @\"[^\"]*\"
    //   GlobalVar   @[-a-zA-Z$._][-a-zA-Z$._0-9]*
    //   GlobalVarID @[0-9]+
    return self.lexVar(.global_var, .global_id);
}

fn lexPercent(self: *Lexer) Token {
    // "Lex all tokens that start with a % character."
    //   LocalVar   ::= %\"[^\"]*\"
    //   LocalVar   ::= %[-a-zA-Z$._][-a-zA-Z$._0-9]*
    //   LocalVarID ::= %[0-9]+
    return self.lexVar(.local_var, .local_var_id);
}

fn lexVar(self: *Lexer, varKind: Token.Kind, varId: Token.Kind) Token {
    var loc: Token.Loc = .{
        .start = self.idx - 1,
        .end = undefined,
    };

    // wont't support @"..." and %"..."
    if (self.b[self.idx] == '"') {
        self.idx += 1;

        while (self.adv()) |ch| {
            if (ch == '"') {
                loc.end = self.idx;
                return .{ .kind = .err, .loc = loc };
            }
        } else {
            loc.end = self.idx;
            return .{ .kind = .err, .loc = loc };
        }
        unreachable;
    }

    // "Handle VarName: [-a-zA-Z$._][-a-zA-Z$._0-9]*"
    if (self.readVarName(varKind)) |tok| {
        return tok;
    }
    
    // "Handle VarID: [0-9]+"
    return self.lexUIntID(varId);
}

fn lexUIntID(self: *Lexer, varId: Token.Kind) Token {
    // "Lex an ID: [0-9]+. On success, the ID is stored in UIntVal and Token is
    // returned, otherwise the Error token is returned.""
    
    var loc: Token.Loc = .{
        // start after the %, the start..end contains the actual variable name
        .start = self.idx,
        .end = undefined,
    };
    
    if (!ascii.isDigit(self.b[self.idx])) {
        loc.start = self.idx - 1;
        loc.end = self.idx;
        return .{ .kind = .err, .loc = loc };
    }

    self.idx += 1;
    while (ascii.isDigit(self.b[self.idx])) {
        self.idx += 1;
    }

    loc.end = self.idx;
    return .{ .kind = varId, .loc = loc };
}

fn readVarName(self: *Lexer, varKind: Token.Kind) ?Token {
    // "Handle VarName: [-a-zA-Z$._][-a-zA-Z$._0-9]*"
    // "ReadVarName - Read the rest of a token containing a variable name."
    
    var loc: Token.Loc = .{
        // start after the %, @, the start..end contains the actual variable name
        .start = self.idx,
        .end = undefined,
    };

    const isCond = struct {
        fn isCond(ch: u8) bool {
            return switch (ch) {
                '-', '$', '.', '_' => true,
                else => false,
            };
        }
    }.isCond;

    if (isCond(self.b[self.idx]) or ascii.isAlphabetic(self.b[self.idx])) {
        self.idx += 1;
        while (isCond(self.b[self.idx]) or ascii.isAlphanumeric(self.b[self.idx])) {
            self.idx += 1;
        }
        loc.end = self.idx;
        return .{ .loc = loc, .kind = varKind };
    }
    return null;
}

// fn lexPositive(self: *Lexer) Token {
//     var loc: Token.Loc = .{
//         .start = self.idx - 1,
//         .end = undefined,
//     };
//
//     // "If the letter after the negative is a number, this is probably not a label."
//     if (!ascii.isDigit(self.b[self.idx])) {
//         loc.end = self.idx + 1;
//         return .{ .kind = .err, .loc = loc };
//     }
//
//     // "Skip digits"
//     self.idx += 1;
//     while (ascii.isDigit(self.b[self.idx])) {
//         self.idx += 1;
//     }
//
//     // "At this point, we need a '.'."
//     if (self.b[self.idx] != '.') {
//         loc.end = self.idx + 1;
//         return .{ .kind = .err, .loc = loc };
//     }
//     self.idx += 1;
//
//     // "Skip over [0-9]*([eE][-+]?[0-9]+)?"
//     while (ascii.isDigit(self.b[self.idx])) {
//         self.idx += 1;
//     }
//
//     if (self.b[self.idx] == 'e' or self.b[self.idx] == 'E') {
//         if (ascii.isDigit(self.b[self.idx + 1]) or
//             (
//                 (self.b[self.idx + 1] == '-' or self.b[self.idx + 1] == '+') and
//                 ascii.isDigit(self.b[self.idx + 1])
//             )
//         ) {
//             self.idx += 2;
//             while (ascii.isDigit(self.b[self.idx])) {
//                 self.idx += 1;
//             }
//         }
//     }
//
//     loc.end = self.idx;
//     return .{
//         .kind = .float,
//         .loc = loc,
//     };
// }

const TestPiece = union(enum) {
    id: struct { Token.Kind, ?[:0]const u8 },
    lit: [:0]const u8,
};

fn testPieces(buffer: [:0]const u8, pieces: []const TestPiece) !void {
    const allocator = std.testing.allocator;
    const expectEqual = std.testing.expectEqual;
    const expectEqualStrings = std.testing.expectEqualStrings;

    var lexer = Lexer.init(buffer, allocator);
    defer lexer.deinit();

    var i: usize = 0;
    while (true) {
        const tok = try lexer.next();

        errdefer std.debug.print(
            "failed inside run {}..{} ({s})\n",
            .{ tok.loc.start, tok.loc.end, tok.loc.slice(buffer) }
        );

        switch (pieces[i]) {
            .id => |t| {
                try expectEqual(t.@"0", tok.kind);
                if (t.@"1") |lit| {
                    try expectEqualStrings(lit, tok.loc.slice(buffer));
                }
            },
            .lit => |lit| {
                const kind = try lexer.token_map.intern(allocator, lit);
                try expectEqual(kind, tok.kind);
            },
        }

        if (tok.kind == .eof) {
            break;
        }

        i += 1;
    }
}

test "simple" {
    const pieces = [_]TestPiece{
        .{ .id = .{ .define, null } }, .{ .id = .{ .integer_type, "i32" } }, .{ .id = .{ .global_var, "test1" } },
            .{ .id = .{ .lparen, null } }, .{ .id = .{ .integer_type, "i32" } }, .{ .id = .{ .local_var, "X" } }, .{ .id = .{ .rparen, null } },
        //
        .{ .id = .{ .local_var_id, "1" } }, .{ .id = .{ .equal, null } }, .{ .lit = "alloca" }, .{ .id = .{ .integer_type, "i32" } },
        //
        .{ .lit = "br" }, .{ .lit = "label" }, .{ .id = .{ .local_var_id, "2" } },
        //
        .{ .id = .{ .eof, null } },
    };

    const buffer =
        \\define i32 @test1(i32 %X)
        \\; Implicit entry label. Not printed on output.
        \\  %1 = alloca i32
        \\  br label %2
    ;
    try testPieces(buffer, &pieces);
}

test "nul" {
    const pieces = [_]TestPiece{
        .{ .id = .{ .define, null } }, .{ .id = .{ .integer_type, "i32" } }, .{ .id = .{ .global_var, "test1" } },
            .{ .id = .{ .lparen, null } }, .{ .id = .{ .integer_type, "i32" } }, .{ .id = .{ .local_var, "X" } }, .{ .id = .{ .rparen, null } },
        .{ .id = .{ .eof, null } },
    };

    const buffer =
        "define\x00i32\x00 @test1\x00(\x00i32 %X\x00)\x00"
    ;
    try testPieces(buffer, &pieces);
}
