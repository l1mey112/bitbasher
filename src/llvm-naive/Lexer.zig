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

pub const Token = struct {
    kind: Kind,
    loc: Loc,

    pub const Kind = enum(usize) {
        const begin_forget = @intFromEnum(Kind.private);
        const end_forget = @intFromEnum(Kind.local_unnamed_addr);

        err,
        eof,
        integer_type,

        label_literal,
        integer_literal,
        float_literal,
        hex_float_literal,

        global_var,
        global_id,
        local_var,
        local_var_id,
        metadata_var, // needs to be unescaped (just \\)
        summary_id,
        attr_grp_id,

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
        dotdotdot,
        exclaim,
        hash,

        string_constant, // needs to be unescaped

        // begin non-reserved
        declare,
        define,
        target,
        source_filename,

        // vectors
        vscale,
        x,

        // prefix
        prefix,
        prologue,

        gc,
        personality,

        // types
        @"void",
        half,
        bfloat,
        float,
        double,
        x86_fp80,
        fp128,
        ppc_fp128,
        x86_amx,
        ptr,
        //
        metadata,
        token,
        label,

        @"addrspace",

        // --- begin_forget ---

        // Linkage Types
        private,
        internal,
        availiable_externally,
        linkonce,
        weak,
        common,
        appending,
        extern_weak,
        linkonce_odr,
        weak_odr,
        external,

        // Visibility
        default,
        hidden,
        protected,

        // DLL Storage Class
        dllimport,
        dllexport,

        // Calling Convention
        ccc,
        fastcc,
        intel_ocl_bicc,
        coldcc,
        cfguard_checkcc,
        x86_stdcallcc,
        x86_fastcallcc,
        x86_thiscallcc,
        x86_vectorcallcc,
        arm_apcscc,
        arm_aapcscc,
        arm_aapcs_vfpcc,
        aarch64_vector_pcs,
        aarch64_sve_vector_pcs,
        aarch64_sme_preservemost_from_x0,
        aarch64_sme_preservemost_from_x1,
        aarch64_sme_preservemost_from_x2,
        msp430_intrcc,
        avr_intrcc,
        avr_signalcc,
        ptx_kernel,
        ptx_device,
        spir_func,
        spir_kernel,
        x86_64_sysvcc,
        win64cc,
        anyregcc,
        preserve_mostcc,
        preserve_allcc,
        preserve_nonecc,
        ghccc,
        swiftcc,
        swifttailcc,
        x86_intrcc,
        hhvmcc,
        hhvm_ccc,
        cxx_fast_tlscc,
        amdgpu_vs,
        amdgpu_ls,
        amdgpu_hs,
        amdgpu_es,
        amdgpu_gs,
        amdgpu_ps,
        amdgpu_cs,
        amdgpu_cs_chain,
        amdgpu_cs_chain_preserve,
        amdgpu_kernel,
        tailcc,
        m68k_rtdcc,
        graalcc,
        riscv_vector_cc,
        riscv_vls_cc,
        cc,
        
        // Random other attributes
        unnamed_addr,
        local_unnamed_addr,

        // --- end_forget ---

        // Parameter Attributes
        // https://llvm.org/docs/LangRef.html#parameter-attributes
        // -------------
        // only a selection of attributes are written here, just the ones
        // we need to know when to skip.
        // test(<ty>)
        byval,
        byref,
        preallocated,
        inalloca,
        sret,
        elementtype,
        captures,
        dereferenceable,
        dereferenceable_or_null,
        nofpclass,
        alignstack,
        initializes,
        range,
        // align <n> or align(<n>)
        @"align",        
        
        _,

        pub fn lit(kind: Kind, map: *const TokenMap) []const u8 {
            return map.get(kind);
        }

        pub fn forgettable(kind: Kind) bool {
            return switch (@intFromEnum(kind)) {
                Kind.begin_forget...Kind.end_forget => true,
                else => false,
            };
        }

        // .@"align" needs to be special cased
        pub fn isAttributeParen(kind: Kind) bool {
            return switch (@intFromEnum(kind)) {
                @intFromEnum(Kind.byval)...@intFromEnum(Kind.range) => true,
                else => false,
            };
        }

        pub fn isAttributesAndBeyond(kind: Kind) bool {
            return @intFromEnum(kind) >= @intFromEnum(Kind.byval);
        }

        pub fn isType(kind: Kind) bool {
            return switch (kind) {
                .@"void"....ptr => true,
                else => false,
            };
        }
    };

    pub const Loc = struct {
        start: usize,
        end: usize,

        pub fn slice(self: Loc, buffer: [:0]const u8) []const u8 {
            return buffer[self.start..self.end];
        }

        pub fn sliceUnescape(self: Loc, allocator: Allocator, buffer: [:0]const u8) ![]const u8 {
            const str = self.slice(buffer);

            // "UnEscapeLexed - Run through the specified buffer and change \xx codes to the
            // appropriate character."

            var unescaped = try std.ArrayList(u8).initCapacity(allocator, str.len);
            errdefer unescaped.deinit(allocator);

            var i: usize = 0;
            while (i < str.len) {
                if (str[i] == '\\') {
                    if (i + 1 < str.len and str[i + 1] == '\\') {
                        unescaped.appendAssumeCapacity('\\');
                        i += 2;
                    } else if (
                        i + 2 < str.len and ascii.isHex(str[i + 1]) and
                        ascii.isHex(str[i + 2])
                    ) {
                        const hi = hexDigitToInt(str[i + 1]);
                        const lo = hexDigitToInt(str[i + 2]);
                        const byte_val = @as(u8, @intCast(hi * 16 + lo));

                        unescaped.appendAssumeCapacity(byte_val);
                        i += 3;
                    }
                    else {
                        unescaped.appendAssumeCapacity('\\');
                        i += 1;
                    }
                } else {
                    unescaped.appendAssumeCapacity(str[i]);
                    i += 1;
                }
            }
            return unescaped.toOwnedSlice(allocator);
        }

        // we can assume that integers will be in decimal form

        pub fn unsigned(self: Loc, buffer: [:0]const u8) !u64 {
            const str = self.slice(buffer);

            if (str[0] == '-') {
                return std.fmt.ParseIntError.InvalidCharacter;
            }
            return try std.fmt.parseInt(u64, str, 10);
        }

        pub fn signed(self: Loc, buffer: [:0]const u8) !i64 {
            const str = self.slice(buffer);
            return try std.fmt.parseInt(i64, str, 10);
        }
    };
};

pub fn init(buffer: [:0]const u8) Lexer {
    // skip the UTF-8 BOM if present
    return .{
        .b = buffer,
        .idx = if (std.mem.startsWith(u8, buffer, "\xEF\xBB\xBF")) 3 else 0,
        .token_map = .init,
    };
}

pub fn deinit(self: *Lexer, allocator: Allocator) void {
    self.token_map.deinit(allocator);
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

pub fn next(self: *Lexer, allocator: Allocator) !Token {
    while (true) {
        const err: Token = .{
            .kind = .err,
            .loc = .{ .start = self.idx, .end = self.idx + 1 }
        };
        
        if (self.adv()) |curr| switch (curr) {
            // [a-zA-Z_]
            '_', 'a'...'z', 'A'...'Z' => {
                return try self.lexIdentifier(allocator);
            },
            // ignore whitespace
            0, ' ', '\t', '\n', '\r' => {
                continue;
            },
            // will not support floating point constants starting with `+`
            '+' => return err,
            '@' => return self.lexAt(),
            // will not support comdat or weird labels
            '$' => return err,
            '%' => return self.lexPercent(),
            '"' => return self.lexQuote(),
            '.' => return self.lexDot(),
            ';' => {
                self.skipLineComment();
                continue;
            },
            '!' => return self.lexExclaim(),
            '^' => return self.lexCaret(),
            '#' => return self.lexHash(),
            '0'...'9', '-' => return self.lexDigitOrNegative(),
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

fn lexIdentifier(self: *Lexer, allocator: Allocator) !Token {
    // "Lex a label, integer type, keyword, or hexadecimal integer constant."
    //    Label           [-a-zA-Z$._0-9]+:
    //    IntegerType     i[0-9]+
    //    Keyword         sdiv, float, ...
    //    HexIntConstant  [us]0x[0-9A-Fa-f]+

    const start = self.idx - 1;
    var loc: Token.Loc = .{
        .start = start,
        .end = undefined,
    };

    // "Check for [us]0x[0-9A-Fa-f]+ which are Hexadecimal constant generated by
    // the CFE to avoid forcing it to deal with 64-bit numbers."

    // we can safely ignore these hex constants, as it is assumed the textual format
    // comes from "llvm-dis"

    if (self.b[start] == 'i' and ascii.isDigit(self.b[self.idx])) {
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

    // we can just assume the default, we don't need the other one

    if (self.b[self.idx] == ':') {
        loc.end = self.idx + 1;
        return .{ .kind = .label_literal, .loc = loc };
    }
    
    // "Check for [us]0x[0-9A-Fa-f]+ which are Hexadecimal constant generated by
    // the CFE to avoid forcing it to deal with 64-bit numbers."

    // will not support [us] hex constants
    if (
        (self.b[start] == 'u' or self.b[start] == 's') and
        self.b[start + 1] == '0' and self.b[start + 2] == 'x' and
        ascii.isHex(self.b[start + 3])
    ) {
        self.idx = start + 3;
        while (ascii.isHex(self.b[self.idx])) {
            self.idx += 1;
        }
        loc.end = self.idx;
        return .{ .kind = .err, .loc = loc };
    }

    loc.end = self.idx;

    // catch all Keywords
    const ident = try self.token_map.intern(allocator, loc.slice(self.b));
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

    // will not support @"..." and %"..."
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
        // start after the %, ^, the start..end contains the actual variable name
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

fn isVarSpecial(ch: u8) bool {
    return switch (ch) {
        '-', '$', '.', '_' => true,
        else => false,
    };
}

fn readVarName(self: *Lexer, varKind: Token.Kind) ?Token {
    // "Handle VarName: [-a-zA-Z$._][-a-zA-Z$._0-9]*"
    // "ReadVarName - Read the rest of a token containing a variable name."
    
    var loc: Token.Loc = .{
        // start after the %, @, the start..end contains the actual variable name
        .start = self.idx,
        .end = undefined,
    };

    if (isVarSpecial(self.b[self.idx]) or ascii.isAlphabetic(self.b[self.idx])) {
        self.idx += 1;
        while (isVarSpecial(self.b[self.idx]) or ascii.isAlphanumeric(self.b[self.idx])) {
            self.idx += 1;
        }
        loc.end = self.idx;
        return .{ .loc = loc, .kind = varKind };
    }
    return null;
}

fn lexQuote(self: *Lexer) Token {
    // "Lex all tokens that start with a " character."
    //   QuoteLabel        "[^"]+":
    //   StringConstant    "[^"]*"

    var loc: Token.Loc = .{
        // start after the ", the start..end contains the actual string
        .start = self.idx,
        .end = undefined,
    };

    while (self.adv()) |ch| {
        if (ch == '"') {
            // don't include the "
            loc.end = self.idx - 1;

            var kind: Token.Kind = .string_constant;
            if (self.b[self.idx] == ':') {
                self.idx += 1;
                // we don't check if a nul character is in this name
                kind = .label_literal;
            }
            return .{ .kind = kind, .loc = loc };
        }
    } else {
        loc.end = self.idx;
        return .{ .kind = .err, .loc = loc };
    }
}

fn isLabelTail(self: *Lexer, start_idx: usize) ?usize {
    // "Return true if this pointer points to a valid end of a label."
    
    var cursor = start_idx;
    while (isLabelChar(self.b[cursor])) {
        cursor += 1;
    }

    if (self.b[cursor] == ':') {
        return cursor + 1; // Return index after the colon.
    }

    return null;
}

fn lexDigitOrNegative(self: *Lexer) Token {
    // "Lex tokens for a label or a numeric constant, possibly starting with -."
    //    Label             [-a-zA-Z$._0-9]+:
    //    NInteger          -[0-9]+
    //    FPConstant        [-+]?[0-9]+[.][0-9]*([eE][-+]?[0-9]+)?
    //    PInteger          [0-9]+
    //    HexFPConstant     0x[0-9A-Fa-f]+
    //    HexFP80Constant   0xK[0-9A-Fa-f]+
    //    HexFP128Constant  0xL[0-9A-Fa-f]+
    //    HexPPC128Constant 0xM[0-9A-Fa-f]+

    const start = self.idx - 1;
    var loc: Token.Loc = .{
        .start = start,
        .end = undefined,
    };

    // "If the letter after the negative is not a number, this is probably a label."
    if (!ascii.isDigit(self.b[start]) and !ascii.isDigit(self.b[self.idx])) {
        // "Okay, this is not a number after the -, it's probably a label."
        if (isLabelTail(self, self.idx)) |end_idx| {
            self.idx = end_idx;
            loc.end = end_idx - 1; // do not include the :
            return .{ .kind = .label_literal, .loc = loc };
        }
        loc.end = self.idx;
        return .{ .kind = .err, .loc = loc };
    }

    // "At this point, it is either a label, int or fp constant."

    // "Skip digits, we have at least one."
    while (ascii.isDigit(self.b[self.idx])) {
        self.idx += 1;
    }

    // "Check if this is a fully-numeric label:"
    if (ascii.isDigit(self.b[start]) and self.b[self.idx] == ':') {
        // we don't parse and validate the numeric label
        loc.end = self.idx;
        self.idx += 1; // "Skip the colon."
        return .{ .kind = .label_literal, .loc = loc };
    }

    // "Check to see if this really is a string label, e.g. "-1:"."
    if (isLabelChar(self.b[self.idx]) or self.b[self.idx] == ':') {
        if (isLabelTail(self, self.idx)) |end_idx| {
            self.idx = end_idx;
            loc.end = end_idx - 1; // do not include the :
            return .{ .kind = .label_literal, .loc = loc };
        }
    }

    // "If the next character is a '.', then it is a fp value, otherwise its"
    // "integer."
    if (self.b[self.idx] != '.') {
        if (self.b[start] == '0' and self.b[start + 1] == 'x') {
            return self.lex0x(start);
        }
        loc.end = self.idx;
        return .{ .kind = .integer_literal, .loc = loc };
    }

    self.idx += 1;

    // "Skip over [0-9]*([eE][-+]?[0-9]+)?"
    while (ascii.isDigit(self.b[self.idx])) {
        self.idx += 1;
    }

    if (self.b[self.idx] == 'e' or self.b[self.idx] == 'E') {
        if (ascii.isDigit(self.b[self.idx + 1]) or
            (((self.b[self.idx + 1] == '-') or (self.b[self.idx + 1] == '+')) and
            ascii.isDigit(self.b[self.idx + 2])))
        {
            self.idx += 2;
            while (ascii.isDigit(self.b[self.idx])) {
                self.idx += 1;
            }
        }
    }

    loc.end = self.idx;
    return .{ .kind = .float_literal, .loc = loc };
}

fn lex0x(self: *Lexer, start: usize) Token {
    // "Lex all tokens that start with a 0x prefix, knowing they match and are not
    // labels."
    //    HexFPConstant     0x[0-9A-Fa-f]+
    //    HexFP80Constant   0xK[0-9A-Fa-f]+
    //    HexFP128Constant  0xL[0-9A-Fa-f]+
    //    HexPPC128Constant 0xM[0-9A-Fa-f]+
    //    HexHalfConstant   0xH[0-9A-Fa-f]+
    //    HexBFloatConstant 0xR[0-9A-Fa-f]+

    var loc: Token.Loc = .{
        .start = start,
        .end = undefined,
    };

    self.idx = start + 2;

    switch (self.b[self.idx]) {
        'K', 'L', 'M', 'H', 'R' => self.idx += 1,
        else => {},
    }

    if (!ascii.isHex(self.b[self.idx])) {
        // "Bad token, return it as an error."
        loc.end = self.idx;
        return .{ .kind = .err, .loc = loc };
    }

    while (ascii.isHex(self.b[self.idx])) {
        self.idx += 1;
    
    }
    loc.end = self.idx;
    return .{ .kind = .hex_float_literal, .loc = loc };
}

fn lexDot(self: *Lexer) Token {
    var loc: Token.Loc = .{
        .start = self.idx - 1,
        .end = undefined,
    };
    
    if (isLabelTail(self, self.idx)) |end_idx| {
        self.idx = end_idx;
        loc.end = end_idx - 1; // do not include the :
        return .{ .kind = .label_literal, .loc = loc };
    }
    if (self.b[self.idx] == '.' and self.b[self.idx + 1] == '.') {
        self.idx += 2;
        loc.end = self.idx;
        return .{ .kind = .dotdotdot, .loc = loc };
    }

    loc.end = self.idx;
    return .{ .kind = .err, .loc = loc };
}

fn lexExclaim(self: *Lexer) Token {
    var loc: Token.Loc = .{
        .start = self.idx - 1,
        .end = undefined,
    };

    if (isVarSpecial(self.b[self.idx]) or ascii.isAlphabetic(self.b[self.idx]) or
        self.b[self.idx] == '\\')
    {
        self.idx += 1;
        while (isVarSpecial(self.b[self.idx]) or ascii.isAlphanumeric(self.b[self.idx]) or self.b[self.idx] == '\\') {
            self.idx += 1;
        }

        // skip !
        loc.start = loc.start + 1;
        loc.end = self.idx;
        return .{ .kind = .metadata_var, .loc = loc };
    }
    loc.end = self.idx;
    return .{ .kind = .exclaim, .loc = loc };
}

fn lexCaret(self: *Lexer) Token {
    // "Lex all tokens that start with a ^ character."
    //    SummaryID ::= ^[0-9]+
    return self.lexUIntID(.summary_id);
}

fn lexHash(self: *Lexer) Token {
    // "Lex all tokens that start with a # character."
    //    AttrGrpID ::= #[0-9]+
    //    Hash ::= #

    if (ascii.isDigit(self.b[self.idx])) {
        return self.lexUIntID(.attr_grp_id);
    }
    const loc: Token.Loc = .{
        .start = self.idx - 1,
        .end = self.idx,
    };
    return .{ .kind = .hash, .loc = loc };
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

fn hexDigitToInt(c: u8) u8 {
    return switch (c) {
        '0'...'9' => c - '0',
        'a'...'f' => c - 'a' + 10,
        'A'...'F' => c - 'A' + 10,
        else => unreachable,
    };
}

const TestPiece = union(enum) {
    id: struct { Token.Kind, ?[:0]const u8 },
    lit: [:0]const u8,
};

fn testPieces(buffer: [:0]const u8, pieces: []const TestPiece) !void {
    const allocator = std.testing.allocator;
    const expectEqual = std.testing.expectEqual;
    const expectEqualStrings = std.testing.expectEqualStrings;

    var lexer = Lexer.init(buffer);
    defer lexer.deinit(allocator);

    var i: usize = 0;
    while (true) {
        const tok = try lexer.next(allocator);

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
        .{ .id = .{ .label_literal, "3" } }, .{ .id = .{ .label_literal, "2" } },
        .{ .id = .{ .label_literal, "-4" } }, .{ .id = .{ .label_literal, "-erm" } }, .{ .id = .{ .label_literal, ".label" } }, .{ .id = .{ .label_literal, "..erm..label" } },
            .{ .id = .{ .dotdotdot, null } },
        //
        .{ .id = .{ .integer_literal, "123" } }, .{ .id = .{ .integer_literal, "-163" } },
        .{ .id = .{ .float_literal, "1231." } },
        .{ .id = .{ .hex_float_literal, "0x7FF0000000000000" } }, .{ .id = .{ .comma, null } },
            .{ .id = .{ .float_literal, "1.000000e+01" } },
        .{ .id = .{ .hex_float_literal, "0x8000000000000000" } },
        //
        .{ .lit = "ret" }, .{ .lit = "bfloat" }, .{ .id = .{ .hex_float_literal, "0xRFF80" } },
        //
        .{ .id = .{ .exclaim, null } }, .{ .id = .{ .metadata_var, "." } }, .{ .id = .{ .comma, null } },
        .{ .id = .{ .metadata_var, "BBBa\\\\ng" } }, .{ .id = .{ .metadata_var, "bang" } },
        //
        .{ .id = .{ .summary_id, "23" } },
        .{ .id = .{ .attr_grp_id, "231" } }, .{ .id = .{ .hash, null } },
        //
        .{ .id = .{ .err, "u0x23132" } }, .{ .id = .{ .err, "s0x0001" } },
        //
        .{ .id = .{ .eof, null } },
    };

    const buffer =
        \\define i32 @test1(i32 %X)
        \\; Implicit entry label. Not printed on output.
        \\  %1 = alloca i32
        \\  br label %2
        \\
        \\3: ; Explicit numeric label
        \\"2": ; string label, quoted number
        \\
        \\-4:   ; evil label
        \\-erm: ; evil label
        \\.label:
        \\..erm..label: ...
        \\
        \\123 -163
        \\1231.
        \\0x7FF0000000000000, 1.000000e+01
        \\0x8000000000000000
        \\
        \\ret bfloat 0xRFF80
        \\
        \\! !.,
        \\!BBBa\\ng !bang
        \\
        \\^23
        \\#231 #
        \\
        \\u0x23132
        \\s0x0001
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

test "amalgamation" {
    const allocator = std.testing.allocator;
    const expect = std.testing.expect;

    // this is a sort of "catch all" regression test.
    // the actual lexed tokens have been inspected to make sure they're correct

    const buffer = @embedFile("./test/sqlite3.ll");

    var lexer = Lexer.init(buffer);
    defer lexer.deinit(allocator);

    while (true) {
        const tok = try lexer.next(allocator);
        if (tok.kind == .eof) {
            break;
        }

        errdefer std.debug.print(
            "failed inside run {}..{} ({s})\n",
            .{ tok.loc.start, tok.loc.end, tok.loc.slice(buffer) }
        );

        try expect(tok.kind != .err);
    }
}

test "unescape" {
    const allocator = std.testing.allocator;
    const expectEqualStrings = std.testing.expectEqualStrings;

    const buffer =
        \\"\5Cbegin{\00\\"
    ;

    const loc: Token.Loc = .{
        .start = 1,
        .end = buffer.len - 1,
    };

    const str = try loc.sliceUnescape(allocator, buffer);
    defer allocator.free(str);

    try expectEqualStrings("\x5Cbegin{\x00\\", str);
}
