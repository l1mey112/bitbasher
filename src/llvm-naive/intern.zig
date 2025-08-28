//! I can only dream of such a datastructure in C.

const std = @import("std");
const Allocator = std.mem.Allocator;

pub fn Options(
    comptime InternIdx: type,
) type {
    return struct {
        /// When to start including the enum fields as matchable.
        reserved_field_end: ?InternIdx,
    };
}

pub fn StaticInternUnmanagedExtra(
    comptime InternIdx: type,
    comptime options: Options(InternIdx),
) type {

    const fields = @typeInfo(InternIdx).@"enum".fields;
    comptime var pieces: [fields.len]struct { []const u8, InternIdx } = undefined;

    comptime {
        if (@typeInfo(InternIdx).@"enum".is_exhaustive) {
            @compileError("only supports enums that cover the entire integral type");
        }
    }

    const seed = blk: {

        var hit_reserved_field = true;
        var reserved_field = -1;
        
        if (options.reserved_field_end) |f| {
            hit_reserved_field = false;
            reserved_field = @intFromEnum(f);
        }
        var i = 0;
        
        for (fields) |f| {
            if (f.value == reserved_field) {
                hit_reserved_field = true;
            }
            
            if (hit_reserved_field) {
                pieces[i] = .{ f.name, @as(InternIdx, @enumFromInt(f.value)) };
                i += 1;
            }
        }

        break :blk std.StaticStringMap(InternIdx).initComptime(pieces[0..i]);
    };

    return struct {
        const This = @This();

        map: std.StringArrayHashMapUnmanaged(void),
        seedmap: std.StaticStringMap(InternIdx),

        pub const init: This = .{
            .map = .empty,
            .seedmap = seed,
        };

        /// The same `allocator` must be used over all calls
        pub fn intern(self: *This, allocator: Allocator, k: []const u8) !InternIdx {
            if (seed.get(k)) |inte| {
                return inte;
            }
            
            // Now return with offset `pieces.len`.

            if (self.map.getIndex(k)) |idx| {
                return @enumFromInt(idx + pieces.len);
            }
            const dupe = try allocator.dupe(u8, k);
            const idx = self.map.count();
            try self.map.put(allocator, dupe, undefined);
            return @enumFromInt(idx + pieces.len);
        }

        pub fn get(self: *This, inte: InternIdx) []const u8 {
            var idx = @intFromEnum(inte);
            if (idx < pieces.len) {
                return pieces[idx].@"0";
            }
            idx -= pieces.len;
            return self.map.entries.get(idx).key;
        }

        /// The same `allocator` must be used over all calls
        pub fn deinit(self: *This, allocator: Allocator) void {
            for (0..self.map.count()) |i| {
                const key = self.map.entries.get(i).key;
                allocator.free(key);
            }
            self.map.deinit(allocator);
        }
    };
}

pub fn StaticInternUnmanaged(
    comptime InternIdx: type,
) type {
    return StaticInternUnmanagedExtra(InternIdx, .{ .reserved_field_end = null });
}

test "basic" {
    const allocator = std.testing.allocator;
    const expect = std.testing.expect;
    
    const Identifier = enum(usize) {
        declare,
        _,
    };

    var intern: StaticInternUnmanaged(Identifier) = .init;
    defer intern.deinit(allocator);

    const v0 = try intern.intern(allocator, "declare");

    const v1 = try intern.intern(allocator, "fart");
    const v2 = try intern.intern(allocator, "among");
    const v3 = try intern.intern(allocator, "fart");

    try expect(v0 == Identifier.declare);
    try expect(v1 == @as(Identifier, @enumFromInt(@intFromEnum(v0) + 1)));

    try expect(v1 == v3);
    try expect(v1 != v2);

    try expect(std.mem.eql(u8, intern.get(v1), "fart"));
    try expect(std.mem.eql(u8, intern.get(v2), "among"));
}

test "reserved" {
    const allocator = std.testing.allocator;
    const expect = std.testing.expect;
    
    const Identifier = enum(usize) {
        eof,
        
        declare,
        _,
    };

    var intern: StaticInternUnmanagedExtra(Identifier, .{ .reserved_field_end = .declare }) = .init;
    defer intern.deinit(allocator);

    const v0 = try intern.intern(allocator, "declare");
    const v1 = try intern.intern(allocator, "fart");
    const vnil = try intern.intern(allocator, "eof");

    try expect(v0 == Identifier.declare);
    try expect(vnil != .eof);
    try expect(vnil == @as(Identifier, @enumFromInt(@intFromEnum(v1) + 1)));
}