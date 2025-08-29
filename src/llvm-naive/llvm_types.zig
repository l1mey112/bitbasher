const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

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
};

const TypeExtra = union(enum) {
	
};

pub const TypeTable = struct {
	map: std.AutoArrayHashMapUnmanaged(TypeExtra, void),

	const index_offset = @typeInfo(TypeId).@"enum".fields.len;

	pub const init: TypeTable = .{
		.map = .empty,
	};
	
	pub fn intern(self: *TypeTable, allocator: Allocator, entry: TypeExtra) TypeId {
		if (self.map.getIndex(entry)) |idx| {
			return @enumFromInt(idx + index_offset);
		}
		const idx = self.map.count();
		try self.map.put(allocator, entry);
		return @enumFromInt(idx + index_offset);
	}

	/// Will panic if `typeId` is not a composite type.
	pub fn extra(self: *TypeTable, type_id: TypeId) TypeExtra {
		const idx = @intFromEnum(type_id);
		assert(idx < index_offset);
		idx -= index_offset;
		return self.map.entries.get(idx);
	}
};
