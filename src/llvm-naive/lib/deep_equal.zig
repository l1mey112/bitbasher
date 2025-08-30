const std = @import("std");

pub fn deepEql(a: anytype, b: @TypeOf(a), comptime strat: std.hash.Strategy) bool {
    const T = @TypeOf(a);

    switch (@typeInfo(T)) {
        .@"struct" => |info| {
            inline for (info.fields) |field_info| {
                if (!deepEql(@field(a, field_info.name), @field(b, field_info.name), strat)) return false;
            }
            return true;
        },
        .error_union => {
            if (a) |a_p| {
                if (b) |b_p| return deepEql(a_p, b_p, strat) else |_| return false;
            } else |a_e| {
                if (b) |_| return false else |b_e| return a_e == b_e;
            }
        },
        .@"union" => |info| {
            if (info.tag_type) |UnionTag| {
                const tag_a = std.meta.activeTag(a);
                const tag_b = std.meta.activeTag(b);
                if (tag_a != tag_b) return false;

                inline for (info.fields) |field_info| {
                    if (@field(UnionTag, field_info.name) == tag_a) {
                        return deepEql(@field(a, field_info.name), @field(b, field_info.name), strat);
                    }
                }
                return false;
            }
            @compileError("cannot compare untagged union type " ++ @typeName(T));
        },
        .array => {
            if (a.len != b.len) return false;
            for (a, 0..) |e, i|
                if (!deepEql(e, b[i], strat)) return false;
            return true;
        },
        .vector => |info| {
            var i: usize = 0;
            while (i < info.len) : (i += 1) {
                if (!deepEql(a[i], b[i], strat)) return false;
            }
            return true;
        },
        .pointer => |info| {
            switch (info.size) {
                .one => {
                    if (a == b) return true;
                    return switch (strat) {
                        .Shallow => false,
                        .Deep => deepEql(a.*, b.*, .Shallow),
                        .DeepRecursive => deepEql(a.*, b.*, .DeepRecursive),
                    };
                },
                .many, .c => {
                    if (a == b) return true;
                    if (strat != .Shallow) {
                        @compileError("cannot compare pointer-to-many or C-pointer for deep equality");
                    }
                },
                .slice => {
                    if (a.len != b.len) return false;
                    if (a.ptr == b.ptr) return true;
                    switch (strat) {
                        .Shallow => return false,
                        .Deep => {
                            for (a, b) |ae, be| {
                                if (!deepEql(ae, be, .Shallow)) return false;
                            }
                            return true;
                        },
                        .DeepRecursive => {
                            for (a, b) |ae, be| {
                                if (!deepEql(ae, be, .DeepRecursive)) return false;
                            }
                            return true;
                        },
                    }
                },
            }
        },
        .optional => {
            if (a == null and b == null) return true;
            if (a == null or b == null) return false;
            return deepEql(a.?, b.?, strat);
        },
        else => return a == b,
    }
}
