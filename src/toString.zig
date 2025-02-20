const std = @import("std");
const math = std.math;
const big = math.big;
const Limb = big.Limb;
const Const = big.int.Const;
const Managed = big.int.Managed;
const Mutable = big.int.Mutable;

const chars = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";

fn size_in_base_upper_bound(bit_count: usize, base: u8) usize {
    return int(f(bit_count) * log(2, base)) + 1;
}

const Constants = struct { big_bases: [37]Limb, digits_per_limb: [37]u8 };

const constants: Constants = blk: {
    @setEvalBranchQuota(2000);
    var digits_per_limb = [_]u8{0} ** 37;
    var bases = [_]Limb{0} ** 37;
    for (3..37) |base| {
        digits_per_limb[base] = @intCast(math.log(Limb, base, math.maxInt(Limb)));
        bases[base] = std.math.pow(Limb, base, digits_per_limb[base]);
    }
    break :blk Constants{ .big_bases = bases, .digits_per_limb = digits_per_limb };
};

const div = @import("div.zig");


pub fn subquadratic(allocator: std.mem.Allocator, a: *Managed, b: u8) ![]u8 {
    var string = try allocator.alloc(u8, size_in_base_upper_bound(a.bitCountAbs(), 10));
    @memset(string, 0);

    const N = a.bitCountAbs() - 1;
    const k = int(@floor(f(N) * log(2, b) / 2)) + 1;

    try subquadratic_rec(allocator, k, string, a, b);
    var i: usize = 0;
    for (string) |x| {
        if (x != 0) break;
        i += 1;
    }
    std.mem.copyForwards(u8, string[0 .. string.len - i], string[i..]);
    string = try allocator.realloc(string, string.len - i);

    for (string) |*x|
        x.* = chars[x.*];

    return string;
}
pub fn subquadratic_iter(allocator: std.mem.Allocator, A: *Managed, b: u8) ![]u8 {
    var full_string = try allocator.alloc(u8, size_in_base_upper_bound(A.bitCountAbs(), 10));
    @memset(full_string, 0);

    var r = try Managed.init(allocator);
    var base = try Managed.init(allocator);
    defer r.deinit();
    defer base.deinit();

    const StackItem = struct { a: Managed, k: usize, string: []u8 };

    // TODO: proove that
    const max_depth = int(@ceil(log(size_in_base_upper_bound(A.bitCountAbs(), 10), 2) - log(constants.digits_per_limb[b], 2))) + 1;
    var stack = try allocator.alloc(StackItem, std.math.pow(usize, 2, max_depth));
    var new_stack = try allocator.alloc(StackItem, std.math.pow(usize, 2, max_depth));
    defer allocator.free(stack);
    defer allocator.free(new_stack);
    var stack_i: usize = 0;
    var new_stack_i: usize = 0;

    const N = A.bitCountAbs() - 1;
    stack[0] = StackItem{ .a = try A.clone(), .k = int(@floor(f(N) * log(2, b) / 2)) + 1, .string = full_string };
    stack_i += 1;

    // TODO: after each depth, the cache can be cleared, so bases can be reused
    var base_cache = std.AutoHashMap(usize, Managed).init(allocator);
    defer {
        var it = base_cache.valueIterator();
        while (it.next()) |cached| {
            cached.deinit();
        }
        base_cache.deinit();
    }

    var depth: usize = 0;
    while (stack_i > 0) {
        while (stack_i > 0) {
            stack_i -= 1;
            const item = stack[stack_i];
            var a = item.a;
            const k = item.k;
            const string = item.string;

            // 2k because the k passed to the function is the number of digits of the bottom half of a
            if (2 * k < constants.digits_per_limb[b]) {
                std.debug.assert(a.len() <= 1);

                // not string.len - 1 to avoid overflow
                var i = string.len;
                var value = a.limbs[0]; // k < digits_per_limb => a is contained in one limb

                while (value > 0) {
                    string[i - 1] = @truncate(value % b);
                    value /= b;
                    i -= 1;
                }
                a.deinit();
                continue;
            }

            const base_num = blk: {
                if (base_cache.contains(k))
                    break :blk base_cache.getPtr(k).?;
                try base.set(b);
                try base.pow(&base, @intCast(k));
                try base_cache.put(k, try base.clone());
                break :blk &base;
            };
            try a.divFloor(&r, &a, base_num);

            new_stack[new_stack_i] = StackItem{ .a = a, .k = k - k / 2, .string = string[0 .. string.len - k] };
            new_stack[new_stack_i + 1] = StackItem{ .a = try r.clone(), .k = k / 2, .string = string[string.len - k ..] };
            new_stack_i += 2;
        }
        @memcpy(stack[0..new_stack_i], new_stack[0..new_stack_i]);
        stack_i = new_stack_i;
        new_stack_i = 0;
        depth += 1;
    }
    std.debug.assert(depth <= max_depth);

    var i: usize = 0;
    for (full_string) |x| {
        if (x != 0) break;
        i += 1;
    }
    std.mem.copyForwards(u8, full_string[0 .. full_string.len - i], full_string[i..]);
    full_string = try allocator.realloc(full_string, full_string.len - i);

    for (full_string) |*x|
        x.* = chars[x.*];

    return full_string;
}

pub noinline fn basecase(allocator: std.mem.Allocator, string: []u8, a: *Managed, base: u8) !void {
    var string_len: usize = string.len;
    //var num = try allocator.dupe(Limb, a.limbs[0..div.llnormalize(a.limbs)]);
    var num = a.limbs[0..a.len()];
    var num_len = num.len;

    const big_base = constants.big_bases[base];
    const dig_per_limb = constants.digits_per_limb[base];
    var limb_buffer = try allocator.alloc(Limb, num.len);
    @memset(limb_buffer, 0);

	var b = try a.clone();
	var R = try Managed.init(allocator);
	var c = try (Const { .limbs = &[_]Limb {big_base}, .positive = true }).toManaged(allocator);

    while (num_len > 1) {
        div._basecase_div_rem(limb_buffer, num[0..num_len], &[_]Limb{big_base});
		try b.divTrunc(&R, &b, &c);
		// std.debug.print("{} {} {}\n", .{num[0], R.limbs[0], num[0] == R.limbs[0]});
		std.debug.assert(num[0] == R.limbs[0]);


        var r: big.DoubleLimb = num[0];
		r <<= @bitSizeOf(Limb);
		r /= big_base;
		r += 1;
        const tmp = num;
        num = limb_buffer;
        limb_buffer = tmp;
        @memset(limb_buffer, 0);

		string_len -= dig_per_limb;
		for(0..dig_per_limb) |_| {
			r *= base;
			string[string_len] = @intCast(r >> @bitSizeOf(Limb));
			r &= std.math.maxInt(Limb);
            string_len += 1;
		}
		string_len -= dig_per_limb;

        // for(0..dig_per_limb) |_| {
        // // while (r != 0) {
        //     string[string_len - 1] = @intCast(r % base);
        //     r /= base;
        //     string_len -= 1;
        // }
        if (num[num_len - 1] == 0)
            num_len -= 1;
    }
	var r = num[0];
	while (r != 0) {
		string[string_len - 1] = @intCast(r % base);
		r /= base;
		string_len -= 1;
	}
}

const subquadra_threshold = 12;
fn subquadratic_rec(allocator: std.mem.Allocator, k: usize, string: []u8, a: *Managed, b: u8) !void {
    // 2k because the k passed to the function is the number of digits of the bottom half of a
    // if (2 * k < constants.digits_per_limb[b]) {
    //     std.debug.assert(a.len() <= 1);

    //     // not string.len - 1 to avoid overflow
    //     var i = string.len;
    //     var value = a.limbs[0]; // k < digits_per_limb => a is contained in one limb

    //     while (value > 0) {
    //         string[i - 1] = @truncate(value % b);
    //         value /= b;
    //         i -= 1;
    //     }
    //     return;
    // }
	if(a.len() <= subquadra_threshold)
		return basecase(allocator, string, a, b);
    var q = try Managed.init(allocator);
    var r = try Managed.init(allocator);
    var base = try Managed.init(allocator);
    defer q.deinit();
    defer r.deinit();
    defer base.deinit();

    // TODO: better memory for base, q and r
    try base.set(b);
    try base.pow(&base, @intCast(k));
    try q.divFloor(&r, a, &base);

    try subquadratic_rec(allocator, k - k / 2, string[0 .. string.len - k], &q, b);
    try subquadratic_rec(allocator, k / 2, string[string.len - k ..], &r, b);
}

fn f(n: anytype) f64 {
    return @floatFromInt(n);
}
fn int(fl: anytype) usize {
    return @intFromFloat(fl);
}

// TODO: use Mutable instead of Managed
fn convert_trunc(allocator: std.mem.Allocator, limb_buffer: []Limb, string: []u8, b: u8, y: *Managed, k: usize, n: usize) !void {
    _ = limb_buffer;
    const alpha = log(b, 2);

    const base = try (Const{ .positive = true, .limbs = &[_]math.big.Limb{b} }).toManaged(allocator);

    for (1..k + 1) |i| {
        const ni = n - int(@floor(f(i) * alpha));
        const ni_1 = n - int(@floor(f(i - 1) * alpha));
        try y.mul(y, &base);
        // try y.mul(y.toConst(), base, limb_buffer, all);

        const limb_size = @bitSizeOf(std.math.big.Limb);
        const r: u8 = @truncate(y.limbs[ni_1 / limb_size] >> @intCast(ni_1 % limb_size));

        try y.shiftRight(y, ni_1 - ni);
        try y.truncate(y, .unsigned, ni);
        string[i - 1] = r;
    }
}

fn log(n: anytype, base: anytype) f64 {
    return std.math.log(f64, @floatFromInt(base), @floatFromInt(n));
}

fn convert_rec(allocator: std.mem.Allocator, limb_buffer: []Limb, string: []u8, b: u8, k: usize, kt: usize, y: *Managed, n: usize, g: usize) !void {
    if (k <= kt) {
        return convert_trunc(allocator, limb_buffer, string, b, y, k, n);
    }

    const kh = (k + 1) / 2;
    const kl = k - kh + 1;
    // TODO: harden against float imprecisions
    const nh = 2 + int(@ceil(log(g, 2) + f(kh) * log(b, 2)));
    const nl = 2 + int(@ceil(log(g, 2) + f(kl) * log(b, 2)));
    var yh = try Managed.init(allocator);
    var yl = try Managed.init(allocator);
    defer yh.deinit();
    defer yl.deinit();
    try yh.shiftRight(y, n - nh);

    var base = try Managed.init(allocator);
    try base.set(b);
    try base.pow(&base, @intCast(k - kl));
    // std.debug.print("{} {} {}\n", .{y.len(), base.len(), big.int.calcMulLimbsBufferLen(y.len(), base.len(), 1)});
    try y.mul(y, &base);
    try y.truncate(y, .unsigned, n);
    try yl.shiftRight(y, n - nl);

    try convert_rec(allocator, limb_buffer, string[0..kh], b, kh, kt, &yh, nh, g);
    const last_high = string[kh - 1];
    try convert_rec(allocator, limb_buffer, string[kh - 1 ..], b, kl, kt, &yl, nl, g);
    const first_low = string[kh - 1];

    if (last_high == b - 1 and first_low == 0) {
        var carry: u8 = 1;
        for (0..kh - 1) |i| {
            // first kh-1 elements
            const j = (kh - 2) - i;
            const s = string[j] + carry;
            string[j] = s % b;
            carry = s / b;
        }
    }
    if (last_high == 0 and first_low == b - 1) {
        for (string[kh - 1 ..]) |*x|
            x.* = 0;
    }
}

pub fn subquadratic_div_free(allocator: std.mem.Allocator, a: Const, b: u8, kt: usize) ![]const u8 {
    std.debug.assert(kt > 2);
    const k: usize = @intFromFloat(@ceil(@as(f64, @floatFromInt(a.bitCountAbs())) * log(2, b)));
    // TODO: check that number (see the paper's errata)
    const g = @max(kt, int(@ceil(log(k, 2))) + 1);
    const n = 2 + int(@ceil(log(g, 2) + f(k) * log(b, 2)));

    var r = try Managed.init(allocator);
    var base = try Managed.init(allocator);
    try base.set(b);
    try base.pow(&base, @intCast(k));
    var y = try a.toManaged(allocator);
    try y.addScalar(&y, 1);
    try y.shiftLeft(&y, n);
    std.debug.print("k: {}, base len: {}, y len: {}\n", .{ k, base.len(), y.len() });
    try y.divFloor(&r, &y, &base);
    try y.addScalar(&y, -1);

    const string = try allocator.alloc(u8, k);
    var al = std.heap.ArenaAllocator.init(allocator);

    // const buf_len = big.int.calcMulLimbsBufferLen(y.len(), 1, 1);
    // const limb_buffer =

    // std.debug.print("y: {}\n", .{y.len()});
    try convert_rec(al.allocator(), &[_]Limb{}, string, b, k, kt, &y, n, g);
    al.deinit();
    for (string) |*x|
        x.* = chars[x.*];
    return string;
}

pub fn div_free_naive_trunc(allocator: std.mem.Allocator, a: Const, b: u8) ![]u8 {
    std.debug.assert(b > 2 and b <= 16);
    const k: usize = @intFromFloat(@ceil(@as(f64, @floatFromInt(a.bitCountAbs())) * log(2, b)));

    const n = 2 + @as(usize, @intFromFloat(@ceil(log(k, 2) + log(b, 2) * @as(f64, @floatFromInt(k)))));
    var base = try Managed.init(allocator);
    var r = try Managed.init(allocator);
    try base.set(b);
    try base.pow(&base, @intCast(k));

    // y = ((a+1) * (2**n)) // (b**k) - 1
    var y = try a.toManaged(allocator);
    defer y.deinit();
    try y.addScalar(&y, 1);
    try y.shiftLeft(&y, n);
    try y.divFloor(&r, &y, &base);
    try y.addScalar(&y, -1);

    base.deinit();
    r.deinit();

    const string = try allocator.alloc(u8, k);
    try convert_trunc(allocator, &[_]Limb{}, string, b, &y, k, n);
    for (string) |*d|
        d.* = chars[d.*];
    return string;
}
