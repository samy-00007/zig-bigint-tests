const std = @import("std");
const math = std.math;
const big = math.big;
const Limb = big.Limb;
const Const = big.int.Const;
const Managed = big.int.Managed;
const Mutable = big.int.Mutable;

var gpa = std.heap.GeneralPurposeAllocator(.{}){};
const allocator = gpa.allocator();
var arena = std.heap.ArenaAllocator.init(allocator);

const chars = "0123456789ABCDEF";

// const digits_per_limb = 9; //math.log(math.big.Limb, 10, math.maxInt(math.big.Limb));
const digits_per_limb = math.log(math.big.Limb, 10, math.maxInt(math.big.Limb));

const N_bench = 1;

const Algo = enum {
	trunc,
	rec_trunc,
	native
};

fn size_in_base_upper_bound(bit_count: usize, base: u8) usize {
	return int(f(bit_count) * log(2, base)) + 1;
}
pub fn main() !void {
	const args = try std.process.argsAlloc(allocator);

	var a = try Managed.init(allocator);
	try a.set(1);

	if(args.len == 1) {
		for(10000..100000) |i| {
			std.debug.print("i: {}\n", .{i});
			var b = try a.clone();
			try b.shiftLeft(&b, i);
			const string1 = try subquadratic(arena.allocator(), &b, 10);
			const string2 = try b.toString(arena.allocator(), 10, .upper);
			if(!std.mem.eql(u8, string1, string2)) {
				std.debug.panic("i = {}\n", .{i});
			}
		}
		return;
	}
	const num = try std.fmt.parseInt(usize, args[1], 10);
	try a.shiftLeft(&a, num);
	
	const string = try a.toString(arena.allocator(), 10, .upper);
	// const string = try subquadratic_div_free(allocator, a.toConst(), 10, digits_per_limb);
	const string2 = try subquadratic(arena.allocator(), &a, 10);
	std.debug.print("1: {s}\n\n", .{string});
	std.debug.print("2: {s}\n\n", .{string2});
	std.debug.print("eql: {}\n", .{std.mem.eql(u8, string, string2)});
	//
  	// std.debug.print("res: {s}\n", .{string});
	// std.mem.doNotOptimizeAway(&string);

	// bench(a)
}

fn subquadratic(all: std.mem.Allocator, a: *Managed, b: u8) ![]u8 {
	var string = try allocator.alloc(u8, size_in_base_upper_bound(a.bitCountAbs(), 10));
	@memset(string, 0);

	const N = a.bitCountAbs() - 1;
	const k = int(@floor(f(N) * log(2, b) / 2)) + 1;

	try subquadratic_rec(all, k, string, a, b);
	var i: usize = 0;
	for(string) |x| {
		if(x != 0) break;
		i += 1;
	}
	std.mem.copyForwards(u8, string[0..string.len - i], string[i..]);
	string = try all.realloc(string, string.len - i);

	for(string) |*x|
		x.* = chars[x.*];

	return string;
}

fn subquadratic_rec(all: std.mem.Allocator, k: usize, string: []u8, a: *Managed, b: u8) !void {
	// 2k because the k passed to the function is the number of digits of the bottom half of a
	if(2*k < digits_per_limb) {
		std.debug.assert(a.len() <= 1);

		// not string.len - 1 to avoid overflow
		var i = string.len;
		var value = a.limbs[0]; // k < digits_per_limb => a is contained in one limb

		while(value > 0) {
			string[i - 1] = @truncate(value % b);
			value /= b;
			i -= 1;
		}
		return;
	}
	var q = try Managed.init(all);
	var r = try Managed.init(all);
	var base = try Managed.init(all);
	defer q.deinit();
	defer r.deinit();
	defer base.deinit();

	try base.set(b);
	try base.pow(&base, @intCast(k));
	try q.divFloor(&r, a, &base);

	try subquadratic_rec(all, k - k / 2, string[0..string.len - k], &q, b);
	try subquadratic_rec(all, k / 2, string[string.len - k..], &r, b);
}





fn bench(a: Managed) !void {
	const N = N_bench;
	const args = try std.process.argsAlloc(allocator);

	if(args.len == 1) {
		var t = std.time.nanoTimestamp();
		// for(0..N) |_| {
		// 	const res = try div_free_naive_trunc(allocator, a.toConst(), 10);
		// 	std.mem.doNotOptimizeAway(&res);
		// }
		std.debug.print("naive trunc: {}µs / run\n", .{@divFloor(std.time.nanoTimestamp() - t, 1000*N)});
		t = std.time.nanoTimestamp();
		for(0..N) |_| {
			const res = try subquadratic_div_free(allocator, a.toConst(), 10, digits_per_limb);
			std.mem.doNotOptimizeAway(&res);
		}
		std.debug.print("rec trunc: {}µs / run\n", .{@divFloor(std.time.nanoTimestamp() - t, 1000*N)});
		t = std.time.nanoTimestamp();
		for(0..N) |_| {
			const res = try a.toString(allocator, 10, .upper);
			std.mem.doNotOptimizeAway(&res);
		}
		std.debug.print("default: {}µs / run\n", .{@divFloor(std.time.nanoTimestamp() - t, 1000*N)});
		return;
	}
	const algo: Algo = switch(args[1][0]) {
		'0' => .trunc,
		'1' => .rec_trunc,
		'2' => .native,
		else => @panic("wrong algo")
	};

	switch(algo) {
		.trunc => {
			for(0..N) |_| {
				const res = try div_free_naive_trunc(allocator, a.toConst(), 10);
				std.mem.doNotOptimizeAway(&res);
			}
		},
		.rec_trunc => {
			for(0..N) |_| {
				const res = try subquadratic_div_free(allocator, a.toConst(), 10, digits_per_limb);
				std.mem.doNotOptimizeAway(&res);
			}
		},
		.native => {
			for(0..N) |_| {
				const res = try a.toString(allocator, 10, .upper);
				std.mem.doNotOptimizeAway(&res);
			}
		}
	}
}

fn f(n: anytype) f64 {
	return @floatFromInt(n);
}
fn int(fl: anytype) usize {
	return @intFromFloat(fl);
}

fn debug(name: []const u8, n: anytype) void {
	std.debug.print("{s}: {s}\n", .{name, n.toString(allocator, 10, .upper) catch unreachable});
}






// TODO: use Mutable instead of Managed
fn convert_trunc(all: std.mem.Allocator, limb_buffer: []Limb, string: []u8, b: u8, y: *Managed, k: usize, n: usize) !void {
	_ = limb_buffer;
	const alpha = log(b, 2);

	const base = try (Const {.positive = true, .limbs = &[_]math.big.Limb{b}}).toManaged(all);

	for(1..k+1) |i| {
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



fn convert_rec(all: std.mem.Allocator, limb_buffer: []Limb, string: []u8, b: u8, k: usize, kt: usize, y: *Managed, n: usize, g: usize, abcd: bool) !void {
	if(k <= kt) {
		_ = abcd;
		// if(abcd)
		// 	@memset(string, 1)
		// else
		// 	@memset(string, 0);
		// return;
		return convert_trunc(all, limb_buffer, string, b, y, k, n);
	}

	// debug("y", y);

	const kh = (k + 1) / 2;
	const kl = k - kh + 1;
	// TODO: harden against float imprecisions
	const nh = 2 + int(@ceil(log(g, 2) + f(kh) * log(b, 2)));
	const nl = 2 + int(@ceil(log(g, 2) + f(kl) * log(b, 2)));
	var yh = try Managed.init(all);
	var yl = try Managed.init(all);
	defer yh.deinit();
	defer yl.deinit();
	try yh.shiftRight(y, n - nh);

	var base = try Managed.init(all);
	try base.set(b);
	try base.pow(&base, @intCast(k-kl));
	// std.debug.print("{} {} {}\n", .{y.len(), base.len(), big.int.calcMulLimbsBufferLen(y.len(), base.len(), 1)});
	try y.mul(y, &base);
	try y.truncate(y, .unsigned, n);
	try yl.shiftRight(y, n-nl);

	try convert_rec(all, limb_buffer, string[0..kh], b, kh, kt, &yh, nh, g, true);
	const last_high = string[kh-1];
	try convert_rec(all, limb_buffer, string[kh-1..], b, kl, kt, &yl, nl, g, false);
	const first_low = string[kh-1];

	if(last_high == b - 1 and first_low == 0) {
		var carry: u8 = 1;
		for(0..kh - 1) |i| {
			// first kh-1 elements
			const j = (kh - 2) - i;
			const s = string[j] + carry;
			string[j] = s % b;
			carry = s / b;
		}
	}
	if(last_high == 0 and first_low == b - 1) {
		for(string[kh-1..]) |*x|
			x.* = 0;
	}
}

fn subquadratic_div_free(all: std.mem.Allocator, a: Const, b: u8, kt: usize) ![]const u8 {
	std.debug.assert(kt > 2);
	const k: usize = @intFromFloat(@ceil(@as(f64, @floatFromInt(a.bitCountAbs())) * log(2, b)));
	const g = @max(kt, int(@ceil(log(k, 2))) + 1);
	const n = 2 + int(@ceil(log(g, 2) + f(k) * log(b, 2)));

	var r = try Managed.init(all);
	var base = try Managed.init(all);
	try base.set(b);
	try base.pow(&base, @intCast(k));
	var y = try a.toManaged(all);
	try y.addScalar(&y, 1);
	try y.shiftLeft(&y, n);
	try y.divFloor(&r, &y, &base);
	try y.addScalar(&y, -1);

	const string = try all.alloc(u8, k);
	var al = std.heap.ArenaAllocator.init(all);
	
	// const buf_len = big.int.calcMulLimbsBufferLen(y.len(), 1, 1);
	// const limb_buffer = 


	// std.debug.print("y: {}\n", .{y.len()});
	try convert_rec(al.allocator(), &[_]Limb{}, string, b, k, kt, &y, n, g, false);
	al.deinit();
	for(string) |*x|
		x.* = chars[x.*];
	return string;
}


































fn div_free_naive_trunc(all: std.mem.Allocator, a: Const, b: u8) ![]u8 {

	std.debug.assert(b > 2 and b <= 16);
	const k: usize = @intFromFloat(@ceil(@as(f64, @floatFromInt(a.bitCountAbs())) * log(2, b)));

	const n = 2 + @as(usize, @intFromFloat(@ceil(log(k, 2) + log(b, 2) * @as(f64, @floatFromInt(k)))));
	var base = try Managed.init(all);
	var r = try Managed.init(all);
	try base.set(b);
	try base.pow(&base, @intCast(k));

	// y = ((a+1) * (2**n)) // (b**k) - 1
	var y = try a.toManaged(all);
	defer y.deinit();
	try y.addScalar(&y, 1);
	try y.shiftLeft(&y, n);
	try y.divFloor(&r, &y, &base);
	try y.addScalar(&y, -1);

	base.deinit();
	r.deinit();

	const string = try all.alloc(u8, k);
	try convert_trunc(all, &[_]Limb {}, string, b, &y, k, n);
	for(string) |*d| 
		d.* = chars[d.*];
	return string;
}
