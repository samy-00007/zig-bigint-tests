const std = @import("std");
const math = std.math;
const BigInt = math.big.int;
const Const = BigInt.Const;
const Managed = BigInt.Managed;

var gpa = std.heap.GeneralPurposeAllocator(.{}){};
const allocator = gpa.allocator();

const chars = "0123456789ABCDEF";

pub fn main() !void {
	var a = try Managed.init(allocator);
	try a.set(1);
	try a.shiftLeft(&a, 1000);

	std.debug.print("{s}\n\n", .{try div_free_naive_trunc(allocator, a.toConst(), 10)});
	std.debug.print("{s}\n\n", .{try subquadratic_div_free(allocator, a.toConst(), 10, 20)});
	std.debug.print("{s}\n", .{try a.toString(allocator, 10, .upper)});
	// debug("a", a);
	
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
fn convert_trunc(all: std.mem.Allocator, string: []u8, b: u8, y: *Managed, k: usize, n: usize) !void {
	const alpha = log(b, 2);

	const base = try (Const {.positive = true, .limbs = &[_]math.big.Limb{b}}).toManaged(all);

	for(1..k+1) |i| {
		const ni = n - int(@floor(f(i) * alpha));
		const ni_1 = n - int(@floor(f(i - 1) * alpha));
		try y.mul(y, &base);

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




fn convert_rec(all: std.mem.Allocator, string: []u8, b: u8, k: usize, kt: usize, y: *Managed, n: usize, g: usize) !void {
	if(k <= kt) {
		return convert_trunc(all, string, b, y, k, n);
	}

	const kh = (k + 1) / 2;
	const kl = k - kh + 1;
	// TODO: harden against float imprecisions
	const nh = 2 + int(@ceil(log(g, 2) + f(kh) * log(b, 2)));
	const nl = 2 + int(@ceil(log(g, 2) + f(kl) * log(b, 2)));
	var yh = try Managed.init(all);
	var yl = try Managed.init(all);
	try yh.shiftRight(y, n - nh);

	var base = try Managed.init(all);
	try base.set(b);
	try base.pow(&base, @intCast(k-kl));
	try y.mul(y, &base);
	try y.truncate(y, .unsigned, n);
	try yl.shiftRight(y, n-nl);

	try convert_rec(all, string[0..kh], b, kh, kt, &yh, nh, g);
	const last_high = string[kh-1];
	try convert_rec(all, string[kh-1..], b, kl, kt, &yl, nl, g);
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
	//const k = int(@ceil(log(a, b))) + 1;
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
	try convert_rec(all, string, b, k, kt, &y, n, g);
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
	try convert_trunc(all, string, b, &y, k, n);
	for(string) |*d| 
		d.* = chars[d.*];
	return string;
}
