const std = @import("std");
const math = std.math;
const big = math.big;
const Limb = big.Limb;
const Const = big.int.Const;
const Managed = big.int.Managed;
const Mutable = big.int.Mutable;

const c = @cImport({
	@cInclude("stdio.h");
	@cInclude("gmp.h");
});

var gpa = std.heap.GeneralPurposeAllocator(.{}){};
const allocator = gpa.allocator();
var arena = std.heap.ArenaAllocator.init(allocator);


// const digits_per_limb = 9; //math.log(math.big.Limb, 10, math.maxInt(math.big.Limb));

const N_bench = 1;

const Algo = enum {
	trunc,
	rec_trunc,
	native
};


const div = @import("div.zig");


export fn alloc(size: usize) ?*anyopaque {
	const allocated = allocator.alloc(u8, size) catch return null;
	return @ptrCast(allocated.ptr);
}
export fn realloc(ptr: ?*anyopaque, old_size: usize, new_size: usize) ?*anyopaque {
	const previous = @as([*]u8, @ptrCast(ptr))[0..old_size];
	const new = allocator.realloc(previous, new_size) catch return null;
	return new.ptr;
}
export fn free(ptr: ?*anyopaque, size: usize) void {
	if(ptr == null) return;
	allocator.free(@as([*]u8, @ptrCast(ptr))[0..size]);
}



const toString = @import("toString.zig");
const subquadratic = toString.subquadratic;
const subquadratic_iter = toString.subquadratic_iter;
const subquadratic_div_free = toString.subquadratic_div_free;
const div_free_naive_trunc = toString.div_free_naive_trunc;

const digits_per_limb = toString.digits_per_limb;

pub fn main() !void {
	c.mp_set_memory_functions(&alloc, &realloc, &free);

	var a = try Managed.initSet(allocator, 1);
	try a.shiftLeft(&a, 100000);

	var b: c.mpz_t = undefined;
	defer c.mpz_clear(&b);
	c.mpz_init(&b);
	c.mpz_set_ui(&b, 1);
	c.mpz_mul_2exp(&b, &b, 100000);
	// {
	// 	// const str = try a.toString(allocator, 10, .upper);
	// 	const str = try @call(.never_inline, Managed.toString, .{a, allocator, 10, .upper});
	// 	// const str = try toString.naiveToString(allocator, a.toConst(), 10);
	// 	// std.debug.print("{s}\n", .{str});
	// 	std.mem.doNotOptimizeAway(&str);
	// }
	{
		const str = try subquadratic(allocator, &a, 10);
		std.mem.doNotOptimizeAway(&str);
		// const str2: ?[*:0]u8 = c.mpz_get_str(null, 10, &b);
		// const string = std.mem.span(str2.?);
		// std.debug.print("{s}\n\n", .{str});
		// std.debug.print("{s}\n", .{string});
		// std.debug.print("{} {}\n", .{str.len, string.len});
		// std.debug.assert(std.mem.eql(u8, str, string));
	}
	{
		const str: ?[*:0]u8 = c.mpz_get_str(null, 10, &b);
		const string = std.mem.span(str.?);
		std.mem.doNotOptimizeAway(&string);
	}


}



pub fn ___main() !void {
	c.mp_set_memory_functions(&alloc, &realloc, &free);

	var a: c.mpz_t = undefined;
	var b: c.mpz_t = undefined;
	var q: c.mpz_t = undefined;
	var r: c.mpz_t = undefined;
	defer c.mpz_clear(&a);
	defer c.mpz_clear(&b);
	defer c.mpz_clear(&q);
	defer c.mpz_clear(&r);
	c.mpz_init(&a);
	c.mpz_init(&b);
	c.mpz_init(&q);
	c.mpz_init(&r);
	std.debug.assert(c.mpz_set_str(&a, "2", 10) == 0);
	std.debug.assert(c.mpz_set_str(&b, "2", 10) == 0);
	c.mpz_pow_ui(&a, &a, 10000000);
	c.mpz_sub_ui(&a, &a, 1);
	
	c.mpz_pow_ui(&b, &b, 1000000);
	c.mpz_sub_ui(&b, &b, std.math.maxInt(Limb));
	c.mpz_mul_2exp(&b, &b, 5000000);

	c.mpz_fdiv_qr(&q, &r, &a, &b);

	// const str: ?[*:0]u8 = c.mpz_get_str(null, 10, &q);
	// const string = std.mem.span(str.?);
	// std.debug.print("{s}\n", .{string});
}

pub fn ______main() !void {
	// {
	// 	var c = try Managed.initSet(allocator, 11);
	// 	var d = try Managed.initSet(allocator, -2);
	// 	// try q.divFloor(&r, &c, &d);
	// 	const res = try div.unbalanced_division(allocator, &c, &d);
	// 	debug("c", c);
	// 	debug("d", d);
	// 	debug("q", res.q);
	// 	debug("r", res.r);
	// 	return;
	// }
	// defer _ = gpa.deinit();
	var a = try Managed.init(allocator);
	var b = try Managed.init(allocator);
	try a.set(1);
	try a.shiftLeft(&a, 20000000);
	try a.addScalar(&a, -1);
	// try a.setString(10, "105423618548421968754897441896456184123456789485461848674631841264781721614848182658128446216484684684");
	// try a.pow(&a, 300);
	// try a.pow(&a, 10);
	// try a.pow(&a, 200);
	try b.set(1);
	try b.shiftLeft(&b, 2000000);
	try b.addScalar(&b, -std.math.maxInt(Limb));
	// try b.pow(&b, 2);
	try b.shiftLeft(&b, 5000000);
	// try b.setString(10, "123482318184318441235478188484");
	// try b.pow(&b, 200);
	// try a.pow(&a, 10);
	std.debug.print("{} {}\n", .{a.len(), b.len()});
	var q = try Managed.init(allocator);
	var r = try Managed.init(allocator);
	const res2 = try div.unbalanced_division(allocator, &a, &b);
	// const res = try div.basecase_div_rem(allocator, &a, &b);
	// const res = try div.recursive_div_rem(allocator, &a, &b);
	// {
	// 	std.mem.doNotOptimizeAway(&res);
	// 	return;
	// }


	// try q.divFloor(&r, &a, &b);
	try @call(.never_inline, Managed.divFloor, .{&q, &r, &a, &b});
	// {
	// 	std.mem.doNotOptimizeAway(&q);
	// 	return;
	// }
	std.mem.doNotOptimizeAway(&q);
	// std.mem.doNotOptimizeAway(&res);
	std.mem.doNotOptimizeAway(&res2);
	// std.debug.print("{} {}\n", .{res.q.len(), res.r.len()});
	// std.debug.print("{} {}\n", .{q.len(), r.len()});
    // 
	// if(!q.eql(res.q)) @panic("q != res.q");
	// if(!r.eql(res.r)) @panic("r != res.r");

}



pub fn _main() !void {
	defer _ = gpa.deinit();
	const args = try std.process.argsAlloc(allocator);
	defer std.process.argsFree(allocator, args);

	var a = try Managed.init(allocator);
	try a.set(1);
	defer a.deinit();

	if(args.len == 1) {
		for(10000..100000) |i| {
			if(i % 1000 == 0)
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
	const algo = try std.fmt.parseInt(usize, args[1], 10);
	const num = try std.fmt.parseInt(usize, args[2], 10);
	try a.shiftLeft(&a, num);

	const div_free_kt = if(args.len == 4) try std.fmt.parseInt(usize, args[3], 10) else digits_per_limb;
	
	const string = try switch(algo) {
		0 => subquadratic(arena.allocator(), &a, 10),
		1 => subquadratic_iter(arena.allocator(), &a, 10),
		2 => subquadratic_div_free(allocator, a.toConst(), 10, div_free_kt),
		3 => div_free_naive_trunc(arena.allocator(), a.toConst(), 10),
		else => @panic("unknown algo")
	};

	// std.debug.print("1: {s}\n\n", .{string});
	// std.debug.print("2: {s}\n\n", .{string2});
	// std.debug.print("eql: {}\n", .{std.mem.eql(u8, string, string2)});

	std.mem.doNotOptimizeAway(&string);
	arena.deinit();
}


pub fn debug(name: []const u8, n: anytype) void {
	std.debug.print("{s}: {s}\n", .{name, n.toString(allocator, 10, .upper) catch unreachable});
	// std.debug.print("{s}: {s}\n", .{name, subquadratic(arena.allocator(), n, 10) catch unreachable});
}



