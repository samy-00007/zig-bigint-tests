const std = @import("std");
const Allocator = std.mem.Allocator;
const big = std.math.big;
const Managed = big.int.Managed;
const Const = big.int.Const;
const Limb = big.Limb;
const DoubleLimb = big.DoubleLimb;
const HalfLimb = big.HalfLimb;

const limb_size = @sizeOf(Limb);

const debug = @import("main.zig").debug;

// preconditions:
// - b must be normalized
// - q must fit in one digit
fn DivTwoDigitsByOne(ah: Limb, al: Limb, b: Limb) struct { Limb, Limb } {
    const AH: [*]HalfLimb = @ptrCast(@constCast(&ah));
    const AL: [*]HalfLimb = @ptrCast(@constCast(&al));
    const B: [*]HalfLimb  = @ptrCast(@constCast(&b));
    const q1: HalfLimb, const r: Limb = DivThreeHalvesByTwo(AH[0], AH[1], AL[0], B[0], B[1]);
    const R: [*]HalfLimb  = @ptrCast(@constCast(&r));
    const q2: HalfLimb, const S: Limb = DivThreeHalvesByTwo(R[0], R[1], AL[1], B[0], B[1]);
    return . {
      std.mem.bytesToValue(Limb, &[_]HalfLimb {q1, q2}),
      S
    };
  }

fn DivThreeHalvesByTwo(a1: HalfLimb, a2: HalfLimb, a3: HalfLimb, b1: HalfLimb, b2: HalfLimb) struct { HalfLimb, Limb } {
      const A = std.mem.bytesToValue(Limb, &[_]HalfLimb { a1, a2 });
      const B = std.mem.bytesToValue(Limb, &[_]HalfLimb { b1, b2 });
      const q: HalfLimb = @intCast(A / b1);
      const c: HalfLimb = @intCast(A - q * b1);
      const D = q * b2;
      var R = std.mem.bytesToValue(Limb, &[_]HalfLimb { c, a3 }) -% D;

      if(R < 0) {
          q -= 1;
          R += B;
          if(R < 0) {
              q -= 1;
              R += B;
          }
      }
      return .{ q, R };
 }


const llnormalize = div.llnormalize;

pub fn school_division(allocator: Allocator, A: Const, B: *Managed) D_error!struct { Const, Const } {
	const q_limbs = try allocator.alloc(Limb, div.calculateLenQ(llnormalize(A.limbs), B.len()));
	const a_limbs = try allocator.dupe(Limb, A.limbs[0..llnormalize(A.limbs)]);
	const b_limbs = try allocator.dupe(Limb, B.limbs[0..B.len()]);
	@memset(q_limbs, 0);
	div._basecase_div_rem(q_limbs, a_limbs, b_limbs, false);
	// var Q = try Managed.init(allocator);
	// var R = try Managed.init(allocator);
	// try Q.divFloor(&R, &(try A.toManaged(allocator)), B);

	// return .{ Q.toConst(), R.toConst() };
	return .{
		Const { .positive = true, .limbs = q_limbs[0..llnormalize(q_limbs)] },
		Const { .positive = true, .limbs = a_limbs[0..llnormalize(a_limbs)] }
	};
}


const div = @import("div.zig");
const D_error = std.mem.Allocator.Error;


const DIV_LIMIT = 2;

const limb_bits = @bitSizeOf(Limb);


// B must be normalized
pub fn D_2n_1n(allocator: Allocator, A: Const, B: Const) !struct { Const, Const } {
	const n = B.limbs.len;
	const Q = try allocator.alloc(Limb, n);
	const a = try allocator.alloc(Limb, 2*n);
	@memset(a, 0);
	const A_limbs = A.limbs[0..llnormalize(A.limbs)];
	@memcpy(a[0..A_limbs.len], A_limbs);
	_D_2n_1n(Q, a, B.limbs);

	return .{
		Const { .positive = true, .limbs = Q },
		Const { .positive = true, .limbs = try allocator.realloc(a, n) }
	};
}


// B must be normalized, and A shifted by the same amount
// returns .{ Q, R }
// pub fn D_2n_1n(allocator: Allocator, A: Const, B: *Managed) D_error!struct { Const, Const } {
// R is written in A[0..n]
pub fn _D_2n_1n(Q: []Limb, A: []Limb, B: []const Limb) void {
	const n = B.len;
	const k = n / 2;
	{
		std.debug.assert(Q.len == n);
		std.debug.assert(A.len == 2*n);
		// preconditions
		// β^n / 2 <= B < β^n
		std.debug.assert(B[n - 1] >> (@bitSizeOf(Limb) - 1) == 1); // ensure B is normalized

		// try B.shiftLeft(B, n * limb_bits);
		// std.debug.assert(B.toConst().order(A) == .gt); // A < β^n * B
		// try B.shiftRight(B, n * limb_bits);
	}

	if(n % 2 == 1 or n <= DIV_LIMIT) {
		return div._basecase_div_rem(Q, A, B, false);
	}

	const AH = A[k..];
	// D_3n_2n writes R1 in AH[0..2k]
	_D_3n_2n(Q[k..], AH, B);

	const AL = A[0..3*k];
	// D_3n_2n writes R in AL[0..2k] = A[0..n]
	_D_3n_2n(Q[0..k], AL, B);
}


// pub fn D_3n_2n(allocator: std.mem.Allocator, A: Const, B: *Managed) D_error!struct { Const, Const } {
// puts R in A[0..2n]
pub fn _D_3n_2n(Q: []Limb, A: []Limb, B: []const Limb) void {
	const n = B.len / 2;
	{
		std.debug.assert(B.len % 2 == 0);
		std.debug.assert(A.len == 3 * n);
		std.debug.assert(Q.len == n);
		// preconditions
		// β^2n / 2 <= B < β^2n
		std.debug.assert(B[n - 1] >> (@bitSizeOf(Limb) - 1) == 1); // ensure B is normalized

		// try B.shiftLeft(B, n * limb_bits);
		// std.debug.assert(B.toConst().order(A) == .gt); // A < β^n * B
		// try B.shiftRight(B, n * limb_bits);
	}
	const A1 = A[2*n..];
	const B1 = B[n..];
	const R1 = A[n..];
	// llcmp normalizes its inputs
	if(div.llcmp(A1, B1) == -1) {
		// A1 < B1
		_D_2n_1n(Q, A[n..], B[n..]);
	} else {
		// Q = β^n - 1
		Q[n - 1] = std.math.maxInt(Limb);
		const underflows = div.llsubcarryoffsetright(R1, R1, B1, n) != 0;
		// not sure if necessary
		std.debug.assert(!underflows);
		_ = div.lladdcarry(R1, R1, B1);
	}

	// TODO: check if possible to use A[0..2*n] instead
	const R = A;
	var R_is_negative = div.llmulaccLongWithOverflowOffset(.sub, R, Q, B[0..n], 0);

	while(R_is_negative) {
		R_is_negative = div.lladdcarry(R, R, B) == 0;
		div.llsub(Q, Q, &[_]Limb{1});
	}
}


fn mul(allocator: Allocator, A: Const, B: Const) D_error!Const {
	var M = try Managed.init(allocator);
	try M.mul(&(try A.toManaged(allocator)), &(try B.toManaged(allocator)));

	return M.toConst();
}


fn log(n: anytype, base: anytype) f64 {
    return std.math.log(f64, @floatFromInt(base), @floatFromInt(n));
}

fn f(n: anytype) f64 {
    return @floatFromInt(n);
}
fn int(fl: anytype) usize {
    return @intFromFloat(fl);
}


pub fn D_r_s(allocator: Allocator, A: *Managed, B: *Managed) !struct { Const, Const } {
	const s = B.len();
	const k = int(std.math.log2(f(s) / f(DIV_LIMIT))) + 1;
	const m = std.math.pow(usize, 2, k);
	std.debug.assert(std.math.pow(usize, 2, k) * DIV_LIMIT > s);
	std.debug.assert(std.math.pow(usize, 2, k-1) * DIV_LIMIT <= s);

	const j: usize = @intFromFloat(@ceil(f(s) / f(m)));
	const n = j * m;

	const sigma = div.get_normalize_k(B.toConst());
	try A.shiftLeft(A, sigma);
	try B.shiftLeft(B, sigma);

	// TODO: better
	const t = blk: {
		var beta = try Managed.initSet(allocator, 1);
		var l: usize = 2;
		try beta.shiftLeft(&beta, l * n * limb_bits);
		try beta.shiftRight(&beta, 1); // div by 2
		while(A.order(beta) != .lt) {
			l += 1;
			try beta.shiftLeft(&beta, limb_bits * n);
		}
		break :blk l;
	};

	var q_limbs = try allocator.alloc(Limb, (t-1) * n);
	@memset(q_limbs, 0);

	var z_limbs = try allocator.alloc(Limb, 2 * n);
	@memset(z_limbs, 0);
	@memcpy(z_limbs[0..A.len()], A.limbs[(t-2)*n..A.len()]);

	for(0..t-2 + 1) |j_| {
		const i = t-2 - j_;

		const Z = Const { .positive = true, .limbs = z_limbs[0..div.llnormalize(z_limbs)] };
		const Q, const R = try _D_2n_1n(allocator, Z, B);
		@memset(z_limbs, 0);
		if(i > 0)
			@memcpy(z_limbs[0..n], A.limbs[(i-1) * n..i*n]);
		@memcpy(z_limbs[n..n + R.limbs.len], R.limbs);

		std.debug.assert(Q.limbs.len <= n);
		@memcpy(q_limbs[i*n..i*n + Q.limbs.len], Q.limbs);
	}

	return .{
		Const { .positive = true, .limbs = q_limbs[0..div.llnormalize(q_limbs)] },
		Const { .positive = true, .limbs = z_limbs[n..div.llnormalize(z_limbs)] }
	};
}


