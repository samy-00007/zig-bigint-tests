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
	const q_len = div.calculateLenQ(llnormalize(A.limbs), B.len());
	const a_len = llnormalize(A.limbs);
	const allocation = try allocator.alloc(Limb, q_len + a_len);
	defer allocator.free(allocation);

	const q_limbs = allocation[0..q_len];
	const a_limbs = allocation[q_len..];
	@memcpy(a_limbs, A.limbs[0..a_len]);

	const b_limbs = B.limbs[0..B.len()];

	@memset(q_limbs, 0);
	div._basecase_div_rem(q_limbs, a_limbs, b_limbs, false);

	return .{
		Const { .positive = true, .limbs = try allocator.dupe(Limb, q_limbs[0..llnormalize(q_limbs)]) },
		Const { .positive = true, .limbs = try allocator.dupe(Limb, a_limbs[0..llnormalize(a_limbs)]) }
	};
}


const div = @import("div.zig");
const D_error = std.mem.Allocator.Error;


const DIV_LIMIT = 50;

const limb_bits = @bitSizeOf(Limb);


// B must be normalized
pub fn D_2n_1n(allocator: Allocator, A_: Const, B_: Const) !struct { Const, Const } {
	var A = try A_.toManaged(allocator);
	var B = try B_.toManaged(allocator);
	const k = div.get_normalize_k(B_);
	try A.shiftLeft(&A, k);
	try B.shiftLeft(&B, k);

	const n = B.len();
	const Q = try allocator.alloc(Limb, n);
	const a = try allocator.alloc(Limb, 2*n);
	@memset(Q, 0);
	@memset(a, 0);
	const A_limbs = A.limbs[0..A.len()];
	@memcpy(a[0..A_limbs.len], A_limbs);
	try _D_2n_1n(allocator, Q, a, B.limbs[0..n]);

	llshr(a[0..n], a[0..n], k);

	return .{
		Const { .positive = true, .limbs = try allocator.realloc(Q, llnormalize(Q)) },
		Const { .positive = true, .limbs = try allocator.realloc(a, llnormalize(a[0..n])) }
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
		div._basecase_div_rem(Q, A[0..llnormalize(A)], B, false);
		return;
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
		std.debug.assert(B[B.len - 1] >> (@bitSizeOf(Limb) - 1) == 1); // ensure B is normalized

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
	// const D = try mul(allocator, Const { .positive = true, .limbs = Q }, Const { .positive = true, .limbs = B[0..n] });
	// var R_is_negative = div.llsubcarry(R, R, D.limbs) != 0;
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


// pub fn D_r_s(allocator: Allocator, A: *Managed, B: *Managed) !struct { Const, Const } {
// B must be softly normalized (using llnormalize)
// and A must have 1 extra capacity to allow the normalization step
pub fn D_r_s(allocator: Allocator, A: Const, B: Const) !struct { Const, Const } {
	const s = B.limbs.len;
	const k = int(std.math.log2(f(s) / f(DIV_LIMIT))) + 1;
	const m = std.math.pow(usize, 2, k);
	std.debug.assert(std.math.pow(usize, 2, k) * DIV_LIMIT > s);
	std.debug.assert(std.math.pow(usize, 2, k-1) * DIV_LIMIT <= s);

	const j: usize = @intFromFloat(@ceil(f(s) / f(m)));
	const n = j * m;

	const sigma = n * limb_bits - B.bitCountAbs();

	// step 5
	// t is determined before the shift so we only allocate once
	const t = blk: {
		// bit count of a after the shift
		const new_bit_count = A.bitCountAbs() + sigma;
		// limb count of a after the shift
		const limbs_len = new_bit_count / limb_bits + @intFromBool(new_bit_count % limb_bits != 0);
		// upper part of the most significant byte of A after the shift
		// we only care about its leftmost bit, so no need for its lower part
		const leftmost_byte = A.limbs[A.limbs.len - 1] << @intCast(sigma % limb_bits);
		const l = limbs_len / n;
		const rem = limbs_len % n;
		if(rem == 0)
			break :blk
				if(leftmost_byte >> 63 == 1)
					l + 1 // A >= β^(n*l) / 2
				else
					l;
		break :blk l + 1;
	};

	const allocation = try allocator.alloc(Limb, n + t*n + (t-1) * n);
	defer allocator.free(allocation);

	const B_limbs = allocation[0..n];
	@memcpy(B_limbs[0..B.limbs.len], B.limbs);
	@memset(B_limbs[B.limbs.len..], 0);


	// TODO: better
	var R = allocation[n..n + t*n];
	@memcpy(R[0..A.limbs.len], A.limbs);
	@memset(R[A.limbs.len..], 0);

	llshl(R, R[0..A.limbs.len], sigma);
	llshl(B_limbs, B_limbs[0..B.limbs.len], sigma);

	const Q = allocation[n + t*n..n + t*n + n * (t - 1)];
	@memset(Q, 0);

	// R is written in A[0..n]
	for(0..t-2 + 1) |j_| {
		const i = t-2 - j_;
		const Z = R[i * n .. (i + 2) * n];

		_D_2n_1n(Q[i*n..(i+1)*n], Z, B_limbs);
	}

	llshr(R[0..n], R[0..n], sigma);

	const R0 = R[0..n];
	return .{
		Const { .positive = true, .limbs = try allocator.dupe(Limb, Q[0..llnormalize(Q)]) },
		Const { .positive = true, .limbs = try allocator.dupe(Limb, R0[0..llnormalize(R0)]) }
	};
}



fn llshl(r: []Limb, a: []const Limb, shift: usize) void {
    @setRuntimeSafety(false);
    std.debug.assert(a.len >= 1);

    const interior_limb_shift = @as(std.math.big.Log2Limb, @truncate(shift));

    // We only need the extra limb if the shift of the last element overflows.
    // This is useful for the implementation of `shiftLeftSat`.
    if (a[a.len - 1] << interior_limb_shift >> interior_limb_shift != a[a.len - 1]) {
        std.debug.assert(r.len >= a.len + (shift / limb_bits) + 1);
    } else {
        std.debug.assert(r.len >= a.len + (shift / limb_bits));
    }

    const limb_shift = shift / limb_bits + 1;

    var carry: Limb = 0;
    var i: usize = 0;
    while (i < a.len) : (i += 1) {
        const src_i = a.len - i - 1;
        const dst_i = src_i + limb_shift;

        const src_digit = a[src_i];
        r[dst_i] = carry | @call(.always_inline, std.math.shr, .{
            Limb,
            src_digit,
            limb_bits - @as(Limb, @intCast(interior_limb_shift)),
        });
        carry = (src_digit << interior_limb_shift);
    }

    r[limb_shift - 1] = carry;
    @memset(r[0 .. limb_shift - 1], 0);
}

fn llshr(r: []Limb, a: []const Limb, shift: usize) void {
    @setRuntimeSafety(false);
    std.debug.assert(a.len >= 1);
    std.debug.assert(r.len >= a.len - (shift / limb_bits));

    const limb_shift = shift / limb_bits;
    const interior_limb_shift = @as(std.math.big.Log2Limb, @truncate(shift));

    var i: usize = 0;
    while (i < a.len - limb_shift) : (i += 1) {
        const dst_i = i;
        const src_i = dst_i + limb_shift;

        const src_digit = a[src_i];
        const src_digit_next = if (src_i + 1 < a.len) a[src_i + 1] else 0;
        const carry = @call(.always_inline, std.math.shl, .{
            Limb,
            src_digit_next,
            limb_bits - @as(Limb, @intCast(interior_limb_shift)),
        });
        r[dst_i] = carry | (src_digit >> interior_limb_shift);
    }
}
