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
	div._basecase_div_rem(q_limbs, a_limbs, b_limbs);
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
// B must be normalized, and A shifted by the same amount
// returns .{ Q, R }
pub fn D_2n_1n(allocator: Allocator, A: Const, B: *Managed) D_error!struct { Const, Const } {
	const n = B.len();
	const k = n / 2;
	{
		// preconditions
		// β^n / 2 <= B < β^n
		std.debug.assert(B.limbs[B.len() - 1] >> (@bitSizeOf(Limb) - 1) == 1); // ensure B is normalized

		try B.shiftLeft(B, n * limb_bits);
		std.debug.assert(B.toConst().order(A) == .gt); // A < β^n * B
		try B.shiftRight(B, n * limb_bits);
	}

	if(n % 2 == 1 or n <= DIV_LIMIT) {
		return school_division(allocator, A, B);
	}

	const half = n;
	const quarter_l = k;
	const quarter_h = half + k;
	// TODO: handle when A is not 2n sized (fill with 0)
	const A1 = Const { .positive = true, .limbs = A.limbs[quarter_h..A.limbs.len] };
	const A2 = Const { .positive = true, .limbs = A.limbs[half..quarter_h] };
	const A3 = Const { .positive = true, .limbs = A.limbs[quarter_l..half] };
	const A4 = Const { .positive = true, .limbs = A.limbs[0..quarter_l] };

	const B1 = Const { .positive = true, .limbs = B.limbs[0..n / 2] };
	const B2 = Const { .positive = true, .limbs = B.limbs[n / 2..B.len()] };

	{
		const limbs = try allocator.alloc(Limb, n / 2 + 1);
		@memset(limbs, 0);
		limbs[n / 2] = 1;
		const B_n_2 = Const { .positive = true, .limbs = limbs };
		for(&[_]Const {A1, A2, A3, A4, B1, B2}) |x| {
			std.debug.assert(B_n_2.order(x) == .gt);
		}
	}

	var AH = Const { .positive = true, .limbs = A.limbs[quarter_l..A.limbs.len] };
	AH.limbs = AH.limbs[0..div.llnormalize(AH.limbs)];
	const Q1: Const, const R_1: Const = try D_3n_2n(allocator, AH, B);

	if(false) {
		var q = try Managed.init(allocator);
		var r = try Managed.init(allocator);
		try q.divFloor(&r, &(try AH.toManaged(allocator)), B);
		std.debug.assert(q.toConst().eql(Q1));
		std.debug.assert(r.toConst().eql(R_1));
	}

	const limbs = try allocator.alloc(Limb, 3 * n);
	@memset(limbs, 0);
	@memcpy(limbs[0..quarter_l], A4.limbs);
	@memcpy(limbs[quarter_l..quarter_l + R_1.limbs.len], R_1.limbs);

	var AL = Const { .positive = true, .limbs = limbs };
	// needed for the order
	AL.limbs = AL.limbs[0..div.llnormalize(AL.limbs)];
	const Q2: Const, const R: Const = try D_3n_2n(allocator, AL, B);
	if(false) {
		var q = try Managed.init(allocator);
		var r = try Managed.init(allocator);
		try q.divFloor(&r, &(try AL.toManaged(allocator)), B);
		std.debug.assert(q.toConst().eql(Q2));
		std.debug.assert(r.toConst().eql(R));
	}

	const Q_limbs = try allocator.alloc(Limb, n);
	@memset(Q_limbs, 0);
	@memcpy(Q_limbs[0..Q2.limbs.len], Q2.limbs[0..Q2.limbs.len]);
	std.debug.print("l: {} ({}) {} ({}), {} {}\n", .{Q1.limbs.len, div.llnormalize(Q1.limbs), Q2.limbs.len, div.llnormalize(Q2.limbs), n, k});
	@memcpy(Q_limbs[k..k + Q1.limbs.len], Q1.limbs);

	return .{
		Const { .positive = true, .limbs = Q_limbs[0..div.llnormalize(Q_limbs)] },
		R,
	};
}


pub fn D_3n_2n(allocator: std.mem.Allocator, A: Const, B: *Managed) D_error!struct { Const, Const } {
	std.debug.assert(B.len() % 2 == 0);
	const n = B.len() / 2;
	{
		// preconditions
		// β^2n / 2 <= B < β^2n
		std.debug.assert(B.limbs[B.len() - 1] >> (@bitSizeOf(Limb) - 1) == 1); // ensure B is normalized

		try B.shiftLeft(B, n * limb_bits);
		std.debug.assert(B.toConst().order(A) == .gt); // A < β^n * B
		try B.shiftRight(B, n * limb_bits);
	}
	const A1 = Const { .positive = true, .limbs = A.limbs[2 * n..A.limbs.len] };
	const A2 = Const { .positive = true, .limbs = A.limbs[n..2*n] };
	const A3 = Const { .positive = true, .limbs = A.limbs[0..n] };

	const B1 = Const { .positive = true, .limbs = B.limbs[n..B.len()] };
	const B2 = Const { .positive = true, .limbs = B.limbs[0..n] };
	{
		const limbs = try allocator.alloc(Limb, n + 1);
		@memset(limbs, 0);
		limbs[n] = 1;
		const B_n = Const { .positive = true, .limbs = limbs };
		for(&[_]Const {A1, A2, A3, B1, B2}) |x| {
			std.debug.assert(B_n.order(x) == .gt);
		}
	}

	const AH = Const { .positive = true, .limbs = A.limbs[n..] };
	const Q_: Const, const R1: Const = blk: {
		if(A1.order(B1) == .lt) {
			var B1_ = try B1.toManaged(allocator);
			const Q_: Const, const R1: Const = try D_2n_1n(allocator, AH, &B1_);
			break :blk .{ Q_, R1 };
		} else {
			const Q_limbs = try allocator.alloc(Limb, n);
			@memset(Q_limbs, 0);
			Q_limbs[n - 1] = std.math.maxInt(Limb);
			const Q_ = Const { .positive = true, .limbs = Q_limbs };
			
			var R1 = try AH.toManaged(allocator);
			var B1_ = try B1.toManaged(allocator);
			try R1.add(&R1, &B1_);
			try B1_.shiftLeft(&B1_, n * limb_bits);
			try R1.sub(&R1, &B1_);
			break :blk .{ Q_, R1.toConst() };
		}
	};

	var Q__ = try Q_.toManaged(allocator);

	const D = try (try mul(allocator, Q_, B2)).toManaged(allocator);
	var R_ = try R1.toManaged(allocator);
	try R_.shiftLeft(&R_, n * limb_bits);
	try R_.add(&R_, &(try A3.toManaged(allocator)));
	try R_.sub(&R_, &D);

	const zero = Const { .positive = true, .limbs = &[_]Limb {0} };
	std.debug.assert(zero.eqlZero());
	while(R_.toConst().order(zero) == .lt) {
		try R_.add(&R_, B);
		try Q__.addScalar(&Q__, -1);
	}
	return .{ Q__.toConst(), R_.toConst() };
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
		const Q, const R = try D_2n_1n(allocator, Z, B);
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


