const std = @import("std");
const Allocator = std.mem.Allocator;
const big = std.math.big;
const Managed = big.int.Managed;
const Const = big.int.Const;
const Limb = big.Limb;
const DoubleLimb = big.DoubleLimb;

const limb_bit_size = @bitSizeOf(Limb);
const limb_size = @sizeOf(Limb);

const debug = @import("main.zig").debug;


pub const Result = struct {
	q: Managed,
	r: Managed
};


fn _unbalanced_division(allocator: Allocator, a: *Managed, b: *Managed) !Result {
	var Q = try Managed.init(allocator);
	var A_ = try Managed.init(allocator);
	const n = b.len();
	var m = a.len() - n;
	while(m > n) {
		try A_.shiftRight(a, (m - n) * limb_bit_size);
		var res = try _recursive_div_rem(allocator, &A_, b);
		try Q.shiftLeft(&Q, n * limb_bit_size);
		try Q.add(&Q, &res.q);

		try res.r.shiftLeft(&res.r, (m - n) * limb_bit_size);
		try a.truncate(a, .unsigned, (m - n) * limb_bit_size);
		try a.add(a, &res.r);

		m -= n;
	}
	var res = try _recursive_div_rem(allocator, a, b);
	try Q.shiftLeft(&Q, m * limb_bit_size);
	try Q.add(&Q, &res.q);
	
	return Result {
		.q = Q,
		.r = res.r
	};
}

pub fn unbalanced_division(allocator: Allocator, a: *Managed, b: *Managed) !Result {
	const k = get_normalize_k(b.toConst());
	var a1 = try a.clone();
	var b1 = try b.clone();
	try a1.shiftLeft(a, k);
	try b1.shiftLeft(b, k);

	var res = try _unbalanced_division(allocator, &a1, &b1);
	try res.r.shiftRight(&res.r, k);
	return res;
}


const T = 200;

fn _recursive_div_rem(allocator: Allocator, a__: *Managed, b__: *Managed) !Result {
	var a_ = try a__.clone();
	var b_ = try b__.clone();
	var a = &a_;
	var b = &b_;
	if(b.order(a.*) == .gt) return Result {
		.q = try Managed.initSet(allocator, 0),
		.r = try a.clone()
	};
	if(a.eql(b.*)) return Result {
		.q = try Managed.initSet(allocator, 1),
		.r = try Managed.initSet(allocator, 0)
	};

	const n = b.len();
	const m = a.len() - n;
	std.debug.assert(n >= m);

	if(m < T) {
		return _basecase_div_rem(allocator, a, b);
	}

	const k = m / 2;
	var B0 = try Managed.init(allocator);
	var B1 = try Managed.init(allocator);
	defer B0.deinit();
	defer B1.deinit();

	try B0.truncate(b, .unsigned, k * limb_bit_size);
	try B1.shiftRight(b, k * limb_bit_size);

	var A0 = try Managed.init(allocator);
	try A0.truncate(a, .unsigned, 2 * k * limb_bit_size);

	var A_rec_1 = try Managed.init(allocator);
	defer A_rec_1.deinit();
	try A_rec_1.shiftRight(a, 2 * k * limb_bit_size);

	const res1 = try _recursive_div_rem(allocator, &A_rec_1, &B1);
	var Q1 = res1.q;
	var A_ = res1.r;
	var Q1B0 = try Q1.clone();
	try Q1B0.mul(&Q1B0, &B0);
	try Q1B0.shiftLeft(&Q1B0, k * limb_bit_size);

	try A_.shiftLeft(&A_, 2 * k * limb_bit_size);
	try A_.add(&A_, &A0);
	try A_.sub(&A_, &Q1B0);

	try b.shiftLeft(b, k * limb_bit_size);
	while(!A_.isPositive()) {
		try Q1.addScalar(&Q1, -1);
		try A_.add(&A_, b);
	}
	try b.shiftRight(b, k * limb_bit_size);


	var A_rec_0 = try Managed.init(allocator);
	defer A_rec_0.deinit();
	try A_rec_0.shiftRight(&A_, k * limb_bit_size);

	const res0 = try _recursive_div_rem(allocator, &A_rec_0, &B1);
	var Q0 = res0.q;
	var A__ = res0.r;
	var Q0B0 = try Q0.clone();
	try Q0B0.mul(&Q0B0, &B0);

	try A_.truncate(&A_, .unsigned, k * limb_bit_size);

	try A__.shiftLeft(&A__, k * limb_bit_size);
	try A__.add(&A__, &A_);
	try A__.sub(&A__, &Q0B0);

	while(!A__.isPositive()) {
		try Q0.addScalar(&Q0, -1);
		try A__.add(&A__, b);
	}
	
	try Q1.shiftLeft(&Q1, k * limb_bit_size);
	try Q1.add(&Q1, &Q0);
	return Result {
		.q = Q1,
		.r = A__
	};
}

pub fn recursive_div_rem(allocator: Allocator, a: *Managed, b: *Managed) !Result {
	std.debug.assert(b.len() >= a.len() - b.len());

	const k = get_normalize_k(b.toConst());
	var a1 = try a.clone();
	var b1 = try b.clone();
	try a1.shiftLeft(a, k);
	try b1.shiftLeft(b, k);

	var res = try _recursive_div_rem(allocator, &a1, &b1);
	try res.r.shiftRight(&res.r, k);
	return res;
}

// TODO: SvobodaDivision ?
noinline fn _basecase_div_rem(allocator: Allocator, a: *Managed, b: *Managed) !Result {
	// std.debug.print("a: {}, b: {}, diff: {}\n", .{a.len(), b.len(), @as(isize, @intCast(a.len())) - @as(isize, @intCast(b.len()))});
	if(b.order(a.*) == .gt) {
		return Result {
			.q = try Managed.initSet(allocator, 0),
			.r = try a.clone()
		};
	}
	if(a.eql(b.*)) {
		return Result {
			.q = try Managed.initSet(allocator, 1),
			.r = try Managed.initSet(allocator, 0)
		};
	}

	std.debug.assert(get_normalize_k(b.toConst()) == 0);
	std.debug.assert(!a.eql(b.*));
	std.debug.assert(b.order(a.*) != .gt);

	const n = b.len();
	const m = a.len() - n;
	var Q_limbs = try allocator.alloc(Limb, m + 1);
	defer allocator.free(Q_limbs);

	try b.shiftLeft(b, m * limb_bit_size);
	if(a.order(b.*) != .lt) {
		Q_limbs[m] = 1;
		try a.sub(a, b);
	} else {
		Q_limbs = try allocator.realloc(Q_limbs, m);
	}
	try b.shiftRight(b, limb_bit_size);

	const limbs = try allocator.alloc(Limb, b.len() + m);
	defer allocator.free(limbs);

	for(0..m) |i| {
		const j = m-1 - i;

		// const Q_limb_j = ((@as(DoubleLimb, a.limbs[n + j]) << limb_bit_size) + @as(DoubleLimb, a.limbs[n + j - 1])) / @as(DoubleLimb, b.limbs[n-1]);
		const TripleLimb = std.meta.Int(.unsigned, 3 * limb_bit_size);
		const Q_limb_j = ((@as(TripleLimb, a.limbs[n + j]) << (2*limb_bit_size)) + (@as(TripleLimb, a.limbs[n + j - 1]) << limb_bit_size) + @as(TripleLimb, a.limbs[n + j - 2])) / 
			((@as(DoubleLimb, b.limbs[n-1]) << limb_bit_size) + @as(TripleLimb, b.limbs[n - 2]));
		const qj = @as(Limb, @min(Q_limb_j, std.math.maxInt(Limb)));
		Q_limbs[j] = qj;

		if(qj != 0) {
			var len: usize = 1;
			var carry: DoubleLimb = 0;
			for(0..b.len()) |k| {
				const r = @as(DoubleLimb, b.limbs[k]) * @as(DoubleLimb, qj) + carry;
				limbs[k] = @truncate(r);
				if(limbs[k] != 0) 
					len = k + 1;
				carry = r >> limb_bit_size;
			}
			limbs[b.len()] = @truncate(carry);
			if(carry != 0) 
				len = b.len() + 1;

			const qBj = Managed {
				.allocator = allocator,
				.limbs = limbs,
				.metadata = len
			};

			// TODO: replace a.sub
			try a.sub(a, &qBj);
		}

		while(!a.isPositive()) {
			Q_limbs[j] -= 1;
			try a.add(a, b);
		}

		try b.shiftRight(b, limb_bit_size);
	}
	
	const Q = Const {
		.limbs = Q_limbs,
		// TODO
		.positive = true
	};
	return Result {
		.q = try Q.toManaged(allocator),
		.r = try a.clone()
	};
}
pub fn basecase_div_rem(allocator: Allocator, a: *Managed, b: *Managed) !Result {
	const k = get_normalize_k(b.toConst());
	var a1 = try a.clone();
	var b1 = try b.clone();
	try a1.shiftLeft(a, k);
	try b1.shiftLeft(b, k);

	var res = try _basecase_div_rem(allocator, &a1, &b1);
	try res.r.shiftRight(&res.r, k);
	return res;
}

fn get_normalize_k(a: Const) usize {
	if(a.eqlZero()) @panic("trying to normalize 0");
	return @clz(a.limbs[a.limbs.len - 1]);
}
