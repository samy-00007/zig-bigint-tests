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
		// var res = try _recursive_div_rem(allocator, A_.limbs[0..A_.len()], b.limbs[0..b.len()]);
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

// fn _recursive_div_rem(allocator: Allocator, a__: *Managed, b__: *Managed) !Result {
fn __recursive_div_rem(allocator: Allocator, a: []const Limb, b: []const Limb) !Result {
	// var a_ = try a__.clone();
	// var b_ = try b__.clone();
	// var a = &a_;
	// var b = &b_;
	// if(b.order(a.*) == .gt) return Result {
	// 	.q = try Managed.initSet(allocator, 0),
	// 	.r = try a.clone()
	// };
	// if(a.eql(b.*)) return Result {
	// 	.q = try Managed.initSet(allocator, 1),
	// 	.r = try Managed.initSet(allocator, 0)
	// };

	const n = b.len;
	const m = a.len - n;
	std.debug.assert(n >= m);

	if(m < T) {
		var a_ = Managed {
			.limbs = a,
			.allocator = allocator,
			.metadata = a.len
		};
		var b_ = Managed {
			.limbs = b,
			.allocator = allocator,
			.metadata = b.len
		};
		return _basecase_div_rem(allocator, &a_, &b_);
	}

	const k = m / 2;
	var B0 = try Managed.init(allocator);
	var B1 = try Managed.init(allocator);
	defer B0.deinit();
	defer B1.deinit();

	try B0.truncate(b, .unsigned, k * limb_bit_size);
	try B1.shiftRight(b, k * limb_bit_size);

	// var A0 = try Managed.init(allocator);
	// try A0.truncate(a, .unsigned, 2 * k * limb_bit_size);
	const A_mod_limbs = a.limbs[0..2*k];

	// var A_rec_1 = try Managed.init(allocator);
	// defer A_rec_1.deinit();
	// try A_rec_1.shiftRight(a, 2 * k * limb_bit_size);
	const A_rec_1_limbs = a.limbs[2*k..a.len()];

	const res1 = try _recursive_div_rem(allocator, A_rec_1_limbs, &B1);
	var Q1 = res1.q;
	var A_ = res1.r;
	var Q1B0 = try Q1.clone();
	try Q1B0.mul(&Q1B0, &B0);
	try Q1B0.shiftLeft(&Q1B0, k * limb_bit_size);

	try A_.shiftLeft(&A_, 2 * k * limb_bit_size);
	lladd(A_.limbs, A_.limbs, A_mod_limbs);
	// try A_.add(&A_, &A0);
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
		const a_limbs = a.limbs[0..a.len()];
		const b_limbs = b.limbs[0..b.len()];
		const q_limbs = try allocator.alloc(Limb, calculateLenQ(a_limbs, b_limbs));
		const res2 = try __basecase_div_rem(allocator, a, b);

		_basecase_div_rem(q_limbs, a_limbs, b_limbs);

		const q = Managed {
			.limbs = q_limbs,
			.allocator = allocator,
			.metadata = llnormalize(q_limbs)
		};
		a.normalize(a.len());

		std.debug.assert(a.eql(res2.r));
		std.debug.assert(q.eql(res2.q));
		return Result {
			.q = q,
			.r = a.*
		};
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

fn calculateLenQ(a_len: usize, b_len: usize) usize {
	return a_len - b_len + 1;
}

/// Algorithm 1.6 (BasecaseDivRem), Modern Computer Arithmetic
/// q = a / b rem r
/// at the end, r is written in a
/// a and q must be normalized after calling this function TODO: really ?
/// q.len must be at least calculateLenQ(llnormalize(a), llnormalize(b))
noinline fn _basecase_div_rem(q: []Limb, a: []Limb, b: []const Limb) void {
	{
		const order = llcmp(a, b);
		std.debug.assert(get_normalize_k_limbs(b) == 0);
		// if order is 0 or -1, we have a <= b
		// therefore this function shouldn't have been called
		std.debug.assert(order == 1);
		// TODO: useful ?
		std.debug.assert(llnormalize(a) == a.len);
		std.debug.assert(llnormalize(b) == b.len);
	}
	const n = b.len;
	const m = a.len - n;
	std.debug.assert(q.len == m + 1);

	// A >= (B << m * bits)  <=>  (A >> m*bits) >= B ????? TODO (i think yes)
	// step 1
	if(llcmp(a[m..], b) != -1) {
		q[m] = 1;
		llsuboffsetright(a, a, b, m);
	} else {
		q[m] = 0;
	}

	for(0..m) |i| {
		const j = m-1 - i;

		// TODO handle small inputs
		// const Q_limb_j = ((@as(DoubleLimb, a[n + j]) << limb_bit_size) + @as(DoubleLimb, a[n + j - 1])) / @as(DoubleLimb, b[n-1]);
		// TODO: quad limb ?
		const TripleLimb = std.meta.Int(.unsigned, 3 * limb_bit_size);
		// const Q_limb_j = ((@as(TripleLimb, a_limbs[n + j]) << (2*limb_bit_size)) + (@as(TripleLimb, a_limbs[n + j - 1]) << limb_bit_size) + @as(TripleLimb, a_limbs[n + j - 2])) /
		// 	((@as(DoubleLimb, b[n-1]) << limb_bit_size) + @as(TripleLimb, b[n - 2]));
		// see exercise 1.20
		// step 3
		const Q_limb_j = std.mem.bytesToValue(TripleLimb, a[n+j-2..n+j+1]) / std.mem.bytesToValue(DoubleLimb, b[n-2..n]);
		// step 4
		const qj = @as(Limb, @min(Q_limb_j, std.math.maxInt(Limb)));
		q[j] = qj;

		// step 5
		var a_is_negative = llmulLimbOffset(.sub, a, b, qj, j);

		while(a_is_negative) {
			q[j] -= 1;
			// step 8
			// while a is negative, it is in twos complement
			// once it becomes positive, the addition overflows
			a_is_negative = lladdcarryoffsetright(a, a, b, j) == 0;
		}
	}
}



// TODO: remove all allocations
noinline fn __basecase_div_rem(allocator: Allocator, a__: *Managed, b__: *Managed) !Result {
	var a_ = try a__.clone();
	var b_ = try b__.clone();
	var a = &a_;
	var b = &b_;
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
	try a1.shiftLeft(a, k);
	try b.shiftLeft(b, k);

	const q_limbs = try allocator.alloc(Limb, calculateLenQ(a1.len(), b.len()));

	_basecase_div_rem(q_limbs, a1.limbs[0..a1.len()], b.limbs[0..b.len()]);
	a1.normalize(a1.len());
	try a1.shiftRight(&a1, k);
	try b.shiftRight(b, k);
	const q = Managed {
		.limbs = q_limbs,
		.allocator = allocator,
		.metadata = llnormalize(q_limbs)
	};
	return Result {
		.q = q,
		.r = a1
	};
}

fn get_normalize_k(a: Const) usize {
	if(a.eqlZero()) @panic("trying to normalize 0");
	return @clz(a.limbs[a.limbs.len - 1]);
}

fn get_normalize_k_limbs(a: []const Limb) usize {
	{
		var is_zero = true;
		for(a) |x| {
			if(x != 0) {
				is_zero = false;
				break;
			}
		}
		if(is_zero) @panic("trying to normalize 0");
	}
	const len = llnormalize(a);
	return @clz(a[len - 1]);
}












/// r = (in[0] << offsets[0] * bits) op0 
fn llopoffest(r: []Limb, in: [][]const Limb, comptime ops: []const AccOp, offsets: []usize) void {
	_ = r;
	assert(in.len == ops.len + 1 and offsets.len == in.len);
	// TODO
}


/// r = (a << offset_a * limb_bits) - (b << offset_b * limb_bits)
fn llsubcarryoffset(r: []Limb, a: []const Limb, b: []const Limb, offset_a: usize, offset_b: usize) Limb {
    @setRuntimeSafety(debug_safety);
    assert(a.len != 0 and b.len != 0);
    assert(offset_a + a.len >= offset_b + b.len);
    assert(r.len >= offset_a + a.len);

	const min_offset = @min(offset_a, offset_b);

    var i: usize = 0;
    var borrow: Limb = 0;

	while (i < min_offset) : (i += 1) {
		r[i] = 0;
	}
	if(offset_a > offset_b) {
		while (i < offset_a) : (i += 1) {
			// TODO: change that
			const ov1 = @subWithOverflow(0, b[i - offset_b]);
			r[i] = ov1[0];
			const ov2 = @subWithOverflow(r[i], borrow);
			r[i] = ov2[0];
			borrow = @as(Limb, ov1[1]) + ov2[1];
		}
	} else if(offset_b > offset_a) {
		while (i < offset_b) : (i += 1) {
			r[i] = a[i - offset_a];
		}
	}
    while (i < offset_b + b.len) : (i += 1) {
        const ov1 = @subWithOverflow(a[i - offset_a], b[i - offset_b]);
        r[i] = ov1[0];
        const ov2 = @subWithOverflow(r[i], borrow);
        r[i] = ov2[0];
        borrow = @as(Limb, ov1[1]) + ov2[1];
    }

    while (i < offset_a + a.len) : (i += 1) {
        const ov = @subWithOverflow(a[i - offset_a], borrow);
        r[i] = ov[0];
        borrow = ov[1];
    }

    return borrow;
}


fn llsuboffset(r: []Limb, a: []const Limb, b: []const Limb, offset_a: usize, offset_b: usize) void {
    @setRuntimeSafety(debug_safety);
    assert(offset_a + a.len > offset_b + b.len or (offset_a + a.len == offset_b + b.len and a[a.len - 1] >= b[b.len - 1]));
    assert(llsubcarryoffset(r, a, b, offset_a, offset_b) == 0);
}










const debug_safety = false;
const assert = std.debug.assert;




fn lladdcarryoffsetright(r: []Limb, a: []const Limb, b: []const Limb, k: usize) Limb {
    @setRuntimeSafety(debug_safety);
    assert(a.len != 0 and b.len != 0);
    assert(a.len >= k + b.len);
    assert(r.len >= a.len);

    var i: usize = 0;
    var carry: Limb = 0;

	while (i < k) : (i += 1) {
		r[i] = a[i];
	}

    while (i < k + b.len) : (i += 1) {
        const ov1 = @addWithOverflow(a[i], b[i - k]);
        r[i] = ov1[0];
        const ov2 = @addWithOverflow(r[i], carry);
        r[i] = ov2[0];
        carry = @as(Limb, ov1[1]) + ov2[1];
    }

    while (i < a.len) : (i += 1) {
        const ov = @addWithOverflow(a[i], carry);
        r[i] = ov[0];
        carry = ov[1];
    }

    return carry;
}

fn lladdoffsetright(r: []Limb, a: []const Limb, b: []const Limb, k: usize) void {
    @setRuntimeSafety(debug_safety);
    assert(r.len >= a.len + 1);
    r[a.len] = lladdcarryoffsetright(r, a, b, k);
}



fn lladdcarry(r: []Limb, a: []const Limb, b: []const Limb) Limb {
    @setRuntimeSafety(debug_safety);
    assert(a.len != 0 and b.len != 0);
    assert(a.len >= b.len);
    assert(r.len >= a.len);

    var i: usize = 0;
    var carry: Limb = 0;

    while (i < b.len) : (i += 1) {
        const ov1 = @addWithOverflow(a[i], b[i]);
        r[i] = ov1[0];
        const ov2 = @addWithOverflow(r[i], carry);
        r[i] = ov2[0];
        carry = @as(Limb, ov1[1]) + ov2[1];
    }

    while (i < a.len) : (i += 1) {
        const ov = @addWithOverflow(a[i], carry);
        r[i] = ov[0];
        carry = ov[1];
    }

    return carry;
}

fn lladd(r: []Limb, a: []const Limb, b: []const Limb) void {
    @setRuntimeSafety(debug_safety);
    assert(r.len >= a.len + 1);
    r[a.len] = lladdcarry(r, a, b);
}


/// r = (a << @bitSizeOf(Limb) * k) - b
fn llsubcarryoffsetleft(r: []Limb, a: []const Limb, b: []const Limb, k: usize) Limb {
    @setRuntimeSafety(debug_safety);
    assert(a.len != 0 and b.len != 0);
    assert(k + a.len >= b.len);
    assert(r.len >= a.len);

    var i: usize = 0;
    var borrow: Limb = 0;

	while (i < k) : (i += 1) {
		// TODO: change that
        const ov1 = @subWithOverflow(0, b[i]);
        r[i] = ov1[0];
        const ov2 = @subWithOverflow(r[i], borrow);
        r[i] = ov2[0];
        borrow = @as(Limb, ov1[1]) + ov2[1];
	}
    while (i < b.len) : (i += 1) {
        const ov1 = @subWithOverflow(a[i - k], b[i]);
        r[i] = ov1[0];
        const ov2 = @subWithOverflow(r[i], borrow);
        r[i] = ov2[0];
        borrow = @as(Limb, ov1[1]) + ov2[1];
    }

    while (i < k + a.len) : (i += 1) {
        const ov = @subWithOverflow(a[i - k], borrow);
        r[i] = ov[0];
        borrow = ov[1];
    }

    return borrow;
}

/// r = (a << @bitSizeOf(Limb) * k) - b
fn llsuboffsetleft(r: []Limb, a: []const Limb, b: []const Limb, k: usize) void {
    @setRuntimeSafety(debug_safety);
    assert(a.len + k > b.len or (a.len + k == b.len and a[a.len - 1] >= b[b.len - 1]));
    assert(llsubcarryoffsetleft(r, a, b, k) == 0);
}


/// r = a - (b << @bitSizeOf(Limb) * k)
fn llsubcarryoffsetright(r: []Limb, a: []const Limb, b: []const Limb, k: usize) Limb {
    @setRuntimeSafety(debug_safety);
    assert(a.len != 0 and b.len != 0);
    assert(a.len >= k + b.len);
    assert(r.len >= a.len);

    var i: usize = 0;
    var borrow: Limb = 0;

	while (i < k) : (i += 1) {
		r[i] = a[i];
	}
    while (i < k + b.len) : (i += 1) {
        const ov1 = @subWithOverflow(a[i], b[i - k]);
        r[i] = ov1[0];
        const ov2 = @subWithOverflow(r[i], borrow);
        r[i] = ov2[0];
        borrow = @as(Limb, ov1[1]) + ov2[1];
    }

    while (i < a.len) : (i += 1) {
        const ov = @subWithOverflow(a[i], borrow);
        r[i] = ov[0];
        borrow = ov[1];
    }

    return borrow;
}

/// r = a - (b << @bitSizeOf(Limb) * k)
fn llsuboffsetright(r: []Limb, a: []const Limb, b: []const Limb, k: usize) void {
    @setRuntimeSafety(debug_safety);
    assert(a.len > k + b.len or (a.len == k + b.len and a[a.len - 1] >= b[b.len - 1]));
    assert(llsubcarryoffsetright(r, a, b, k) == 0);
}




fn llsubcarry(r: []Limb, a: []const Limb, b: []const Limb) Limb {
    @setRuntimeSafety(debug_safety);
    assert(a.len != 0 and b.len != 0);
    assert(a.len >= b.len);
    assert(r.len >= a.len);

    var i: usize = 0;
    var borrow: Limb = 0;

    while (i < b.len) : (i += 1) {
        const ov1 = @subWithOverflow(a[i], b[i]);
        r[i] = ov1[0];
        const ov2 = @subWithOverflow(r[i], borrow);
        r[i] = ov2[0];
        borrow = @as(Limb, ov1[1]) + ov2[1];
    }

    while (i < a.len) : (i += 1) {
        const ov = @subWithOverflow(a[i], borrow);
        r[i] = ov[0];
        borrow = ov[1];
    }

    return borrow;
}

fn llsub(r: []Limb, a: []const Limb, b: []const Limb) void {
    @setRuntimeSafety(debug_safety);
    assert(a.len > b.len or (a.len == b.len and a[a.len - 1] >= b[b.len - 1]));
    assert(llsubcarry(r, a, b) == 0);
}



const AccOp = enum {
    /// The computed value is added to the result.
    add,

    /// The computed value is subtracted from the result.
    sub,
};

/// acc = acc (op) (y * xi << y_offset * limb_bits)
/// The result is computed modulo `r.len`.
/// Returns whether the operation overflowed.
fn llmulLimbOffset(comptime op: AccOp, acc: []Limb, y: []const Limb, xi: Limb, y_offset: usize) bool {
    @setRuntimeSafety(debug_safety);
    if (xi == 0) {
        return false;
    }

    const split = @min(y_offset + y.len, acc.len);
    var a_lo = acc[0..split];
    var a_hi = acc[split..];

    switch (op) {
        .add => {
            var carry: Limb = 0;
            var j: usize = y_offset;
            while (j < a_lo.len) : (j += 1) {
                a_lo[j] = addMulLimbWithCarry(a_lo[j], y[j - y_offset], xi, &carry);
            }

            j = 0;
            while ((carry != 0) and (j < a_hi.len)) : (j += 1) {
                const ov = @addWithOverflow(a_hi[j], carry);
                a_hi[j] = ov[0];
                carry = ov[1];
            }

            return carry != 0;
        },
        .sub => {
            var borrow: Limb = 0;
            var j: usize = y_offset;
            while (j < a_lo.len) : (j += 1) {
                a_lo[j] = subMulLimbWithBorrow(a_lo[j], y[j - y_offset], xi, &borrow);
            }

            j = 0;
            while ((borrow != 0) and (j < a_hi.len)) : (j += 1) {
                const ov = @subWithOverflow(a_hi[j], borrow);
                a_hi[j] = ov[0];
                borrow = ov[1];
            }

            return borrow != 0;
        },
    }
}


/// a + b * c + *carry, sets carry to the overflow bits
pub fn addMulLimbWithCarry(a: Limb, b: Limb, c: Limb, carry: *Limb) Limb {
    @setRuntimeSafety(debug_safety);

    // ov1[0] = a + *carry
    const ov1 = @addWithOverflow(a, carry.*);

    // r2 = b * c
    const bc = @as(DoubleLimb, std.math.mulWide(Limb, b, c));
    const r2 = @as(Limb, @truncate(bc));
    const c2 = @as(Limb, @truncate(bc >> limb_bit_size));

    // ov2[0] = ov1[0] + r2
    const ov2 = @addWithOverflow(ov1[0], r2);

    // This never overflows, c1, c3 are either 0 or 1 and if both are 1 then
    // c2 is at least <= maxInt(Limb) - 2.
    carry.* = ov1[1] + c2 + ov2[1];

    return ov2[0];
}


/// a - b * c - *carry, sets carry to the overflow bits
fn subMulLimbWithBorrow(a: Limb, b: Limb, c: Limb, carry: *Limb) Limb {
    // ov1[0] = a - *carry
    const ov1 = @subWithOverflow(a, carry.*);

    // r2 = b * c
    const bc = @as(DoubleLimb, std.math.mulWide(Limb, b, c));
    const r2 = @as(Limb, @truncate(bc));
    const c2 = @as(Limb, @truncate(bc >> limb_bit_size));

    // ov2[0] = ov1[0] - r2
    const ov2 = @subWithOverflow(ov1[0], r2);
    carry.* = ov1[1] + c2 + ov2[1];

    return ov2[0];
}



/// Returns -1, 0, 1 if |a| < |b|, |a| == |b| or |a| > |b| respectively for limbs.
pub fn llcmp(a: []const Limb, b: []const Limb) i8 {
    @setRuntimeSafety(debug_safety);
    const a_len = llnormalize(a);
    const b_len = llnormalize(b);
    if (a_len < b_len) {
        return -1;
    }
    if (a_len > b_len) {
        return 1;
    }

    var i: usize = a_len - 1;
    while (i != 0) : (i -= 1) {
        if (a[i] != b[i]) {
            break;
        }
    }

    if (a[i] < b[i]) {
        return -1;
    } else if (a[i] > b[i]) {
        return 1;
    } else {
        return 0;
    }
}

/// returns the min length the limb could be.
fn llnormalize(a: []const Limb) usize {
    @setRuntimeSafety(debug_safety);
    var j = a.len;
    while (j > 0) : (j -= 1) {
        if (a[j - 1] != 0) {
            break;
        }
    }

    // Handle zero
    return if (j != 0) j else 1;
}
