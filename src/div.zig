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

pub fn _unbalanced_division(q: []Limb, a: []Limb, b: []const Limb) void {
	std.debug.assert(llnormalize(a) == a.len);
	std.debug.assert(llnormalize(b) == b.len);
	const n = b.len;
	var m = a.len - n;
	while(m > n) {
		// TODO: handle the add
		_recursive_div_rem(q[m-n..m+1], a[m-n..], b);
		m -= n;
	}
	_recursive_div_rem(q[0..m], a[0..llnormalize(a)], b);
}

pub fn __unbalanced_division(allocator: Allocator, a: *Managed, b: *Managed) !Result {
	var Q = try Managed.init(allocator);
	var A_ = try Managed.init(allocator);
	const n = b.len();
	var m = a.len() - n;
	while(m > n) {
		try A_.shiftRight(a, (m - n) * limb_bit_size);

		const q_limbs = try allocator.alloc(Limb, calculateLenQ(A_.len(), b.len()));
		@memset(q_limbs, 0);
		const r = try allocator.dupe(Limb, A_.limbs[0..A_.len()]);
		defer allocator.free(r);
		defer allocator.free(q_limbs);

		_recursive_div_rem(q_limbs, r, b.limbs[0..b.len()]);
		// var res = try _recursive_div_rem(allocator, A_.limbs[0..A_.len()], b.limbs[0..b.len()]);
		try Q.shiftLeft(&Q, n * limb_bit_size);
		var res_q = try (Const {.limbs = q_limbs, .positive = true}).toManaged(allocator);
		try Q.add(&Q, &res_q);

		var res_r = try (Const { .limbs = r, .positive = true}).toManaged(allocator);
		try res_r.shiftLeft(&res_r, (m - n) * limb_bit_size);
		try a.truncate(a, .unsigned, (m - n) * limb_bit_size);
		try a.add(a, &res_r);

		m -= n;
	}
	const q_limbs = try allocator.alloc(Limb, calculateLenQ(a.len(), b.len()));
	@memset(q_limbs, 0);
	const r = try allocator.dupe(Limb, a.limbs[0..a.len()]);
	defer allocator.free(r);
	defer allocator.free(q_limbs);

	_recursive_div_rem(q_limbs, r, b.limbs[0..b.len()]);
	const res_r = try (Const { .limbs = r, .positive = true}).toManaged(allocator);
	var res_q = try (Const {.limbs = q_limbs, .positive = true}).toManaged(allocator);
	defer res_q.deinit();

	try Q.shiftLeft(&Q, m * limb_bit_size);
	try Q.add(&Q, &res_q);

	return Result {
		.q = Q,
		.r = res_r
	};
}

pub fn unbalanced_division(allocator: Allocator, a: *Managed, b: *Managed) !Result {
	const k = get_normalize_k(b.toConst());
	var a1 = try a.clone();
	try a1.shiftLeft(a, k);
	try b.shiftLeft(b, k);

	const q_limbs = try allocator.alloc(Limb, calculateLenQ(a1.len(), b.len()));
	@memset(q_limbs, 0);

	_unbalanced_division(q_limbs, a1.limbs[0..a1.len()], b.limbs[0..b.len()]);

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


const T = 200;

pub fn _recursive_div_rem(q: []Limb, a: []Limb, b: []const Limb) void {
	// TODO: needed ?
	// std.debug.assert(llnormalize(a) == a.len);
	// std.debug.assert(llnormalize(b) == b.len);
	std.debug.assert(b[b.len - 1] >> (@bitSizeOf(Limb) - 1) == 1); // b[0] >= (2^@bitSizeOf(Limb)) / 2
	{
		const order = llcmp(a, b);
		if(order == -1) {
			// a < b, r = a, q = 0
			return;	// q is already zeroes
		}
		if(order == 0) {
			// a == b, r = 0, q = 1
			@memset(a, 0);
			q[0] = 1;
			return;	// q is already zeroes
		}
	}

	const n = b.len;
	const m = a.len - n;
	std.debug.assert(n >= m);

	if(m < T) {
		_basecase_div_rem(q, a, b);
		return;
	}

	const k = m / 2;

	const B0 = b[0..llnormalize(b[0..k])];
	const B1 = b[k..];
	// TODO: k + 1 ?
	var Q0 = q[0..k];
	var Q1 = q[k..];
	var R1 = a[2*k..];
	{
		// TODO: normalize needed ?
		_recursive_div_rem(Q1, R1[0..llnormalize(R1)], B1);


		Q1 = Q1[0..llnormalize(Q1)];
		// TODO: need the better version ? (see llmulacc)
		var a_is_negative = if(Q1.len > B0.len) 
			llmulaccLongWithOverflowOffset(.sub, a, Q1, B0, k)
		else
			llmulaccLongWithOverflowOffset(.sub, a, B0, Q1, k);

		while(a_is_negative) {
			// TODO: better function
			llsub(Q1, Q1, &[_]Limb {1});
			// while a is negative, it is in twos complement
			// once it becomes positive, this add overflows
			a_is_negative = lladdcarryoffsetright(a, a, b, k) == 0;
		}
	}
	// TODO: exercise 1.20

	var R0 = a[k..];
	{
		_recursive_div_rem(Q0, R0[0..llnormalize(R0)], B1);

		// TODO: check if Q0 can overflow
		Q0 = Q0[0..llnormalize(Q0)];
		var a_is_negative = if(Q0.len > B0.len) 
			llmulaccLongWithOverflowOffset(.sub, a, Q0, B0, 0)
		else
			llmulaccLongWithOverflowOffset(.sub, a, B0, Q0, 0);

		while(a_is_negative) {
			llsub(Q0, Q0, &[_]Limb{1});
			// TODO: no offset version ?
			a_is_negative = lladdcarryoffsetright(a, a, b, 0) == 0;
		}
	}
}



pub fn recursive_div_rem(allocator: Allocator, a: *Managed, b: *Managed) !Result {
	// n >= m
	std.debug.assert(2*b.len() >= a.len());

	const k = get_normalize_k(b.toConst());
	var a1 = try a.clone();
	try a1.shiftLeft(a, k);
	try b.shiftLeft(b, k);

	const q_limbs = try allocator.alloc(Limb, calculateLenQ(a1.len(), b.len()));
	@memset(q_limbs, 0);

	_recursive_div_rem(q_limbs, a1.limbs[0..a1.len()], b.limbs[0..b.len()]);
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

pub fn calculateLenQ(a_len: usize, b_len: usize) usize {
	return a_len - b_len + 1;
}


pub fn print(comptime format: []const u8, args: anytype, depth: usize) void {
	const writer = std.io.getStdErr().writer();
	writer.writeByteNTimes(' ', depth) catch @panic("failed to print");
	writer.print(format, args) catch @panic("failed to print");
}
/// Algorithm 1.6 (BasecaseDivRem), Modern Computer Arithmetic
/// q = a / b rem r
/// at the end, r is written in a
/// a and q must be normalized after calling this function TODO: really ?
/// q.len must be at least calculateLenQ(llnormalize(a), llnormalize(b))
/// TODO: version where q is written in a directly ?
pub noinline fn _basecase_div_rem(q: []Limb, a: []Limb, b: []const Limb) void {
	const order = llcmp(a, b);
	if(order == 0) {
		// a = b
		q[0] = 1;
		@memset(a, 0);
		return;
	}
	if(order == -1) {
		// a < b
		return;
	}
	{
		std.debug.assert(get_normalize_k_limbs(b) == 0);
		// TODO: useful ?
		std.debug.assert(llnormalize(a) == a.len);
		std.debug.assert(llnormalize(b) == b.len);
	}
	const n = b.len;
	const m = a.len - n;
	std.debug.assert(q.len >= m + 1);

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
		// TODO: fix that
		const Q_limb_j = if(a.len > 3 and b.len > 1)
			std.mem.bytesToValue(TripleLimb, a[n+j-2..n+j+1]) / std.mem.bytesToValue(DoubleLimb, b[n-2..n])
			else
				std.mem.bytesToValue(DoubleLimb, a[n+j-1..n+j+1]) / b[n-1];
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

pub fn get_normalize_k(a: Const) usize {
	if(a.eqlZero()) @panic("trying to normalize 0");
	return @clz(a.limbs[a.limbs.len - 1]);
}

pub fn get_normalize_k_limbs(a: []const Limb) usize {
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







/// r = r (op) a * b << offset * bits
noinline fn llmulaccLongWithOverflowOffset(comptime op: AccOp, r: []Limb, a: []const Limb, b: []const Limb, offset: usize) bool {
    @setRuntimeSafety(debug_safety);
	// std.debug.print("{} {}\n", .{a.len, llnormalize(a)});
    assert(r.len >= a.len);
    assert(a.len >= b.len);

    var i: usize = 0;
	// TODO: does it work ?
	var has_overflowed = false;
    while (i < b.len) : (i += 1) {
        if(llmulLimbOffset(op, r[i..], a, b[i], offset))
			has_overflowed = true;
    }
	return has_overflowed;
}




/// r = (in[0] << offsets[0] * bits) op0 
pub fn llopoffest(r: []Limb, in: [][]const Limb, comptime ops: []const AccOp, offsets: []usize) void {
	_ = r;
	assert(in.len == ops.len + 1 and offsets.len == in.len);
	// TODO
}


/// r = (a << offset_a * limb_bits) - (b << offset_b * limb_bits)
pub fn llsubcarryoffset(r: []Limb, a: []const Limb, b: []const Limb, offset_a: usize, offset_b: usize) Limb {
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


pub fn llsuboffset(r: []Limb, a: []const Limb, b: []const Limb, offset_a: usize, offset_b: usize) void {
    @setRuntimeSafety(debug_safety);
    assert(offset_a + a.len > offset_b + b.len or (offset_a + a.len == offset_b + b.len and a[a.len - 1] >= b[b.len - 1]));
    assert(llsubcarryoffset(r, a, b, offset_a, offset_b) == 0);
}










const debug_safety = false;
const assert = std.debug.assert;




noinline fn lladdcarryoffsetright(r: []Limb, a: []const Limb, b: []const Limb, k: usize) Limb {
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

pub fn lladdoffsetright(r: []Limb, a: []const Limb, b: []const Limb, k: usize) void {
    @setRuntimeSafety(debug_safety);
    assert(r.len >= a.len + 1);
    r[a.len] = lladdcarryoffsetright(r, a, b, k);
}



pub fn lladdcarry(r: []Limb, a: []const Limb, b: []const Limb) Limb {
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

pub fn lladd(r: []Limb, a: []const Limb, b: []const Limb) void {
    @setRuntimeSafety(debug_safety);
    assert(r.len >= a.len + 1);
    r[a.len] = lladdcarry(r, a, b);
}


/// r = (a << @bitSizeOf(Limb) * k) - b
pub fn llsubcarryoffsetleft(r: []Limb, a: []const Limb, b: []const Limb, k: usize) Limb {
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
pub fn llsuboffsetleft(r: []Limb, a: []const Limb, b: []const Limb, k: usize) void {
    @setRuntimeSafety(debug_safety);
    assert(a.len + k > b.len or (a.len + k == b.len and a[a.len - 1] >= b[b.len - 1]));
    assert(llsubcarryoffsetleft(r, a, b, k) == 0);
}


/// r = a - (b << @bitSizeOf(Limb) * k)
pub fn llsubcarryoffsetright(r: []Limb, a: []const Limb, b: []const Limb, k: usize) Limb {
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
pub fn llsuboffsetright(r: []Limb, a: []const Limb, b: []const Limb, k: usize) void {
    @setRuntimeSafety(debug_safety);
    assert(a.len > k + b.len or (a.len == k + b.len and a[a.len - 1] >= b[b.len - 1]));
    assert(llsubcarryoffsetright(r, a, b, k) == 0);
}




pub fn llsubcarry(r: []Limb, a: []const Limb, b: []const Limb) Limb {
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

pub fn llsub(r: []Limb, a: []const Limb, b: []const Limb) void {
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
pub fn llmulLimbOffset(comptime op: AccOp, acc: []Limb, y: []const Limb, xi: Limb, y_offset: usize) bool {
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
pub fn subMulLimbWithBorrow(a: Limb, b: Limb, c: Limb, carry: *Limb) Limb {
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
pub noinline fn llcmp(a: []const Limb, b: []const Limb) i8 {
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
pub fn llnormalize(a: []const Limb) usize {
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
