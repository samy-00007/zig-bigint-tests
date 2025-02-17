import math
chars = "0123456789ABCDEF"
# https://inria.hal.science/file/index/docid/864293/filename/get_str.pdf


def naive(n, b):
    assert b <= 16
    string = ""
    while n > 0:
        string += chars[n % b]
        n //= b
    return string[::-1]


def div_free_naive(a, b, k):
    assert a < b**k

    def convert_naive(y, k, n):
        string = ""
        for i in range(1, k + 1):
            t = b * y
            string += chars[t // (2**n)]
            y = t % (2**n)
        return string
    n = (2 * (b ** k)).bit_length()
    y = ((a + 1) * (2**n)) // (b**k) - 1
    return convert_naive(y, k, n)


def div_free_naive_trunc(a, b, k):
    assert a < b**k

    def convert_trunc(y, k, n):
        alpha = math.log2(b)
        string = ""
        for i in range(1, k + 1):
            ni = n - math.floor(i * alpha)
            ni_1 = n - math.floor((i-1) * alpha)
            t = b * y
            string += chars[t // (2**ni_1)]
            z = t % 2**ni_1
            y = z >> (ni_1 - ni)
        return string

    n = (2 * k * (b**k)).bit_length()
    y = ((a+1) * (2**n)) // (b**k) - 1
    return convert_trunc(y, k, n)


def subquadratic_div_free(a, b, kt):
    assert kt > 2

    def convert_trunc(y, k, n):
        alpha = math.log2(b)
        string = []
        for i in range(1, k + 1):
            ni = n - math.floor(i * alpha)
            ni_1 = n - math.floor((i-1) * alpha)
            t = b * y
            string.append(t // (2**ni_1))
            z = t % 2**ni_1
            y = z >> (ni_1 - ni)
        return string

    def convert_rec(k, y, n, g):
        if k <= kt:
            return convert_trunc(y, k, n)

        kh = (k + 1) // 2
        kl = k - kh + 1
        nh = (4 * g * (b ** kh)).bit_length()
        nl = (4 * g * (b ** kl)).bit_length()
        yh = math.floor(y * 2**(nh-n))
        yl = ((y*b**(k-kl)) % (2**n)) >> (n-nl)
        sh = convert_rec(kh, yh, nh, g)
        sl = convert_rec(kl, yl, nl, g)

        if sh[-1] == b-1 and sl[0] == 0:
            # add 1 mod b^kh
            carry = 1
            for i in range(len(sh) - 1, -1, -1):
                s = sh[i] + carry
                sh[i] = s % b
                carry = s // b
        if sh[-1] == 0 and sl[0] == b-1:
            sl = [0] * kl
        return sh[0:-1] + sl

    # if a is a power of b, b ** k == a, but we want a < b ** k
    # ceil is required because of float imprecision
    k = math.ceil(math.log(a, b)) + 1
    #todo: does it matter ?
    g = max(kt, math.ceil(math.log2((k-3)/(kt-3)))) if k > 3 else max(math.ceil(math.log2(k)) + 1, kt)
    # g = max(kt, math.ceil(math.log2((k - 3) / (kt - 3))))
    n = (4 * g * b**k).bit_length()
    y = ((a+1) * 2**n) // (b**k) - 1

    res = convert_rec(k, y, n, g)
    for i, x in enumerate(res):
        if x != 0:
            res = res[i:]
            break
    return "".join(map(lambda x: chars[x], res))


def subquadratic(a, b, n=0, s=""):
    if a < b:
        # print(s)
        # print()
        print("prof: " + str(n))
        return chars[a]
    k = math.floor(math.log(a, b) / 2) + 1

    # print(" " * n + str(k) + "   " + str(a))

    assert b ** (2*k - 2) <= a < b ** (2*k)
    q = a // (b ** k)
    R = a % (b ** k)
    r = subquadratic(R, b, n+1, "(" + s + ") % 10^" + str(k))
    return subquadratic(q, b, n+1, "(" + s + ") // 10^" + str(k)) + "0" * (k - len(r)) + r


"""
print(subquadratic(1 << 10000, 10, s="1 << 10000"))
n_digits = math.floor(math.log(1 << 10000, 10)) + 1
print(math.log(n_digits, 2))
"""


limb_len = 64
Limb = 2**limb_len


# return A > B
def gt(A, B):
    if len(A) != len(B):
        return len(A) > len(B)
    for x, y in reversed(list(zip(A, B))):
        if y >= x:
            return False
    return True


def eq(A, B):
    if len(A) != len(B):
        return False
    for x, y in zip(A, B):
        if x != y:
            return False
    return True


def gte(A, B):
    return eq(A, B) or gt(A, B)


# return k such as B * 2^k is normalized
def get_normalize_k(A):
    last = A[-1]
    return limb_len - last.bit_length()


def shift_right(A: list[int], k):
    A = A.copy()
    limb_k = k // limb_len
    k %= limb_len
    for i in range(limb_k):
        if len(A) == 0:
            break
        A.pop(0)

    carry = 0
    for i, x in reversed(list(enumerate(A))):
        next_carry = (x << (limb_len - k)) & (2**limb_len - 1)
        A[i] = x >> k | carry
        if A[i] == 0 and i == len(A) - 1:
            A.pop(i)
        carry = next_carry
    return A


def shift_left(A: list[int], k):
    A = A.copy()
    limb_k = k // limb_len
    k %= limb_len
    for i in range(limb_k):
        A.insert(0, 0)

    carry = 0
    for i, x in enumerate(A):
        r = x << k | carry
        A[i] = r & (2**limb_len - 1)
        carry = r >> limb_len
    if carry > 0:
        A.append(carry)
    return A


def add(A, B):
    A = A.copy()
    carry = 0
    for i in range(len(A)):
        ai = A[i]
        bi = 0 if i >= len(B) else B[i]
        r = ai + bi + carry
        A[i] = r % (2**limb_len)
        carry = r // (2**limb_len)
    if carry > 0:
        A.append(carry)
    return A


def sub(A, B):
    if gt(B, A):
        d, _ = sub(B, A)
        return d, -1
    A = A.copy()
    carry = 0
    for i in range(len(A)):
        ai = A[i]
        bi = 0 if i >= len(B) else B[i]
        r = ai - bi + carry
        A[i] = r % (2**limb_len)
        carry = r // (2**limb_len)
    while len(A) > 0 and A[-1] == 0:
        A.pop(-1)
    return A, 1


def mul(A, k):
    A = A.copy()
    carry = 0
    for i in range(len(A)):
        r = A[i] * k + carry
        A[i] = r % Limb
        carry = r // Limb
    if carry != 0:
        A.append(carry)
    return A


def mult(A, B):
    C = [0] * (len(A) + len(B))
    for i, x in enumerate(B):
        C = add(C, shift_left(mul(A, x), i * limb_len))
    while len(C) > 0 and C[-1] == 0:
        C.pop(-1)
    return C




# A and B are array of 64 bits integers
def _basecase_div_rem(A, B):
    assert get_normalize_k(B) == 0

    if len(B) > len(A):
        return ([0], A)
    if eq(A, B):
        return ([1], [0])
    n = len(B)
    m = len(A) - n
    Q = [0] * (m + 1)

    B1 = shift_left(B, m * limb_len)
    if gte(A, B1):
        Q[m] = 1
        A, _ = sub(A, B1)
    else:
        Q.pop(m)

    for i in range(0, m):
        A += [0] * (m + n - len(A))
        j = m - 1 - i
        Q[j] = (A[n + j] * Limb + A[n + j - 1]) // B[n-1]
        Q[j] = min(Q[j], Limb - 1)
        Bj = shift_left(B, j * limb_len)
        qBj = mul(Bj, Q[j])
        A, signe = sub(A, qBj)
        while signe == -1 and not eq(A, [0]):
            Q[j] -= 1
            A, signe = sub(Bj, A)
    return Q, A


def basecase_div_rem(A, B):
    k = get_normalize_k(B)
    A1 = shift_left(A, k)
    B1 = shift_left(B, k)

    Q1, R1 = _basecase_div_rem(A1, B1)
    return Q1, shift_right(R1, k)


T = 2 # usually between 50 and 200
def _recursive_div_rem(A, B):
    n = len(B)
    m = len(A) - n
    print(m)
    if m < T:
        print(A, B)
        return _basecase_div_rem(A, B)
    k = m // 2
    print('A, B', A, B)
    B1 = shift_right(B, k * limb_len)
    print('B1', B1)
    print()
    B0 = B[0:k]
    Q1, R1 = _recursive_div_rem(shift_right(A, 2*k * limb_len), B1)
    print('abcd')

    A_, signe = sub(add(shift_left(R1, 2 * k * limb_len), A[0:min(len(A), 2*k)]), shift_left(mult(Q1, B0), k * limb_len))

    while signe == -1:
        Q1, _ = sub(Q1, [1])
        A_, signe = sub(shift_left(B, k * limb_len), A_)

    print(len(shift_right(A_, k * limb_len)))
    Q0, R0 = _recursive_div_rem(shift_right(A_, k * limb_len), B1)

    A__, signe = sub(add(shift_left(R0, k * limb_len), A_[0:min(len(A_), k)]), mult(Q0, B0))

    while signe == -1:
        Q0 = sub(Q0, [1])
        A__, signe = sub(B, A__)

    return add(shift_left(Q1, k * limb_len), Q0), A__

def recursive_div_rem(A, B):
    k = get_normalize_k(B)
    A1 = shift_left(A, k)
    B1 = shift_left(B, k)

    Q1, R1 = _recursive_div_rem(A1, B1)
    return Q1, shift_right(R1, k)






