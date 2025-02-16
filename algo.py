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


def subquadratic(a, b, n = 0):
    if a < b:
        return chars[a]
    # k = math.ceil(math.log(a, b) / 2)
    k = math.floor(math.log(a, b) / 2) + 1
    print(" " * n + str(k) + "   " + str(a))
    """
    # print(a, b, k, math.log(a, b)/2, (a.bit_length()) * math.log(2, b)/2)
    N = a.bit_length() - 1
    lk = math.floor(N * math.log(2, b)/2) + 1
    lk2 = N * math.log(2, b)/2
    hk = math.ceil((N+1) * math.log(2, b)/2)
    if hk - lk > 0:
        print(math.log(a, b) /2)
        print(k)
        print(lk2, lk, hk)
        k1 = lk
        # print(a, b ** (2*(k1-1)), b**(2*k1))
        print(a, b ** k1)
        print()
    """
    # assert b ** (2*k1 - 2) <= a < b ** (2*k1)
    # assert b ** (2*k2 - 2) <= a < b ** (2*k2)
    assert b ** (2*k - 2) <= a < b ** (2*k)
    q = a // (b ** k)
    R = a % (b ** k)
    r = subquadratic(R, b, n+1)
    return subquadratic(q, b, n+1) + "0" * (k - len(r)) + r


print(subquadratic(1 << 10000, 10))
"""
# print(subquadratic_div_free(1000, 10, 3))
import time
A = 100000000000000000000000000000000000000000000000000000000000000000000000000000000
dA = 200000

t = time.monotonic()
for i in range(A, A + dA):
    subquadratic_div_free(i, 10, 20)
print(time.monotonic() - t)

t = time.monotonic()
for i in range(A, A + dA):
    naive(i, 10)
print(time.monotonic() - t)
"""
