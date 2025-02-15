chars = "0123456789ABCDEF"


def naive(n, b):
    assert b <= 16
    string = ""
    while n > 0:
        string += chars[n % b]
        n //= b
    return string[::-1]


def div_free_naive(a, b, k):
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

