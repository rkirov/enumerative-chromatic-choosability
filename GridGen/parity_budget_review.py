#!/usr/bin/env python3
"""Reproduce the 2026-09-23 parity-budget review without external packages.

Default: exact rational certificates for the existing sufficient inequalities.
--explore: also estimate their best threshold numerically. Numerical minima are
exploratory, not certified lower bounds. The general finite-degree ECC bridge
is not yet formalized; passing this script does not itself prove that theorem.
"""

import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import inf, prod


def parity_power(a, b, n):
    # Positive recurrence, avoiding subtraction/cancellation in the exact check.
    even, odd = 1, 0
    for _ in range(n):
        even, odd = a * even + b * odd, b * even + a * odd
    return even, odd


CERTIFICATES = [
    # Degree, proposed integer threshold, x0, even branch bound, odd branch bound.
    (3, 15, Q(3, 25), Q(10823, 10000), Q(1341, 5000)),
    (4, 20, Q(17, 200), Q(1381, 1250), Q(297, 1000)),
    (5, 26, Q(13, 200), Q(11159, 10000), Q(387, 1250)),
    (6, 32, Q(53, 1000), Q(11257, 10000), Q(1607, 5000)),
    (8, 43, Q(19, 500), Q(5659, 5000), Q(409, 1250)),
    (10, 54, Q(3, 100), Q(11403, 10000), Q(3373, 10000)),
]


def verify():
    for degree, threshold, x, even, odd in CERTIFICATES:
        assert degree >= 1 and x > 0 and even >= 1 and odd >= 0
        a, b = 1 + x * odd, x * even
        for ports in range(degree):
            branch_even, branch_odd = parity_power(a, b, ports)
            assert branch_even <= even and branch_odd <= odd
        root = parity_power(a, b, degree)[1]
        for ports in range(degree + 1):
            assert parity_power(a, b, ports)[1] <= root
        assert threshold * x * (1 - root) >= 1
        assert 2 * even * odd < 1
        print(f"EXACT PASS D={degree}, K={threshold}, x0={x}, E={even}, O={odd}; "
              f"root margin={float(threshold*x*(1-root)-1):.8f}, "
              f"edge budget={float(2*even*odd):.8f}")


def estimate(degree, x):
    even, odd = 1.0, 0.0
    for _ in range(10000):
        try:
            a, b = 1 + x * odd, x * even
            nxt_even = ((a + b)**(degree - 1) + (a - b)**(degree - 1)) / 2
            nxt_odd = ((a + b)**(degree - 1) - (a - b)**(degree - 1)) / 2
        except OverflowError:
            return inf
        if nxt_even + nxt_odd > 10:
            return inf
        error = max(abs(nxt_even - even), abs(nxt_odd - odd))
        even, odd = nxt_even, nxt_odd
        if error < 1e-13:
            break
    else:
        return inf
    a, b = 1 + x * odd, x * even
    root = ((a + b)**degree - (a - b)**degree) / 2
    if root >= 1 or 2 * even * odd >= 1:
        return inf
    return 1 / (x * (1 - root))


def explore():
    for degree in (3, 4, 5, 6, 8, 10, 20, 100, 1000):
        step = 1 / (10000 * degree)
        x = min((j * step for j in range(1000, 4000)),
                key=lambda y: estimate(degree, y))
        lo, hi = x - step, x + step
        for _ in range(50):
            a, b = (2 * lo + hi) / 3, (lo + 2 * hi) / 3
            if estimate(degree, a) < estimate(degree, b):
                hi = b
            else:
                lo = a
        x = (lo + hi) / 2
        print(f"NUMERICAL D={degree}: threshold~{estimate(degree, x):.9f}, x~{x:.12f}")


def verify_fractional_obstruction():
    """Exact certificate that dropping integrality cannot settle K_{2,25}."""
    left_a, left_b = {0, 1, 2, 3}, {0, 1, 4, 5}
    types = ({0, 1, 2, 4}, {0, 1, 2, 5}, {0, 1, 3, 4}, {0, 1, 3, 5})
    bases = Counter(prod(len(t - {a, b}) for t in types)
                    for a, b in product(left_a, left_b))
    assert bases == {81: 2, 16: 2, 36: 8, 72: 4}
    sqrt6_upper, fourth72_upper = Q(245, 100), Q(292, 100)
    assert sqrt6_upper**2 > 6 and fourth72_upper**4 > 72
    upper = (2 * 3**25 + 2 * 2**25 + 8 * 6**12 * sqrt6_upper
             + 4 * 72**6 * fourth72_upper)
    ordinary = 4 * 3**25 + 12 * 2**25
    assert upper < ordinary
    print("EXACT PASS K2,25 fractional obstruction: "
          f"certified upper ratio={float(upper/ordinary):.9f} < 1")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--explore", action="store_true")
    args = parser.parse_args()
    verify()
    verify_fractional_obstruction()
    if args.explore:
        explore()
