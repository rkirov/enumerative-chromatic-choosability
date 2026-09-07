#!/usr/bin/env python3
"""Independent exact checker for the K_{2,26} four-list counterexample.

The computation uses the 16 fibers over colors on the two-vertex side.  It does not enumerate
the 4^28 possible functions on all vertices.
"""

from itertools import product
from math import prod


LEFT_A = (0, 1, 2, 3)
LEFT_B = (0, 1, 4, 5)
RIGHT_TYPES = (
    frozenset((0, 1, 2, 4)),
    frozenset((0, 1, 2, 5)),
    frozenset((0, 1, 3, 4)),
    frozenset((0, 1, 3, 5)),
)
MULTIPLICITIES = (6, 7, 7, 6)


def list_count(multiplicities: tuple[int, int, int, int]) -> int:
    """Count colorings by conditioning on the two colors on the small side."""
    return sum(
        prod(
            len(right_list.difference((a, b))) ** multiplicity
            for right_list, multiplicity in zip(RIGHT_TYPES, multiplicities)
        )
        for a, b in product(LEFT_A, LEFT_B)
    )


def uniform_count(n: int, k: int = 4) -> int:
    """P(K_{2,n}, k) = k(k-1)^n + k(k-1)(k-2)^n."""
    return k * (k - 1) ** n + k * (k - 1) * (k - 2) ** n


def compositions4(n: int):
    for x0 in range(n + 1):
        for x1 in range(n - x0 + 1):
            for x2 in range(n - x0 - x1 + 1):
                yield x0, x1, x2, n - x0 - x1 - x2


def best_four_type_count(n: int) -> tuple[int, tuple[int, int, int, int]]:
    return min((list_count(xs), xs) for xs in compositions4(n))


def main() -> None:
    bad = list_count(MULTIPLICITIES)
    uniform = uniform_count(26)
    fibers = [
        prod(
            len(right_list.difference((a, b))) ** multiplicity
            for right_list, multiplicity in zip(RIGHT_TYPES, MULTIPLICITIES)
        )
        for a, b in product(LEFT_A, LEFT_B)
    ]

    assert fibers == [
        2541865828329, 67108864, 13060694016, 13060694016,
        67108864, 2541865828329, 13060694016, 13060694016,
        13060694016, 13060694016, 1253826625536, 1114512556032,
        13060694016, 13060694016, 1114512556032, 1253826625536,
    ]
    assert bad == 9_925_029_789_650
    assert uniform == 10_168_268_619_684
    assert bad < uniform

    best25, mult25 = best_four_type_count(25)
    best26, mult26 = best_four_type_count(26)
    assert best25 >= uniform_count(25)
    assert best26 == bad
    assert mult26 in ((6, 7, 7, 6), (7, 6, 6, 7))

    print(f"P(K_2,26, L) = {bad}")
    print(f"P(K_2,26, 4) = {uniform}")
    print(f"strict gap      = {uniform - bad}")
    print(f"best n=25 in four-type family: {best25} at {mult25}")
    print(f"best n=26 in four-type family: {best26} at {mult26}")


if __name__ == "__main__":
    main()
