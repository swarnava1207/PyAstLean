"""A small numeric-toolkit showcase: `typing` annotations + a `scipy` subset, all transpiled
to Lean 4 and backed only by Mathlib (computable Float implementations)."""

from __future__ import annotations

from typing import List

from scipy import constants
from scipy.linalg import det, norm
from scipy.special import comb, erf, factorial, gamma
from scipy.stats import gmean, hmean, tmean


def variance(xs: List[float]) -> float:
    m = tmean(xs)
    total = 0.0
    for x in xs:
        total = total + (x - m) * (x - m)
    return total / len(xs)


def main():
    data: List[float] = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]

    print("=== scipy.special ===")
    print("5!        =", factorial(5))
    print("C(8,3)    =", comb(8, 3))
    print("gamma(6)  =", gamma(6.0))
    print("erf(1)    =", erf(1.0))

    print("=== scipy.constants ===")
    print("pi        =", constants.pi)
    print("golden    =", constants.golden)

    print("=== scipy.stats ===")
    print("mean      =", tmean(data))
    print("gmean     =", gmean(data))
    print("hmean     =", hmean(data))
    print("variance  =", variance(data))

    print("=== scipy.linalg ===")
    matrix: List[List[float]] = [[4.0, 3.0], [6.0, 3.0]]
    print("det       =", det(matrix))
    print("norm[3,4] =", norm([3.0, 4.0]))


if __name__ == "__main__":
    main()
