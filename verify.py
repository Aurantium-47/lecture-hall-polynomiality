#!/usr/bin/env python3
"""Finite exact checks accompanying the Lecture Hall polynomiality proof.

Run with Python 3.8+ and SymPy. This script uses no floating-point arithmetic
or network access. The checks support, but do not replace, the proof for all
indices. The results are written to verification.json beside this script.
"""

import json
import sys
from math import comb
from pathlib import Path

import sympy
from sympy.polys.domains import ZZ
from sympy.polys.rings import ring


def alpha_sign(height):
    return -1 if height >= 4 and height % 2 == 0 else 1


def dyck_moments(alpha, nmax, zero, one):
    """Weighted Dyck paths: down-steps from height h have weight alpha[h]."""
    states = {0: one}
    moments = [one]
    for step in range(1, 2 * nmax + 1):
        next_states = {}
        remaining = 2 * nmax - step
        for height, weight in states.items():
            # Paths too high to return by the final step can be discarded.
            if height + 1 <= remaining:
                next_states[height + 1] = next_states.get(height + 1, zero) + weight
            if height:
                next_states[height - 1] = (
                    next_states.get(height - 1, zero) + weight * alpha[height]
                )
        states = next_states
        if step % 2 == 0:
            moments.append(states.get(0, zero))
    return moments


def determinant(matrix, zero, one):
    """Bareiss elimination with row pivoting and checked exact divisions."""
    if not matrix:
        return one
    a = [row[:] for row in matrix]
    previous, sign = one, 1
    for k in range(len(a) - 1):
        if a[k][k] == zero:
            pivot_row = next((r for r in range(k + 1, len(a)) if a[r][k] != zero), None)
            if pivot_row is None:
                return zero
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, len(a)):
            for j in range(k + 1, len(a)):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                quotient, remainder = divmod(numerator, previous)
                if remainder != zero:
                    raise ArithmeticError("Non-exact Bareiss division")
                a[i][j] = quotient
        for i in range(k + 1, len(a)):
            a[i][k] = zero
        previous = pivot
    return sign * a[-1][-1]


def toeplitz_equation(ell, index, zero, one):
    """E_i: rows 1..ceil(i/2), columns floor(i/2)+1..i; see the paper."""
    rows = range(1, (index + 1) // 2 + 1)
    columns = range(index // 2 + 1, index + 1)
    return -determinant([[-ell[c - r + 1] for c in columns] for r in rows], zero, one)


def target(y, index, one):
    result = one
    for j in range(1, index + 1):
        result *= y[j] ** (index + 1 - j)
    return result


def check_equations(y, zero, one):
    nmax = len(y) - 1
    alpha = [zero] + [alpha_sign(k) * y[k] * y[k + 1] for k in range(1, nmax)]
    ell = [zero] + [y[1] * mu for mu in dyck_moments(alpha, nmax - 1, zero, one)]
    for i in range(1, nmax + 1):
        if toeplitz_equation(ell, i, zero, one) != target(y, i, one):
            raise AssertionError("Toeplitz identity failed at index {}".format(i))
    return ell


def compositions(n):
    if n == 0:
        yield ()
    else:
        for first in range(1, n + 1):
            for rest in compositions(n - first):
                yield (first,) + rest


def check_compositions(nmax):
    """Compare a separate depth-profile formula against Dyck path dynamics."""
    R, *generators = ring(",".join("y{}".format(i) for i in range(1, nmax + 2)), ZZ)
    y = [R.zero] + generators
    alpha = [R.zero] + [alpha_sign(k) * y[k] * y[k + 1] for k in range(1, nmax + 1)]
    moments = dyck_moments(alpha, nmax, R.zero, R.one)
    counts = []
    for n in range(1, nmax + 1):
        total = R.zero
        for profile in compositions(n):
            coefficient = 1
            for j in range(len(profile) - 1):
                coefficient *= comb(profile[j] + profile[j + 1] - 1, profile[j + 1])
            term = R(coefficient)
            for height, multiplicity in enumerate(profile, 1):
                term *= alpha[height] ** multiplicity
            total += term
        if total != moments[n]:
            raise AssertionError("Composition formula failed at mu_{}".format(n))
        if len(total) != 2 ** (n - 1):
            raise AssertionError("Monomial count failed at mu_{}".format(n))
        counts.append(len(total))
    return {
        "max_mu_index": nmax,
        "max_ell_index": nmax + 1,
        "all_coefficients_agree": True,
        "monomial_counts_mu_1_onward": counts,
    }


def main():
    R, *generators = ring(",".join("y{}".format(i) for i in range(1, 11)), ZZ)
    ell = check_equations([R.zero] + generators, R.zero, R.one)
    result = {
        "scope": "Finite exact checks; the paper supplies the proof for all indices.",
        "environment": {"python": sys.version.split()[0], "sympy": sympy.__version__},
        "symbolic": {
            "max_index": 10,
            "equations_checked": 10,
            "all_toeplitz_equations_passed": True,
            "monomial_counts_ell_1_onward": [len(p) for p in ell[1:]],
            "first_five": [str(p) for p in ell[1:6]],
        },
    }
    integer_cases = [
        ("all_one", "y_j = 1", [1] * 40),
        ("increasing", "y_j = j", list(range(1, 41))),
        ("alternating_signed", "y_j = (-1)^j * (j mod 5 + 1)",
         [(-1) ** j * (j % 5 + 1) for j in range(1, 41)]),
    ]
    for name, formula, values in integer_cases:
        check_equations([0] + values, 0, 1)
    result["integer"] = {
        "max_index": 40,
        "cases": [{"name": name, "formula": formula} for name, formula, _ in integer_cases],
        "equations_checked": 120,
        "all_toeplitz_equations_passed": True,
    }
    result["composition"] = check_compositions(12)
    serialized = json.dumps(result, indent=2) + "\n"
    Path(__file__).with_name("verification.json").write_text(serialized, encoding="utf-8")
    print(serialized, end="")


if __name__ == "__main__":
    main()
