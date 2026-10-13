#!/usr/bin/env python3
"""Exact finite checks for the Lecture Hall SAGBI extension.

Python 3.10+; SymPy 1.14.0 was used for the recorded run. No network or
floating-point arithmetic is used. Defaults reproduce the packaged JSON data.
The symbolic checks construct Dyck moments and expand the original Toeplitz
minors; they do NOT use the Schur leading-term theorem to compute the minors.
The tests are evidence and debugging aids, not a substitute for the proof.

Run: python code/verify_extensions.py --output-dir regenerated
Then: python code/compare_data.py data regenerated
"""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
from collections import Counter
from itertools import combinations
from pathlib import Path

import sympy
from sympy.polys.domains import ZZ
from sympy.polys.rings import ring


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def alpha_sign(h: int) -> int:
    return -1 if h >= 4 and h % 2 == 0 else 1


def conjugate(lam: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sum(x >= j for x in lam) for j in range(1, max(lam, default=0) + 1))


def partition_for_subset(S: tuple[int, ...]) -> tuple[int, ...]:
    r = len(S)
    return tuple(s - r + j for j, s in enumerate(reversed(S), 1))


def peeling_profile(lam: tuple[int, ...]) -> tuple[int, ...]:
    result = []
    while lam:
        result.append(lam[0])
        lam = conjugate(lam[1:])
    return tuple(result)


def frobenius_profile(lam: tuple[int, ...]) -> tuple[int, ...]:
    lc = conjugate(lam)
    result = []
    for i in range(1, min(len(lam), len(lc)) + 1):
        if lam[i - 1] < i:
            break
        result.extend((lam[i - 1] - i + 1, lc[i - 1] - i))
    while result and result[-1] == 0:
        result.pop()
    return tuple(result)


def predicted_exponent(S: tuple[int, ...], n: int) -> tuple[int, ...]:
    if not S:
        return (1,) + (0,) * (n - 1)
    d = frobenius_profile(partition_for_subset(S)) + (0,) * n
    return (len(S) + d[0],) + tuple(d[j - 1] + d[j] for j in range(1, n))


def inverse_exponent(e: tuple[int, ...]) -> tuple[int, ...]:
    """Inverse of the theorem's bijection, using alternating tails/Frobenius data."""
    e = tuple(e)
    while e and e[-1] == 0:
        e = e[:-1]
    if e == (1,):
        return ()
    require(len(e) >= 2 and e[0] == e[1] + 1, f"Not a Hilbert vector: {e}")
    require(all(e[i] > e[i + 1] for i in range(1, len(e) - 1)), str(e))
    d = tuple(sum((-1) ** (j - i - 1) * e[j] for j in range(i + 1, len(e)))
              for i in range(len(e) - 1))
    A = tuple(d[j] - 1 for j in range(0, len(d), 2))
    B = tuple(d[j] if j < len(d) else 0 for j in range(1, len(d) + 1, 2))
    D = len(A)
    r = B[0] + 1
    lam = tuple(A[i - 1] + i if i <= D else
                sum(j + B[j - 1] >= i for j in range(1, D + 1))
                for i in range(1, r + 1))
    return tuple(sorted(lam[i - 1] + r - i for i in range(1, r + 1)))


def is_lecture_hall(e: tuple[int, ...]) -> bool:
    n = len(e)
    return all(x >= 0 for x in e) and all(
        (n - i - 1) * e[i] >= (n - i) * e[i + 1] for i in range(n - 1))


def is_hilbert(e: tuple[int, ...]) -> bool:
    if not e or e[0] - (e[1] if len(e) > 1 else 0) != 1:
        return False
    return is_lecture_hall(e)


def layer_decomposition(e: tuple[int, ...]) -> list[tuple[int, ...]]:
    """The proof's direct Hilbert-basis decomposition (not used to enumerate)."""
    n = len(e)
    if n == 1:
        return [(1,)] * e[0]
    g = e[0] - e[1]
    result = []
    for t in range(g):
        tail = tuple(min(n - i, max(0, e[i] - t * (n - i))) for i in range(1, n))
        result.append((tail[0] + 1,) + tail)
    return result


def dyck_moments(alpha, max_n: int, zero, one):
    """Independent step-by-step enumeration; alpha is indexed from 1."""
    states = {0: one}
    answer = [one]
    for step in range(1, 2 * max_n + 1):
        after = {}
        remaining = 2 * max_n - step
        for h, value in states.items():
            if h + 1 <= remaining:
                after[h + 1] = after.get(h + 1, zero) + value
            if h:
                after[h - 1] = after.get(h - 1, zero) + value * alpha[h]
        states = after
        if step % 2 == 0:
            answer.append(states.get(0, zero))
    return answer


def bareiss(matrix, zero, one):
    """Exact determinant, with row pivoting and checked divisions."""
    if not matrix:
        return one
    a = [list(row) for row in matrix]
    previous, sign = one, 1
    for k in range(len(a) - 1):
        if a[k][k] == zero:
            pivot = next((j for j in range(k + 1, len(a)) if a[j][k] != zero), None)
            if pivot is None:
                return zero
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, len(a)):
            for j in range(k + 1, len(a)):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                q, remainder = divmod(numerator, previous)
                require(remainder == zero, "Non-exact Bareiss division")
                a[i][j] = q
        for i in range(k + 1, len(a)):
            a[i][k] = zero
        previous = pivot
    return sign * a[-1][-1]


def polynomial_hash(p) -> str:
    """SHA-256 of sorted 'e1,e2,...:coefficient\n' ASCII lines, decreasing lex."""
    h = hashlib.sha256()
    for e in sorted(p, reverse=True):
        h.update((",".join(map(str, e)) + ":" + str(p[e]) + "\n").encode("ascii"))
    return h.hexdigest()


def symbolic_minors(n: int, small_n: int):
    R, *yy = ring(",".join(f"y{j}" for j in range(1, n + 1)), ZZ)
    y = [R.zero] + yy
    alpha = [R.zero] + [alpha_sign(j) * y[j] * y[j + 1] for j in range(1, n)]
    ell = [R.zero] + [y[1] * h for h in dyck_moments(alpha, n - 1, R.zero, R.one)]
    # minors[S] is det M with top |S| rows and columns S+1; ell_S=-minors[S].
    minors = {(): R.one}
    records = []
    small = []
    def record(S, p):
        e = max(p)
        expected = predicted_exponent(S, n)
        require(e == expected, f"Leading exponent mismatch at {S}: {e} != {expected}")
        require(p[e] == 1, f"Nonmonic leading term at {S}")
        require(inverse_exponent(e) == S, f"Inverse failed at {S}")
        lam = partition_for_subset(S)
        d = frobenius_profile(lam)
        require(d == peeling_profile(lam), f"Profile formulas disagree: {S}")
        degree = 1 if not S else len(S) + 2 * sum(lam)
        require(all(sum(a) == degree for a in p), f"Nonhomogeneous minor {S}")
        require(degree <= n * (n + 1) // 2, f"Weight bound failed: {S}")
        records.append({"S": S, "partition": lam, "profile": d,
                        "exponent": e, "leading_coefficient": int(p[e]),
                        "term_count": len(p), "total_degree": degree,
                        "polynomial_sha256": polynomial_hash(p)})
        if not S or max(S) < small_n:
            require(all(not any(a[small_n:]) for a in p), "Unexpected later variable")
            small.append({"S": S, "terms": [[a[:small_n], int(p[a])]
                         for a in sorted(p, reverse=True)]})
    record((), ell[1])
    for size in range(1, n):
        for S in combinations(range(1, n), size):
            val = R.zero
            # Laplace expansion in the LAST row, reusing exact smaller minors.
            for j, s in enumerate(S):
                k = s + 2 - size
                if k >= 1:
                    val += (-1) ** (size + j + 1) * (-ell[k]) * minors[S[:j] + S[j + 1:]]
            minors[S] = val
            record(S, -val)
    return {"n": n, "method": "Dyck step dynamics + original Toeplitz Laplace determinants",
            "records": records}, {"n": small_n, "records": small}


def partitions(total: int, maximum: int | None = None):
    if total == 0:
        yield ()
        return
    if maximum is None:
        maximum = total
    for first in range(min(total, maximum), 0, -1):
        for rest in partitions(total - first, first):
            yield (first,) + rest


def generic_schur(max_size: int):
    R, *a = ring(",".join(f"a{j}" for j in range(1, max_size + 1)), ZZ)
    h = dyck_moments([R.zero] + a, max_size, R.zero, R.one)
    records = []
    for size in range(max_size + 1):
        for lam in partitions(size):
            r = len(lam)
            matrix = [[h[k] if k >= 0 else R.zero for j in range(r)
                       for k in [lam[i] - i + j]] for i in range(r)]
            p = bareiss(matrix, R.zero, R.one)
            d = frobenius_profile(lam)
            expected = d + (0,) * (max_size - len(d))
            sign = (-1) ** sum(d[1::2])
            require(max(p) == expected and p[expected] == sign, f"Schur mismatch: {lam}")
            records.append({"partition": lam, "profile": d, "leading_coefficient": sign,
                            "term_count": len(p), "polynomial_sha256": polynomial_hash(p)})
    return {"maximum_partition_size": max_size, "method": "Dyck dynamics + exact Bareiss JT determinant",
            "records": records}


def finite_bijections(max_n: int):
    output = []
    for n in range(1, max_n + 1):
        images = set()
        for r in range(n):
            for S in combinations(range(1, n), r):
                e = predicted_exponent(S, n)
                require(is_hilbert(e), f"Not in Hilbert basis: n={n}, S={S}, e={e}")
                require(inverse_exponent(e) == S, f"Inverse mismatch n={n}, S={S}")
                images.add(e)
        require(len(images) == 2 ** (n - 1), f"Not injective in n={n}")
        output.append({"n": n, "subsets": 2 ** (n - 1), "distinct_hilbert_images": len(images)})
    return {"note": "Tests only the closed combinatorial formulas, not the symbolic minors.",
            "records": output}


def lattice_vectors(n: int, budget: int):
    """Direct enumeration by normalized inequalities, not by the Hilbert generators."""
    def rec(prefix, remaining):
        i = len(prefix)
        if i == n:
            yield tuple(prefix)
            return
        cap = remaining if i == 0 else min(remaining, prefix[-1] * (n - i) // (n - i + 1))
        for v in range(cap + 1):
            yield from rec(prefix + [v], remaining - v)
    yield from rec([], budget)


def hilbert_checks(max_n: int, budget: int):
    records = []
    for n in range(1, max_n + 1):
        actual = Counter()
        for e in lattice_vectors(n, budget):
            actual[(sum(e[::2]), sum(e[1::2]))] += 1
            layers = layer_decomposition(e)
            require(all(is_hilbert(b) for b in layers), f"Bad layer of {e}")
            require(tuple(sum(b[i] for b in layers) for i in range(n)) == e,
                    f"Layers fail to sum to {e}")
        predicted = Counter({(0, 0): 1})
        for i in range(1, n + 1):
            updated = Counter()
            for (a, b), count in predicted.items():
                for k in range((budget - a - b) // (2 * i - 1) + 1):
                    updated[(a + i * k, b + (i - 1) * k)] += count
            predicted = updated
        require(actual == predicted, f"Bigraded Hilbert function mismatch in n={n}")
        records.append({"n": n, "total_degree_bound": budget,
                        "lattice_points": sum(actual.values()),
                        "bigraded_counts": [[a, b, actual[a, b]] for a, b in sorted(actual)]})
    return {"note": "Direct finite enumeration; the all-index proof does not assume this identity.",
            "records": records}


def write_json(path: Path, obj) -> None:
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--symbolic-n", type=int, default=11)
    parser.add_argument("--small-n", type=int, default=8)
    parser.add_argument("--partition-size", type=int, default=11)
    parser.add_argument("--bijection-n", type=int, default=16)
    parser.add_argument("--hilbert-n", type=int, default=8)
    parser.add_argument("--degree-bound", type=int, default=40)
    args = parser.parse_args()
    if min(args.symbolic_n, args.small_n, args.partition_size, args.bijection_n,
           args.hilbert_n, args.degree_bound) < 1 or args.small_n > args.symbolic_n:
        parser.error("Bounds must be positive; small-n cannot exceed symbolic-n.")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    print("Computing exact symbolic flag minors...", flush=True)
    symbolic, small = symbolic_minors(args.symbolic_n, args.small_n)
    write_json(args.output_dir / "symbolic_minors.json", symbolic)
    write_json(args.output_dir / "small_minors_full.json", small)
    print("Computing independent generic Schur determinants...", flush=True)
    schur = generic_schur(args.partition_size)
    write_json(args.output_dir / "generic_schur.json", schur)
    print("Checking finite bijections...", flush=True)
    bijection = finite_bijections(args.bijection_n)
    write_json(args.output_dir / "bijections.json", bijection)
    print("Enumerating finite lattice-point/Hilbert-function checks...", flush=True)
    hilbert = hilbert_checks(args.hilbert_n, args.degree_bound)
    write_json(args.output_dir / "hilbert_checks.json", hilbert)
    summary = {"status": "all exact checks passed",
               "environment": {"python": platform.python_version(), "sympy": sympy.__version__},
               "symbolic_n": args.symbolic_n, "symbolic_subsets": len(symbolic["records"]),
               "symbolic_total_terms": sum(row["term_count"] for row in symbolic["records"]),
               "largest_symbolic_term_count": max(row["term_count"] for row in symbolic["records"]),
               "generic_partition_size": args.partition_size,
               "generic_partitions": len(schur["records"]),
               "bijection_n": args.bijection_n,
               "formula_bijection_tests": sum(row["subsets"] for row in bijection["records"]),
               "hilbert_n": args.hilbert_n, "degree_bound": args.degree_bound,
               "lattice_points_enumerated": sum(row["lattice_points"] for row in hilbert["records"]),
               "full_small_minor_count": len(small["records"])}
    write_json(args.output_dir / "summary.json", summary)
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
