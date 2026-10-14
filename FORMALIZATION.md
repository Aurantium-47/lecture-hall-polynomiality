# Formalized polynomiality core

The Lean supplement proves the existence and uniqueness of the sequence defined by the positive-index equations below, directly in the fraction field of rational-coefficient polynomials. Every term has an integer-coefficient polynomial representative in exactly its permitted prefix of variables. This covers the polynomiality core of Katthän's Conjecture 3.4 under the source interpretation stated in the README.

The supplementary source is fixed at commit `1dc269cf5bedfc1320a3f4f6d440cf12dd0d9876`. The mathematical modules are in `lean-candidate/W05/`; the terminal theorem is `W05.rational_solution_unique_with_integer_prefix` in `RationalCore.lean`.

## Statement and indexing

Let `K = FractionRing (MvPolynomial Nat Rat)`. For `i >= 1`, put `d = (i+1)/2`, with natural-number division, and define the `d` by `d` matrix with entry `-P(i/2+c-r)` for `r,c : Fin d`. The actual indices have nonnegative differences. The predicate `SatisfiesRational P` requires the negative determinant of this matrix to equal

```text
product over j : Fin i of (image of X_j in K)^(i-j.val).
```

The final theorem has no input assumptions. It asserts that there exists such a sequence `P : Nat -> K`, that any other sequence in the same field satisfying these equations equals `P`, and that for every `n : Nat` there exists

```text
f : MvPolynomial (Fin (n+1)) Int
```

whose image under the variable inclusion, coefficient inclusion `Int -> Rat`, and fraction-field embedding equals `P n`. Thus `P n` represents the original term `ell_(n+1)` and `X_j` represents `y_(j+1)`. The sequence index zero and the equations with indices one and two are included explicitly. The theorem is about independent indeterminates; this uniqueness argument is not a statement about every numerical specialization at zero divisors.

The exact fully expanded terminal type is distributed in `verification/W05_actual_main_type.txt`.

## Proof ingredients and scope

The proof uses finite Jacobi matrices, bandwidth of their powers, division-free diagonal balance, Hankel factorization, a bidiagonal determinant identity, exact truncation stability, signed products, and the actual negative Toeplitz minors. A corner-cofactor difference identity and nonzero prescribed monomials give uniqueness by strong induction. The rational-field proof uses the natural coefficient map for existence and integer witnesses and proves uniqueness directly for arbitrary rational-field solutions.

These modules do not formalize the manuscript's exact Dyck-path identification, composition coefficient formula, monomial count, or the SAGBI and degeneration extension. Those results retain their separate written proofs. This supplement does not make a worldwide-priority claim.

The source paper's page 3 column range has one extra column if read literally. The supplement uses `floor(i/2)+1,...,i`, consistent with its square-block description and examples. The page 4 final monomial of `ell_4` disagrees with the defining equations and the page 8 list. The README records the formula consistent with the equations and later list. These qualifications remain part of the statement; they are not an author-issued erratum.

## Actual execution

The fixed [GitHub Actions run 38480976066](https://github.com/Aurantium-47/lecture-hall-polynomiality/actions/runs/38480976066), job `115583199709`, compiled 19 project modules, including `ImportProbe`. All 19 project imports were bound to newly generated `.olean` files. It printed 103 complete declaration types and their transitive axiom lists. All 21 resource-supervised Lean commands exited zero, both integer- and rational-domain field checks ran, and the final source-integrity and declaration assertions passed.

The union of reported axioms is `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, custom axiom, or native-evaluation trust is used in these checked declarations. The peak sampled process-group RSS was 1,906,372,608 bytes, with no observed swap usage or resource-guard abort. This is a sampled group metric, not a claim about all system memory.

The run used Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with the nine dependencies pinned by `lean-candidate/lake-manifest.json`. Project sources were newly compiled, while external libraries used fixed precompiled caches. Full external dependency source rebuilding, full dependency replay, and an independent kernel implementation were not performed. The exact run's terminal success and complete job log were obtained; a separate final job/step metadata fetch was not performed.

## Reproduction

The workflow retains its historical banded-spine title. Its terminal declaration and recorded source hashes, rather than that early title, define the verified scope.

The checked workflow `.github/workflows/w05-hankel-spine.yml` contains the exact source hashes, dependency revisions, five cache roots, ordered per-module compilation commands, fresh-import checks, full type/axiom probe, and resource guards. It runs on the verification branch `codex/w05-hankel-spine`; updating the default documentation does not trigger another verification run. A reproduction should use that fixed workflow and commit and retain its resource limits. No repeat run is claimed for this documentation update.

The old v0.2.0 release remains the historical manuscript-and-computation package. Its mathematical manuscripts, code, data, dependency files, tag, and release are preserved. This default-branch update adds the formal supplement and its execution record.

This work was completed with AI assistance.
