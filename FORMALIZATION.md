# Formalized polynomiality and signed Dyck identification

The Lean supplement proves the original defining equations have a unique solution over rational functions, every term has an integer-polynomial witness in the required variable prefix, and that solution has the manuscript's exact signed Dyck-path expression. The fixed mathematical source is commit `634f8fa6637688044f12ad108b14051e6d29e8bb`. The source interpretations below remain part of these statements.

## Equations and the polynomiality core

Let `K = FractionRing (MvPolynomial Nat Rat)`. For `i >= 1`, put `d = (i+1)/2`, with natural-number division. The `d` by `d` matrix has entry `-P(i/2+c-r)` for `r,c : Fin d`; its actual index differences are nonnegative. `SatisfiesRational P` requires the negative determinant to equal the product over `j : Fin i` of the image of `X_j` in `K`, raised to `i-j.val`. The negative entries and exterior minus sign are both retained.

[W05.rational_solution_unique_with_integer_prefix](lean-candidate/W05/RationalCore.lean) has no input assumptions. It gives existence, uniqueness among all solutions in `K`, and, for every `n : Nat`, a witness in `MvPolynomial (Fin (n+1)) Int`. Its image under variable inclusion, coefficient inclusion `Int -> Rat`, and the fraction-field embedding equals `P n`.

Here `P n` represents `ell_(n+1)`, and `X_j` represents `y_(j+1)`. Index zero and the first two equations are included. Uniqueness concerns independent indeterminates in this fraction field; it does not assert uniqueness after every numerical specialization at vanishing divisors. The [historical complete core type](verification/W05_actual_main_type.txt) remains unchanged.

## Direct Dyck formula

[DyckWeight.lean](lean-candidate/W05/DyckWeight.lean) reads the actual symbols of mathlib's `DyckWord`. Before symbol `k`, height is the number of earlier up steps minus earlier down steps. The proved prefix condition makes this natural subtraction exact. An up step has weight one; a down step uses `alpha` at its departure height. `dyckWeight` is the product over the actual word indices.

[DyckMomentIdentification.lean](lean-candidate/W05/DyckMomentIdentification.lean) defines `dyckMoment alpha n` as the finite sum of these products over all genuine Dyck words of semilength `n`. Its definition does not use a Jacobi recurrence, matrix power, or canonical moment. Actual mutually inverse maps to all length-`2*n` closed walks in `pathGraph (2*(n+1))`, preservation of the direct weights, and finite-sum reindexing connect it to the weighted-walk matrix expansion and two-step Jacobi contraction.

The resulting statements include:

```lean
dyckMoment alpha n = canonicalJacobiMoment alpha n

signedCanonicalCandidate n =
  MvPolynomial.X 0 * dyckMoment signedJacobiWeight n
```

For every `P : Nat -> FractionRing (MvPolynomial Nat Rat)` satisfying the original equations and every `n : Nat`, `W05.SatisfiesRational_dyck` proves

```lean
P n = integerPolynomialToRationalField
  (MvPolynomial.X 0 * dyckMoment signedJacobiWeight n)
```

At positive height `h`, `signedJacobiWeight h` is `C(epsilon_h) * X_(h-1) * X_h`, where `epsilon_h = -1` exactly when `h >= 4` and `h` is even, and is one otherwise. This gives precisely `ell_(n+1) = y_1 * mu_n`, including the external `X_0` factor.

The empty word has weight one and `dyckMoment alpha 0 = 1`. Every genuine down step departs from positive height; weight and moment congruence theorems prove `alpha_0` has no effect. Legal zero-weight paths remain in the sums. Zero and negative weights are allowed; the general moment theorem requires `CommSemiring`, which the integer polynomial ring satisfies. The [unaltered complete signed-Dyck type excerpt](verification/W05_actual_signed_dyck_type.txt) includes the definition types, weight preservation, moment equality, signed candidate identity, and arbitrary rational-field solution identity.

## Scope and source interpretation

The chain also proves bandwidth, exact finite cutoffs, division-free diagonal balance, Hankel factorization, a bidiagonal determinant identity, signed products, actual negative Toeplitz minors, and strong-induction uniqueness. The integer-prefix result and signed Dyck expression apply to the same unique rational-field solution.

The original paper's page 3 printed column range has one more column than row. The supplement uses `floor(i/2)+1,...,i`, supported by its square-block description and examples. The page 4 final monomial of `ell_4` disagrees with the defining equations and page 8 list; the [README](README.md#source-interpretation) gives the consistent expression. These are disclosed interpretations, not an author-issued erratum or a proof of a literal nonsquare determinant.

The composition coefficient formula, exact nonzero-monomial counts, continued-fraction statements as separate theorems, and SAGBI/degeneration extension have not been formalized here. Their written proofs and historical finite records retain their separate scope. No worldwide-priority or human peer-review claim is made.

## Execution and retained history

[Run 38511499860](https://github.com/Aurantium-47/lecture-hall-polynomiality/actions/runs/38511499860), job `115680821200`, compiled all **28 project modules**, including `ImportProbe` and the complete earlier core. It checked 28 newly generated project imports, 175 complete declaration types and transitive axiom lists, and 30 resource-supervised Lean commands with exit zero. All 41 definition/instance printouts, both integer- and rational-domain Field checks, and final source-integrity and declaration assertions were observed. Later normal metadata confirmed the same unique job and all seven steps completed successfully. Job completion time and HTTP headers were not returned and remain null in the [new execution summary](verification/W05_signed_dyck_execution_summary.json).

The axiom union is `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, custom axiom, or native-evaluation trust is used. Peak sampled process-group RSS was 1,906,302,976 bytes, with zero observed swap and no guard abort. This is a sampled process-group metric.

The earlier core record remains intact: commit `1dc269cf5bedfc1320a3f4f6d440cf12dd0d9876`, [run 38480976066](https://github.com/Aurantium-47/lecture-hall-polynomiality/actions/runs/38480976066), 19 modules, 103 declaration types/axiom lists, and 21 commands. Its [execution summary](verification/W05_execution_summary.json) describes coverage at that historical stage, including the then-unformalized Dyck identification. The new run compiled the full 28-module chain, not only the nine added modules.

[Reproduction and trust boundaries](REPRODUCIBILITY.md) give fixed versions, external caches, two disclosed cache-helper edits, historical workflow titles, byte-hash conventions, and resource guards. Neither Lean nor the mathematical verification suites were rerun for this documentation update. Manuscripts, PDFs, computation records, the v0.2.0 tag, and historical release remain unchanged.

This work was completed with AI assistance.
