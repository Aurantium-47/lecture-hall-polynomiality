import W05.CanonicalHankel
import W05.JacobiPolynomialWitness
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators

namespace W05

/-- Every actual odd positive weight has positive coefficient. -/
theorem signedJacobiWeight_odd (h : ℕ) :
    signedJacobiWeight (2 * h + 1) =
      MvPolynomial.X (2 * h) * MvPolynomial.X (2 * h + 1) := by
  have hn : 2 * h + 1 ≠ 0 := by omega
  have he : ¬ (4 ≤ 2 * h + 1 ∧ Even (2 * h + 1)) := by
    rintro ⟨_, k, hk⟩
    omega
  have hs : 2 * h + 1 - 1 = 2 * h := by omega
  simp only [signedJacobiWeight, if_neg hn, if_neg he, hs, map_one, one_mul]

/-- The first positive even weight is positive; all later positive even weights are negative. -/
theorem signedJacobiWeight_even (h : ℕ) :
    signedJacobiWeight (2 * h + 2) =
      if h = 0 then MvPolynomial.X (2 * h + 1) * MvPolynomial.X (2 * h + 2)
      else -(MvPolynomial.X (2 * h + 1) * MvPolynomial.X (2 * h + 2)) := by
  by_cases hh : h = 0
  · subst h
    simp [signedJacobiWeight]
  · have hn : 2 * h + 2 ≠ 0 := by omega
    have he : 4 ≤ 2 * h + 2 ∧ Even (2 * h + 2) :=
      ⟨by omega, h + 1, by omega⟩
    have hs : 2 * h + 2 - 1 = 2 * h + 1 := by omega
    simp only [signedJacobiWeight, if_neg hn, if_pos he, hs, if_neg hh,
      map_neg, map_one, neg_one_mul, neg_mul]

/-- The actual d_h is an explicit signed product of variable monomials, also at h=0. -/
theorem jacobiDiagonalWeight_signed (h : ℕ) :
    jacobiDiagonalWeight signedJacobiWeight h =
      (-1 : MvPolynomial ℕ ℤ) ^ (h - 1) *
        ∏ k ∈ Finset.range h,
          MvPolynomial.X (2 * k) * MvPolynomial.X (2 * k + 1) ^ 2 *
            MvPolynomial.X (2 * k + 2) := by
  induction h with
  | zero => simp [jacobiDiagonalWeight]
  | succ h ih =>
    rw [jacobiDiagonalWeight_succ, ih, signedJacobiWeight_odd, signedJacobiWeight_even,
      Finset.prod_range_succ]
    by_cases hh : h = 0
    · subst h
      simp [pow_two, mul_assoc]
    · have he : h + 1 - 1 = (h - 1) + 1 := by omega
      have hs : (-1 : MvPolynomial ℕ ℤ) ^ (h + 1 - 1) =
          -((-1 : MvPolynomial ℕ ℤ) ^ (h - 1)) := by
        rw [he, pow_succ, mul_neg_one]
      rw [if_neg hh, hs]
      simp only [pow_two, mul_assoc, mul_neg, neg_mul]

/-- The actual signed canonical H0 determinant, with every scalar sign collected. -/
theorem canonicalJacobiHankel_signed_det_zero (N : ℕ) :
    (canonicalJacobiHankel signedJacobiWeight N 0).det =
      (-1 : MvPolynomial ℕ ℤ) ^ (N * (N - 1) / 2) *
        ∏ h : Fin (N + 1), ∏ k ∈ Finset.range h.val,
          MvPolynomial.X (2 * k) * MvPolynomial.X (2 * k + 1) ^ 2 *
            MvPolynomial.X (2 * k + 2) := by
  have he : (∑ h : Fin (N + 1), h.val - 1) = N * (N - 1) / 2 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.zero_sub, Fin.val_succ, Nat.add_sub_cancel, Nat.zero_add]
    rw [Fin.sum_univ_eq_sum_range (fun h : ℕ => h) N, Finset.sum_range_id]
  rw [canonicalJacobiHankel_det_zero]
  simp_rw [jacobiDiagonalWeight_signed]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, he]

/-- The signed H1 determinant has the actual positive odd-weight product in addition to H0. -/
theorem canonicalJacobiHankel_signed_det_one (N : ℕ) :
    (canonicalJacobiHankel signedJacobiWeight N 1).det =
      (∏ h : Fin (N + 1), MvPolynomial.X (2 * h.val) * MvPolynomial.X (2 * h.val + 1)) *
        ((-1 : MvPolynomial ℕ ℤ) ^ (N * (N - 1) / 2) *
          ∏ h : Fin (N + 1), ∏ k ∈ Finset.range h.val,
            MvPolynomial.X (2 * k) * MvPolynomial.X (2 * k + 1) ^ 2 *
              MvPolynomial.X (2 * k + 2)) := by
  have hd := canonicalJacobiHankel_signed_det_zero N
  rw [canonicalJacobiHankel_det_zero] at hd
  rw [canonicalJacobiHankel_det_one, hd]
  simp_rw [signedJacobiWeight_odd]

end W05
