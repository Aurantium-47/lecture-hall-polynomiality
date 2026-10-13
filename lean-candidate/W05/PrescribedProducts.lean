import W05.SignedWeightProducts

open scoped BigOperators

namespace W05

/-- Raising all previous prefix exponents by one introduces one full prefix product. -/
theorem prefixPowerProduct_succ {R : Type} [CommMonoid R] (x : ℕ → R) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), x j ^ (n + 1 - j)) =
      (∏ j ∈ Finset.range n, x j ^ (n - j)) * ∏ j ∈ Finset.range (n + 1), x j := by
  have hf : (∏ j ∈ Finset.range n, x j ^ (n + 1 - j)) =
      (∏ j ∈ Finset.range n, x j ^ (n - j)) * ∏ j ∈ Finset.range n, x j := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    have he : n + 1 - j = (n - j) + 1 := by
      have := Finset.mem_range.mp hj
      omega
    rw [he, pow_succ]
  rw [Finset.prod_range_succ (fun j => x j ^ (n + 1 - j)) n,
    Finset.prod_range_succ (fun j => x j) n, hf]
  have hn : n + 1 - n = 1 := by omega
  rw [hn, pow_one, mul_assoc]

/-- The paired weight monomial, multiplied by its initial variable, is two full prefix products. -/
theorem pairedWeightProduct_prefix {R : Type} [CommMonoid R] (x : ℕ → R) (h : ℕ) :
    x 0 * (∏ k ∈ Finset.range h, x (2 * k) * x (2 * k + 1) ^ 2 * x (2 * k + 2)) =
      (∏ j ∈ Finset.range (2 * h), x j) * ∏ j ∈ Finset.range (2 * h + 1), x j := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih]
    have hs : 2 * (h + 1) = 2 * h + 2 := by omega
    simp only [hs, Finset.prod_range_succ, pow_two]
    ac_rfl

/-- The full nested Jacobi monomial has exactly the descending odd-prefix exponents. -/
theorem nestedWeightProduct_odd {R : Type} [CommMonoid R] (x : ℕ → R) (N : ℕ) :
    x 0 ^ (N + 1) *
        (∏ h : Fin (N + 1), ∏ k ∈ Finset.range h.val,
          x (2 * k) * x (2 * k + 1) ^ 2 * x (2 * k + 2)) =
      ∏ j ∈ Finset.range (2 * N + 1), x j ^ (2 * N + 1 - j) := by
  rw [Fin.prod_univ_eq_prod_range
    (fun h => ∏ k ∈ Finset.range h, x (2 * k) * x (2 * k + 1) ^ 2 * x (2 * k + 2)) (N + 1)]
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      _ = (x 0 ^ (N + 1) *
          (∏ h ∈ Finset.range (N + 1), ∏ k ∈ Finset.range h,
            x (2 * k) * x (2 * k + 1) ^ 2 * x (2 * k + 2))) *
          (x 0 * ∏ k ∈ Finset.range (N + 1),
            x (2 * k) * x (2 * k + 1) ^ 2 * x (2 * k + 2)) := by
        rw [pow_succ, Finset.prod_range_succ]
        ac_rfl
      _ = (∏ j ∈ Finset.range (2 * N + 1), x j ^ (2 * N + 1 - j)) *
          ((∏ j ∈ Finset.range (2 * (N + 1)), x j) *
            ∏ j ∈ Finset.range (2 * (N + 1) + 1), x j) := by
        rw [ih, pairedWeightProduct_prefix]
      _ = _ := by
        have hs : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
        rw [hs, prefixPowerProduct_succ x ((2 * N + 1) + 1),
          prefixPowerProduct_succ x (2 * N + 1)]
        exact (mul_assoc _ _ _).symm

/-- Pairing successive variables enumerates the even-length prefix exactly once. -/
theorem pairedIndexProduct_prefix {R : Type} [CommMonoid R] (x : ℕ → R) (n : ℕ) :
    (∏ h : Fin n, x (2 * h.val) * x (2 * h.val + 1)) =
      ∏ j ∈ Finset.range (2 * n), x j := by
  rw [Fin.prod_univ_eq_prod_range (fun h => x (2 * h) * x (2 * h + 1)) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have hs : 2 * (n + 1) = 2 * n + 2 := by omega
    simp only [hs, Finset.prod_range_succ, mul_assoc]

noncomputable section

/-- The monomial prescribed by the original equation at index i, with X_j = y_(j+1). -/
def prescribedMonomial (i : ℕ) : MvPolynomial ℕ ℤ :=
  ∏ j : Fin i, MvPolynomial.X j.val ^ (i - j.val)

/-- The scaled signed H0 determinant has the exact original odd-index monomial. -/
theorem canonicalJacobiHankel_prescribed_zero (N : ℕ) :
    MvPolynomial.X 0 ^ (N + 1) * (canonicalJacobiHankel signedJacobiWeight N 0).det =
      (-1 : MvPolynomial ℕ ℤ) ^ (N * (N - 1) / 2) * prescribedMonomial (2 * N + 1) := by
  rw [canonicalJacobiHankel_signed_det_zero, mul_left_comm,
    nestedWeightProduct_odd (fun j => (MvPolynomial.X j : MvPolynomial ℕ ℤ)) N]
  rw [prescribedMonomial,
    Fin.prod_univ_eq_prod_range
      (fun j : ℕ => (MvPolynomial.X j : MvPolynomial ℕ ℤ) ^ (2 * N + 1 - j)) (2 * N + 1)]

/-- The scaled signed H1 determinant has the exact original even-index monomial. -/
theorem canonicalJacobiHankel_prescribed_one (N : ℕ) :
    MvPolynomial.X 0 ^ (N + 1) * (canonicalJacobiHankel signedJacobiWeight N 1).det =
      (-1 : MvPolynomial ℕ ℤ) ^ (N * (N - 1) / 2) * prescribedMonomial (2 * N + 2) := by
  rw [canonicalJacobiHankel_signed_det_one,
    pairedIndexProduct_prefix (fun j => (MvPolynomial.X j : MvPolynomial ℕ ℤ)) (N + 1)]
  calc
    _ = (-1 : MvPolynomial ℕ ℤ) ^ (N * (N - 1) / 2) *
        ((MvPolynomial.X 0 ^ (N + 1) *
          (∏ h : Fin (N + 1), ∏ k ∈ Finset.range h.val,
            MvPolynomial.X (2 * k) * MvPolynomial.X (2 * k + 1) ^ 2 *
              MvPolynomial.X (2 * k + 2))) *
          ∏ j ∈ Finset.range (2 * (N + 1)), MvPolynomial.X j) := by ac_rfl
    _ = (-1 : MvPolynomial ℕ ℤ) ^ (N * (N - 1) / 2) *
        ((∏ j ∈ Finset.range (2 * N + 1), MvPolynomial.X j ^ (2 * N + 1 - j)) *
          ∏ j ∈ Finset.range (2 * (N + 1)), MvPolynomial.X j) := by
      rw [nestedWeightProduct_odd (fun j => (MvPolynomial.X j : MvPolynomial ℕ ℤ)) N]
    _ = _ := by
      have hs : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
      rw [hs,
        ← prefixPowerProduct_succ (fun j => (MvPolynomial.X j : MvPolynomial ℕ ℤ)) (2 * N + 1),
        prescribedMonomial,
        Fin.prod_univ_eq_prod_range
          (fun j : ℕ => (MvPolynomial.X j : MvPolynomial ℕ ℤ) ^ (2 * N + 2 - j)) (2 * N + 2)]

end
end W05
