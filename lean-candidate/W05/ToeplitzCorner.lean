import W05.FractionSatisfies
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace W05

/-- An explicitly sized form of the original square, with offset s=0 or s=1 for its two parities. -/
def negativeToeplitzBlock {R : Type} [Neg R] (P : ℕ → R) (N s : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R := fun r c =>
  -P (N + s + c.val - r.val)

/-- The explicitly sized block is the actual original scalar minor, not an assumed model. -/
theorem negativeToeplitzMinor_eq_block {R : Type} [CommRing R]
    (P : ℕ → R) (N s : ℕ) (hs : s ≤ 1) :
    negativeToeplitzMinor P (2 * N + 1 + s) = -(negativeToeplitzBlock P N s).det := by
  unfold negativeToeplitzMinor negativeToeplitzMatrix
  have hd : (2 * N + 1 + s + 1) / 2 = N + 1 := by omega
  have hf : (2 * N + 1 + s) / 2 = N + s := by omega
  rw [hd, hf]
  rfl

/-- The original equations at indices one and two have coefficient one. -/
theorem negativeToeplitzMinor_first_two {R : Type} [CommRing R]
    (P : ℕ → R) (s : ℕ) (hs : s ≤ 1) : negativeToeplitzMinor P (s + 1) = P s := by
  have he : s + 1 = 2 * 0 + 1 + s := by omega
  rw [he, negativeToeplitzMinor_eq_block P 0 s hs, Matrix.det_fin_one]
  simp only [negativeToeplitzBlock, Fin.val_zero, Nat.zero_add, Nat.add_zero, Nat.sub_zero, neg_neg]

/-- Removing row zero and the last column gives the actual preceding square. -/
theorem negativeToeplitzBlock_corner_submatrix {R : Type} [Neg R]
    (P : ℕ → R) (N s : ℕ) :
    (negativeToeplitzBlock P (N + 1) s).submatrix Fin.succ Fin.castSucc =
      negativeToeplitzBlock P N s := by
  ext r c
  change -P (N + 1 + s + c.val - (r.val + 1)) = -P (N + s + c.val - r.val)
  apply congrArg (fun k : ℕ => -P k)
  omega

/-- Agreement below the new index gives agreement at every entry except the first-row last-column corner. -/
theorem negativeToeplitzBlock_agree_off_corner {R : Type} [Neg R]
    (P Q : ℕ → R) (N s : ℕ) (hagree : ∀ k : ℕ, k < 2 * N + s → P k = Q k)
    (r c : Fin (N + 1)) (hoff : r ≠ 0 ∨ c ≠ Fin.last N) :
    negativeToeplitzBlock P N s r c = negativeToeplitzBlock Q N s r c := by
  change -P (N + s + c.val - r.val) = -Q (N + s + c.val - r.val)
  apply congrArg (fun z : R => -z)
  apply hagree
  have hr := r.isLt
  have hc := c.isLt
  rcases hoff with hr0 | hcl
  · have hv : r.val ≠ 0 := by
      intro h
      apply hr0
      exact Fin.ext h
    omega
  · have hv : c.val ≠ N := by
      intro h
      apply hcl
      apply Fin.ext
      simpa only [Fin.val_last] using h
    omega

/-- Row-zero Laplace expansion identifies the actual highest-new-term coefficient. -/
theorem negativeToeplitzBlock_det_difference {R : Type} [CommRing R]
    (P Q : ℕ → R) (N s : ℕ)
    (hagree : ∀ k : ℕ, k < 2 * N + 2 + s → P k = Q k) :
    (negativeToeplitzBlock P (N + 1) s).det - (negativeToeplitzBlock Q (N + 1) s).det =
      (-1 : R) ^ (N + 1) * (-P (2 * N + 2 + s) - -Q (2 * N + 2 + s)) *
        (negativeToeplitzBlock P N s).det := by
  have hag : ∀ k : ℕ, k < 2 * (N + 1) + s → P k = Q k := by
    intro k hk
    apply hagree k
    omega
  have hcof (j : Fin (N + 2)) :
      (negativeToeplitzBlock Q (N + 1) s).submatrix Fin.succ j.succAbove =
        (negativeToeplitzBlock P (N + 1) s).submatrix Fin.succ j.succAbove := by
    ext r c
    exact (negativeToeplitzBlock_agree_off_corner P Q (N + 1) s hag
      r.succ (j.succAbove c) (Or.inl (Fin.succ_ne_zero r))).symm
  have hcorner (U : ℕ → R) :
      negativeToeplitzBlock U (N + 1) s 0 (Fin.last (N + 1)) = -U (2 * N + 2 + s) := by
    change -U (N + 1 + s + (N + 1) - 0) = -U (2 * N + 2 + s)
    apply congrArg (fun k : ℕ => -U k)
    omega
  rw [Matrix.det_succ_row_zero (negativeToeplitzBlock P (N + 1) s),
    Matrix.det_succ_row_zero (negativeToeplitzBlock Q (N + 1) s)]
  simp_rw [hcof]
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (Fin.last (N + 1))]
  · simp only [Fin.val_last, Fin.succAbove_last, negativeToeplitzBlock_corner_submatrix, hcorner]
    rw [← sub_mul, ← mul_sub]
  · intro j hj hlast
    have hr := negativeToeplitzBlock_agree_off_corner P Q (N + 1) s hag 0 j (Or.inr hlast)
    rw [hr, sub_self]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ (Fin.last (N + 1))))

/-- The original outer-negative minors have the actual preceding-minor coefficient, with its full sign. -/
theorem negativeToeplitzMinor_next_difference {R : Type} [CommRing R]
    (P Q : ℕ → R) (N s : ℕ) (hs : s ≤ 1)
    (hagree : ∀ k : ℕ, k < 2 * N + 2 + s → P k = Q k) :
    negativeToeplitzMinor P (2 * N + 3 + s) - negativeToeplitzMinor Q (2 * N + 3 + s) =
      (-1 : R) ^ (N + 2) * (P (2 * N + 2 + s) - Q (2 * N + 2 + s)) *
        negativeToeplitzMinor P (2 * N + 1 + s) := by
  have hb : 2 * N + 3 + s = 2 * (N + 1) + 1 + s := by omega
  rw [hb, negativeToeplitzMinor_eq_block P (N + 1) s hs,
    negativeToeplitzMinor_eq_block Q (N + 1) s hs, negativeToeplitzMinor_eq_block P N s hs]
  have hn : -(negativeToeplitzBlock P (N + 1) s).det -
      -(negativeToeplitzBlock Q (N + 1) s).det =
      -((negativeToeplitzBlock P (N + 1) s).det - (negativeToeplitzBlock Q (N + 1) s).det) := by ring
  rw [hn, negativeToeplitzBlock_det_difference P Q N s hagree, pow_succ (-1 : R) (N + 1)]
  ring

end W05
