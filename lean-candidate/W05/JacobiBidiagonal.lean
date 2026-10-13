import W05.FiniteJacobi

namespace W05

/-- The unit lower bidiagonal factor of the actual finite Jacobi matrix. -/
def jacobiLowerBidiagonal {R : Type} [Semiring R] (α : ℕ → R) (N : ℕ) :
    Matrix (Fin N) (Fin N) R :=
  let S : Matrix (Fin N) (Fin N) R :=
    fun i j => if i.val = j.val + 1 then α (2 * i.val) else 0
  (1 : Matrix (Fin N) (Fin N) R) + S

/-- The upper bidiagonal factor, with odd-indexed weights on its diagonal. -/
def jacobiUpperBidiagonal {R : Type} [Semiring R] (α : ℕ → R) (N : ℕ) :
    Matrix (Fin N) (Fin N) R := fun i j =>
  if j.val = i.val then α (2 * i.val + 1)
  else if j.val = i.val + 1 then 1 else 0

/-- Division-free factorization of the existing Jacobi definition, including size zero. -/
theorem finiteJacobi_bidiagonal_factorization {R : Type} [CommSemiring R]
    (α : ℕ → R) (N : ℕ) :
    finiteJacobi α N = jacobiLowerBidiagonal α N * jacobiUpperBidiagonal α N := by
  let S : Matrix (Fin N) (Fin N) R :=
    fun i j => if i.val = j.val + 1 then α (2 * i.val) else 0
  change finiteJacobi α N = (1 + S) * jacobiUpperBidiagonal α N
  rw [add_mul, one_mul]
  ext i j
  change finiteJacobi α N i j = jacobiUpperBidiagonal α N i j +
    ∑ k : Fin N, S i k * jacobiUpperBidiagonal α N k j
  by_cases hi : i.val = 0
  · have hs : (∑ k : Fin N, S i k * jacobiUpperBidiagonal α N k j) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hne : i.val ≠ k.val + 1 := by omega
      simp only [S, if_neg hne, zero_mul]
    rw [hs, add_zero]
    simp [finiteJacobi, jacobiUpperBidiagonal, hi]
  · let t : Fin N := ⟨i.val - 1, by have := i.isLt; omega⟩
    have hit : i.val = t.val + 1 := by dsimp [t]; omega
    have hs : (∑ k : Fin N, S i k * jacobiUpperBidiagonal α N k j) =
        α (2 * i.val) * jacobiUpperBidiagonal α N t j := by
      rw [Finset.sum_eq_single t]
      · simp only [S, if_pos hit]
      · intro k hk hkt
        have hne : i.val ≠ k.val + 1 := by
          intro h
          apply hkt
          apply Fin.ext
          omega
        simp only [S, if_neg hne, zero_mul]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ t))
    rw [hs]
    by_cases hdiag : j.val = i.val
    · have hjt : j.val ≠ t.val := by omega
      have hjup : j.val = t.val + 1 := by omega
      simp only [finiteJacobi, jacobiUpperBidiagonal, if_pos hdiag, if_neg hi,
        if_neg hjt, if_pos hjup, mul_one]
      exact add_comm _ _
    · by_cases hup : j.val = i.val + 1
      · have hjt : j.val ≠ t.val := by omega
        have hjup : j.val ≠ t.val + 1 := by omega
        simp only [finiteJacobi, jacobiUpperBidiagonal, if_neg hdiag, if_pos hup,
          if_neg hjt, if_neg hjup, mul_zero, add_zero]
      · by_cases hdown : i.val = j.val + 1
        · have hjt : j.val = t.val := by omega
          have harith : 2 * t.val + 1 = 2 * i.val - 1 := by omega
          simp only [finiteJacobi, jacobiUpperBidiagonal, if_neg hdiag, if_neg hup,
            if_pos hdown, if_pos hjt, zero_add]
          rw [harith]
          exact mul_comm _ _
        · have hjt : j.val ≠ t.val := by omega
          have hjup : j.val ≠ t.val + 1 := by omega
          simp only [finiteJacobi, jacobiUpperBidiagonal, if_neg hdiag, if_neg hup,
            if_neg hdown, if_neg hjt, if_neg hjup, mul_zero, add_zero]

/-- The lower factor has determinant one without any assumption on the weights. -/
theorem jacobiLowerBidiagonal_det_one {R : Type} [CommRing R]
    (α : ℕ → R) (N : ℕ) : (jacobiLowerBidiagonal α N).det = 1 := by
  have htri : (jacobiLowerBidiagonal α N).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hijv : i.val < j.val := hij
    have hne : i ≠ j := by intro h; subst j; omega
    have hd : i.val ≠ j.val + 1 := by omega
    simp only [jacobiLowerBidiagonal, Matrix.add_apply, Matrix.one_apply,
      if_neg hne, if_neg hd, zero_add]
  rw [Matrix.det_of_lowerTriangular (jacobiLowerBidiagonal α N) htri]
  apply Finset.prod_eq_one
  intro i hi
  have hn : i.val ≠ i.val + 1 := by omega
  simp only [jacobiLowerBidiagonal, Matrix.add_apply, Matrix.one_apply_eq,
    if_neg hn, add_zero]

/-- The upper factor's determinant is the product of the odd-indexed weights. -/
theorem jacobiUpperBidiagonal_det_product {R : Type} [CommRing R]
    (α : ℕ → R) (N : ℕ) :
    (jacobiUpperBidiagonal α N).det = ∏ i : Fin N, α (2 * i.val + 1) := by
  have htri : (jacobiUpperBidiagonal α N).BlockTriangular id := by
    intro i j hji
    have hval : j.val < i.val := hji
    have hdiag : j.val ≠ i.val := by omega
    have hup : j.val ≠ i.val + 1 := by omega
    simp only [jacobiUpperBidiagonal, if_neg hdiag, if_neg hup]
  rw [Matrix.det_of_upperTriangular htri]
  apply Finset.prod_congr rfl
  intro i hi
  simp [jacobiUpperBidiagonal]

/-- Closed determinant formula for the actual finite Jacobi matrix, with zero weights allowed. -/
theorem finiteJacobi_det_product {R : Type} [CommRing R]
    (α : ℕ → R) (N : ℕ) :
    (finiteJacobi α N).det = ∏ i : Fin N, α (2 * i.val + 1) := by
  rw [finiteJacobi_bidiagonal_factorization, Matrix.det_mul,
    jacobiLowerBidiagonal_det_one, jacobiUpperBidiagonal_det_product, one_mul]

end W05
