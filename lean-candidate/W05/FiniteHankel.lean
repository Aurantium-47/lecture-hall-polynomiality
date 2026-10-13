import W05.JacobiBalance

open scoped BigOperators

namespace W05

/-- The actual shifted power-moment matrix of one fixed finite Jacobi block. -/
def finiteJacobiHankel {R : Type} [Semiring R] (α : ℕ → R) (N s : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R := fun i j =>
  (finiteJacobi α (N + 1) ^ (i.val + j.val + s)) 0 0

/-- A division-free factorization of the actual finite power moments. -/
theorem finiteJacobiHankel_factorization {R : Type} [CommSemiring R]
    (α : ℕ → R) (N s : ℕ) :
    finiteJacobiHankel α N s =
      jacobiPowerRows α N * (finiteJacobi α (N + 1) ^ s) *
        jacobiDiagonal α (N + 1) * (jacobiPowerRows α N).transpose := by
  let J := finiteJacobi α (N + 1)
  let L := jacobiPowerRows α N
  let D := jacobiDiagonal α (N + 1)
  have hrow (i h : Fin (N + 1)) : (L * J ^ s) i h = (J ^ (i.val + s)) 0 h := by
    change (J ^ i.val * J ^ s) 0 h = (J ^ (i.val + s)) 0 h
    rw [pow_add]
  ext i j
  change (J ^ (i.val + j.val + s)) 0 0 = ((L * J ^ s * D) * L.transpose) i j
  rw [Matrix.mul_apply]
  simp only [D, jacobiDiagonal, Matrix.mul_diagonal, Matrix.transpose_apply, hrow]
  change (J ^ (i.val + j.val + s)) 0 0 =
    ∑ h : Fin (N + 1),
      ((J ^ (i.val + s)) 0 h * jacobiDiagonalWeight α h.val) * (J ^ j.val) 0 h
  have hexp : i.val + j.val + s = i.val + s + j.val := by omega
  rw [hexp, pow_add, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [finiteJacobi_pow_balance_at_zero α N j.val h]
  exact (mul_assoc _ _ _).symm

/-- Determinants of these finite shifted moments, including singular and zero-weight cases. -/
theorem finiteJacobiHankel_det {R : Type} [CommRing R] (α : ℕ → R) (N s : ℕ) :
    (finiteJacobiHankel α N s).det =
      (finiteJacobi α (N + 1)).det ^ s *
        ∏ h : Fin (N + 1), jacobiDiagonalWeight α h.val := by
  rw [finiteJacobiHankel_factorization]
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_pow,
    jacobiPowerRows_det_one, jacobiDiagonal, Matrix.det_diagonal, one_mul, mul_one]

/-- The unshifted finite power-moment determinant is the product of the actual d_h. -/
theorem finiteJacobiHankel_det_zero {R : Type} [CommRing R] (α : ℕ → R) (N : ℕ) :
    (finiteJacobiHankel α N 0).det =
      ∏ h : Fin (N + 1), jacobiDiagonalWeight α h.val := by
  simpa only [pow_zero, one_mul] using finiteJacobiHankel_det α N 0

end W05
