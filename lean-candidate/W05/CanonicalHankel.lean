import W05.FiniteHankel
import W05.JacobiMoments
import W05.JacobiBidiagonal
import Mathlib.Data.Fin.Rev

open scoped BigOperators

namespace W05

/-- Hankel matrices of the canonical moments, rather than one fixed block's moments. -/
def canonicalJacobiHankel {R : Type} [Semiring R] (α : ℕ → R) (N s : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R := fun i j =>
  canonicalJacobiMoment α (i.val + j.val + s)

/-- The zero and one shifts satisfy the actual strict cutoff bound entry by entry. -/
theorem canonicalJacobiHankel_eq_finite {R : Type} [Semiring R]
    (α : ℕ → R) (N s : ℕ) (hs : s ≤ 1) :
    canonicalJacobiHankel α N s = finiteJacobiHankel α N s := by
  ext i j
  exact canonicalJacobiMoment_eq_block α N (i.val + j.val + s)
    (by have := i.isLt; have := j.isLt; omega)

/-- The unshifted canonical determinant is the diagonal-weight product. -/
theorem canonicalJacobiHankel_det_zero {R : Type} [CommRing R]
    (α : ℕ → R) (N : ℕ) :
    (canonicalJacobiHankel α N 0).det =
      ∏ h : Fin (N + 1), jacobiDiagonalWeight α h.val := by
  rw [canonicalJacobiHankel_eq_finite α N 0 (by omega), finiteJacobiHankel_det_zero]

/-- The once-shifted canonical determinant has the additional odd-weight product. -/
theorem canonicalJacobiHankel_det_one {R : Type} [CommRing R]
    (α : ℕ → R) (N : ℕ) :
    (canonicalJacobiHankel α N 1).det =
      (∏ h : Fin (N + 1), α (2 * h.val + 1)) *
        ∏ h : Fin (N + 1), jacobiDiagonalWeight α h.val := by
  rw [canonicalJacobiHankel_eq_finite α N 1 (by omega), finiteJacobiHankel_det,
    finiteJacobi_det_product, pow_one]

/-- The original square negative Toeplitz matrix for a zero-based sequence P. -/
def negativeToeplitzMatrix {R : Type} [Neg R] (P : ℕ → R) (i : ℕ) :
    Matrix (Fin ((i + 1) / 2)) (Fin ((i + 1) / 2)) R := fun r c =>
  -P (i / 2 + c.val - r.val)

/-- Every legal entry of the original square matrix has an untruncated sequence index. -/
theorem negativeToeplitzMatrix_index_bound (i : ℕ) (r c : Fin ((i + 1) / 2)) :
    r.val ≤ i / 2 + c.val := by
  have := r.isLt
  omega

/-- Actual row reversal converts the original negative Toeplitz square to a negative Hankel square. -/
theorem negativeToeplitzMatrix_reverse {R : Type} [Neg R] (P : ℕ → R) (i : ℕ) :
    (negativeToeplitzMatrix P i).submatrix Fin.revPerm id =
      -(fun r c : Fin ((i + 1) / 2) => P (r.val + c.val + (1 - i % 2)) :
        Matrix (Fin ((i + 1) / 2)) (Fin ((i + 1) / 2)) R) := by
  ext r c
  change -P (i / 2 + c.val - (Fin.rev r).val) =
    -P (r.val + c.val + (1 - i % 2))
  apply congrArg (fun k : ℕ => -P k)
  have := r.isLt
  simp only [Fin.val_rev]
  omega

/-- The genuine row-permutation sign and all entrywise minus signs are retained. -/
theorem negativeToeplitzMatrix_det_reverse {R : Type} [CommRing R]
    (P : ℕ → R) (i : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin ((i + 1) / 2))) *
        (negativeToeplitzMatrix P i).det =
      (-1 : R) ^ ((i + 1) / 2) *
        Matrix.det (fun r c : Fin ((i + 1) / 2) => P (r.val + c.val + (1 - i % 2)) :
          Matrix (Fin ((i + 1) / 2)) (Fin ((i + 1) / 2)) R) := by
  let H : Matrix (Fin ((i + 1) / 2)) (Fin ((i + 1) / 2)) R :=
    fun r c => P (r.val + c.val + (1 - i % 2))
  have hr : (negativeToeplitzMatrix P i).submatrix Fin.revPerm id = -H :=
    negativeToeplitzMatrix_reverse (R := R) P i
  calc
    _ = (-H).det := (Matrix.det_permute Fin.revPerm (negativeToeplitzMatrix P i)).symm.trans
      (congrArg Matrix.det hr)
    _ = _ := by simpa only [Fintype.card_fin] using Matrix.det_neg H

end W05
