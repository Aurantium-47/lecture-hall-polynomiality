import W05.BandedPowers
import Mathlib.LinearAlgebra.Matrix.Block

namespace W05

/-- The finite Jacobi matrix from the Dyck-to-Motzkin contraction, with its height-zero case. -/
def finiteJacobi {R : Type} [Semiring R] (α : ℕ → R) (N : ℕ) :
    Matrix (Fin N) (Fin N) R := fun i j =>
  if j.val = i.val then
    if i.val = 0 then α 1 else α (2 * i.val) + α (2 * i.val + 1)
  else if j.val = i.val + 1 then 1
  else if i.val = j.val + 1 then α (2 * i.val - 1) * α (2 * i.val)
  else 0

/-- The actual Jacobi definition satisfies the bandwidth hypothesis. -/
theorem finiteJacobi_band {R : Type} [Semiring R] (α : ℕ → R) (N : ℕ)
    (i j : Fin N) (hfar : i.val + 1 < j.val) : finiteJacobi α N i j = 0 := by
  have hdiag : j.val ≠ i.val := by omega
  have hup : j.val ≠ i.val + 1 := by omega
  have hdown : i.val ≠ j.val + 1 := by omega
  simp only [finiteJacobi, if_neg hdiag, if_neg hup, if_neg hdown]

/-- Every legal upper neighboring entry of the actual matrix is one. -/
theorem finiteJacobi_superdiag {R : Type} [Semiring R] (α : ℕ → R) (N : ℕ)
    (i j : Fin N) (hup : j.val = i.val + 1) : finiteJacobi α N i j = 1 := by
  have hdiag : j.val ≠ i.val := by omega
  simp only [finiteJacobi, if_neg hdiag, if_pos hup]

/-- The first rows of powers of the actual positive-size finite Jacobi matrix. -/
def jacobiPowerRows {R : Type} [Semiring R] (α : ℕ → R) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R := fun i h =>
  (finiteJacobi α (N + 1) ^ i.val) (0 : Fin (N + 1)) h

/-- Finite propagation and the unique all-up walk make these power rows unit lower triangular. -/
theorem jacobiPowerRows_unit_lower {R : Type} [Semiring R] (α : ℕ → R) (N : ℕ) :
    (∀ i h : Fin (N + 1), i < h → jacobiPowerRows α N i h = 0) ∧
      (∀ i : Fin (N + 1), jacobiPowerRows α N i i = 1) := by
  constructor
  · intro i h hih
    exact pow_entry_zero_of_band (finiteJacobi α (N + 1))
      (finiteJacobi_band α (N + 1)) i.val 0 h (by simpa using hih)
  · intro i
    exact pow_entry_maximal_displacement (finiteJacobi α (N + 1))
      (finiteJacobi_band α (N + 1)) (finiteJacobi_superdiag α (N + 1)) i.val 0 i (by simp)

/-- The power-row matrix L, rather than the Jacobi matrix J, has determinant one. -/
theorem jacobiPowerRows_det_one {R : Type} [CommRing R] (α : ℕ → R) (N : ℕ) :
    (jacobiPowerRows α N).det = 1 := by
  have hu := jacobiPowerRows_unit_lower α N
  have htri : (jacobiPowerRows α N).BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact hu.1 i j hij
  rw [Matrix.det_of_lowerTriangular (jacobiPowerRows α N) htri]
  simp only [hu.2, Finset.prod_const_one]

end W05
