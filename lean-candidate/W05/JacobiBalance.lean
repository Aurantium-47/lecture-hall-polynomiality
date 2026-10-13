import W05.FiniteJacobi

open scoped BigOperators

namespace W05

/-- The product of the first h lower-step weights, without division. -/
def jacobiDiagonalWeight {R : Type} [CommMonoid R] (α : ℕ → R) (h : ℕ) : R :=
  ∏ k ∈ Finset.range h, α (2 * k + 1) * α (2 * k + 2)

theorem jacobiDiagonalWeight_succ {R : Type} [CommMonoid R] (α : ℕ → R) (h : ℕ) :
    jacobiDiagonalWeight α (h + 1) =
      jacobiDiagonalWeight α h * (α (2 * h + 1) * α (2 * h + 2)) := by
  exact Finset.prod_range_succ _ _

/-- The actual diagonal weight matrix on a finite Jacobi block. -/
def jacobiDiagonal {R : Type} [CommSemiring R] (α : ℕ → R) (N : ℕ) :
    Matrix (Fin N) (Fin N) R :=
  Matrix.diagonal (fun h => jacobiDiagonalWeight α h.val)

/-- Detailed balance for the genuine finite Jacobi matrix; zero weights are allowed. -/
theorem finiteJacobi_mul_diagonal {R : Type} [CommSemiring R] (α : ℕ → R) (N : ℕ) :
    finiteJacobi α N * jacobiDiagonal α N =
      jacobiDiagonal α N * (finiteJacobi α N).transpose := by
  have hadj (i j : Fin N) (hup : j.val = i.val + 1) :
      finiteJacobi α N i j * jacobiDiagonalWeight α j.val =
        jacobiDiagonalWeight α i.val * finiteJacobi α N j i := by
    have hdiag : i.val ≠ j.val := by omega
    have hrevup : i.val ≠ j.val + 1 := by omega
    have hJji : finiteJacobi α N j i = α (2 * j.val - 1) * α (2 * j.val) := by
      simp only [finiteJacobi, if_neg hdiag, if_neg hrevup, if_pos hup]
    have hodd : 2 * j.val - 1 = 2 * i.val + 1 := by omega
    have heven : 2 * j.val = 2 * i.val + 2 := by omega
    rw [finiteJacobi_superdiag α N i j hup, hJji, one_mul, hodd, heven, hup,
      jacobiDiagonalWeight_succ]
  ext i j
  simp only [jacobiDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  by_cases heq : i = j
  · subst j
    exact mul_comm _ _
  by_cases hup : j.val = i.val + 1
  · exact hadj i j hup
  by_cases hdown : i.val = j.val + 1
  · calc
      finiteJacobi α N i j * jacobiDiagonalWeight α j.val =
          jacobiDiagonalWeight α j.val * finiteJacobi α N i j := mul_comm _ _
      _ = finiteJacobi α N j i * jacobiDiagonalWeight α i.val := (hadj j i hdown).symm
      _ = jacobiDiagonalWeight α i.val * finiteJacobi α N j i := mul_comm _ _
  · have hval : i.val ≠ j.val := fun h => heq (Fin.ext h)
    have hval' : j.val ≠ i.val := Ne.symm hval
    simp only [finiteJacobi, if_neg hval', if_neg hval, if_neg hup, if_neg hdown,
      zero_mul, mul_zero]

/-- The same balance identity holds at every finite power, without inverting D. -/
theorem finiteJacobi_pow_balance {R : Type} [CommSemiring R] (α : ℕ → R) (N p : ℕ) :
    finiteJacobi α N ^ p * jacobiDiagonal α N =
      jacobiDiagonal α N * (finiteJacobi α N ^ p).transpose := by
  let J := finiteJacobi α N
  let D := jacobiDiagonal α N
  have hJD : J * D = D * J.transpose := finiteJacobi_mul_diagonal α N
  have hp (q : ℕ) : J ^ q * D = D * J.transpose ^ q := by
    induction q with
    | zero => simp
    | succ q ih =>
        calc
          J ^ (q + 1) * D = (J ^ q * J) * D := by rw [pow_succ]
          _ = J ^ q * (J * D) := mul_assoc _ _ _
          _ = J ^ q * (D * J.transpose) := by rw [hJD]
          _ = (J ^ q * D) * J.transpose := (mul_assoc _ _ _).symm
          _ = (D * J.transpose ^ q) * J.transpose := by rw [ih]
          _ = D * (J.transpose ^ q * J.transpose) := mul_assoc _ _ _
          _ = D * J.transpose ^ (q + 1) := by rw [pow_succ]
  simpa only [Matrix.transpose_pow] using hp p

/-- In a positive-size block, balance with vertex zero has d_0=1. -/
theorem finiteJacobi_pow_balance_at_zero {R : Type} [CommSemiring R]
    (α : ℕ → R) (N p : ℕ) (h : Fin (N + 1)) :
    (finiteJacobi α (N + 1) ^ p) h 0 =
      jacobiDiagonalWeight α h.val * (finiteJacobi α (N + 1) ^ p) 0 h := by
  have heq := congrArg (fun M : Matrix (Fin (N + 1)) (Fin (N + 1)) R => M h 0)
    (finiteJacobi_pow_balance α (N + 1) p)
  simp only [jacobiDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.transpose_apply] at heq
  have hd0 : jacobiDiagonalWeight α (0 : Fin (N + 1)).val = 1 := by
    simp [jacobiDiagonalWeight]
  simpa only [hd0, mul_one] using heq

end W05
