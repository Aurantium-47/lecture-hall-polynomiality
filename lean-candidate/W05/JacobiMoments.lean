import W05.JacobiCutoff

open scoped BigOperators

namespace W05

/-- A canonical finite Jacobi moment, not yet identified with the original defining sequence. -/
def canonicalJacobiMoment {R : Type} [Semiring R] (α : ℕ → R) (p : ℕ) : R :=
  (finiteJacobi α (p + 1) ^ p) 0 0

theorem canonicalJacobiMoment_zero {R : Type} [Semiring R] (α : ℕ → R) :
    canonicalJacobiMoment α 0 = 1 := by
  simp only [canonicalJacobiMoment, pow_zero, Matrix.one_apply_eq]

/-- The canonical moment agrees with every block large enough for a closed p-step entry. -/
theorem canonicalJacobiMoment_eq_block {R : Type} [Semiring R] (α : ℕ → R)
    (N p : ℕ) (hp : p < 2 * (N + 1)) :
    canonicalJacobiMoment α p = (finiteJacobi α (N + 1) ^ p) 0 0 := by
  unfold canonicalJacobiMoment
  by_cases hNp : N ≤ p
  · exact finiteJacobi_zero_moment_cutoff α N p p hNp hp
  · have hpN : p ≤ N := by omega
    exact (finiteJacobi_zero_moment_cutoff α p N p hpN (by omega)).symm

/-- A single legal Jacobi step only uses weights with positive index at most i+j+1. -/
theorem finiteJacobi_entry_weights_congr {R : Type} [Semiring R]
    (α β : ℕ → R) (N : ℕ) (i j : Fin N)
    (hw : ∀ h : ℕ, 1 ≤ h → h ≤ i.val + j.val + 1 → α h = β h) :
    finiteJacobi α N i j = finiteJacobi β N i j := by
  by_cases hdiag : j.val = i.val
  · by_cases hi0 : i.val = 0
    · simpa only [finiteJacobi, if_pos hdiag, if_pos hi0] using
        hw 1 (by omega) (by omega)
    · simp only [finiteJacobi, if_pos hdiag, if_neg hi0]
      exact congrArg₂ (fun a b : R => a + b)
        (hw (2 * i.val) (by omega) (by omega))
        (hw (2 * i.val + 1) (by omega) (by omega))
  · by_cases hup : j.val = i.val + 1
    · simp only [finiteJacobi, if_neg hdiag, if_pos hup]
    · by_cases hdown : i.val = j.val + 1
      · simp only [finiteJacobi, if_neg hdiag, if_neg hup, if_pos hdown]
        exact congrArg₂ (fun a b : R => a * b)
          (hw (2 * i.val - 1) (by omega) (by omega))
          (hw (2 * i.val) (by omega) (by omega))
      · simp only [finiteJacobi, if_neg hdiag, if_neg hup, if_neg hdown]

/-- Finite powers depend only on the weights allowed by the endpoints and the number of steps. -/
theorem finiteJacobi_pow_weights_congr {R : Type} [Semiring R]
    (α β : ℕ → R) (N p : ℕ) (i j : Fin N)
    (hw : ∀ h : ℕ, 1 ≤ h → h ≤ i.val + j.val + p → α h = β h) :
    (finiteJacobi α N ^ p) i j = (finiteJacobi β N ^ p) i j := by
  induction p generalizing i j with
  | zero => simp only [pow_zero]
  | succ p ih =>
      simp only [pow_succ, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases hfar : j.val + 1 < k.val
      · rw [finiteJacobi_lower_band α N k j hfar,
          finiteJacobi_lower_band β N k j hfar, mul_zero, mul_zero]
      · by_cases hreach : i.val + p < k.val
        · rw [pow_entry_zero_of_band (finiteJacobi α N) (finiteJacobi_band α N) p i k hreach,
            pow_entry_zero_of_band (finiteJacobi β N) (finiteJacobi_band β N) p i k hreach,
            zero_mul, zero_mul]
        · have hprev : ∀ h : ℕ, 1 ≤ h → h ≤ i.val + k.val + p → α h = β h := by
            intro h hh hle
            exact hw h hh (by omega)
          have hlast : ∀ h : ℕ, 1 ≤ h → h ≤ k.val + j.val + 1 → α h = β h := by
            intro h hh hle
            exact hw h hh (by omega)
          exact congrArg₂ (fun a b : R => a * b) (ih i k hprev)
            (finiteJacobi_entry_weights_congr α β N k j hlast)

/-- A closed p-th canonical moment only depends on alpha_1 through alpha_p, including p=0. -/
theorem canonicalJacobiMoment_weights_congr {R : Type} [Semiring R]
    (α β : ℕ → R) (p : ℕ)
    (hw : ∀ h : ℕ, 1 ≤ h → h ≤ p → α h = β h) :
    canonicalJacobiMoment α p = canonicalJacobiMoment β p := by
  unfold canonicalJacobiMoment
  apply finiteJacobi_pow_weights_congr α β (p + 1) p 0 0
  intro h hh hle
  exact hw h hh (by simpa using hle)

end W05
