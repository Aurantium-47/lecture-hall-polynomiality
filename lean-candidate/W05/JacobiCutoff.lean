import W05.FiniteHankel
import Mathlib.Data.Fin.Basic

open scoped BigOperators

namespace W05

/-- The actual Jacobi matrix also has lower bandwidth one. -/
theorem finiteJacobi_lower_band {R : Type} [Semiring R] (α : ℕ → R) (N : ℕ)
    (i j : Fin N) (hfar : j.val + 1 < i.val) : finiteJacobi α N i j = 0 := by
  have hdiag : j.val ≠ i.val := by omega
  have hup : j.val ≠ i.val + 1 := by omega
  have hdown : i.val ≠ j.val + 1 := by omega
  simp only [finiteJacobi, if_neg hdiag, if_neg hup, if_neg hdown]

/-- Enlarging a Jacobi block leaves every old entry unchanged. -/
theorem finiteJacobi_castLE {R : Type} [Semiring R] (α : ℕ → R)
    {N M : ℕ} (hNM : N ≤ M) (i j : Fin N) :
    finiteJacobi α M (Fin.castLE hNM i) (Fin.castLE hNM j) =
      finiteJacobi α N i j := by
  rfl

/-- An entry is stable when there is not enough time to reach the omitted boundary and return. -/
theorem finiteJacobi_pow_cutoff {R : Type} [Semiring R] (α : ℕ → R)
    {N M : ℕ} (hNM : N ≤ M) (p : ℕ) (i j : Fin N)
    (hcut : i.val + j.val + p < 2 * N) :
    (finiteJacobi α M ^ p) (Fin.castLE hNM i) (Fin.castLE hNM j) =
      (finiteJacobi α N ^ p) i j := by
  classical
  induction p generalizing i j with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, Fin.castLE_inj]
  | succ p ih =>
      let e : Fin N ↪ Fin M := Fin.castLEEmb hNM
      let f (k : Fin M) : R :=
        (finiteJacobi α M ^ p) (e i) k * finiteJacobi α M k (e j)
      have hsum : (∑ k : Fin M, f k) = ∑ k : Fin N, f (e k) := by
        have hrestrict : (∑ k ∈ Finset.univ.map e, f k) = ∑ k : Fin M, f k := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro k _hk hnot
          have hlarge : N ≤ k.val := by
            by_contra hn
            have hkN : k.val < N := Nat.lt_of_not_ge hn
            apply hnot
            exact Finset.mem_map.mpr ⟨⟨k.val, hkN⟩, Finset.mem_univ _, Fin.ext rfl⟩
          dsimp only [f]
          by_cases hfar : j.val + 1 < k.val
          · rw [finiteJacobi_lower_band α M k (e j) (by exact hfar), mul_zero]
          · have hreach : (e i).val + p < k.val := by
              change i.val + p < k.val
              have hj := j.isLt
              omega
            rw [pow_entry_zero_of_band (finiteJacobi α M) (finiteJacobi_band α M)
              p (e i) k hreach, zero_mul]
        rw [Finset.sum_map] at hrestrict
        exact hrestrict.symm
      simp only [pow_succ, Matrix.mul_apply]
      change (∑ k : Fin M, f k) =
        ∑ k : Fin N, (finiteJacobi α N ^ p) i k * finiteJacobi α N k j
      rw [hsum]
      apply Finset.sum_congr rfl
      intro k _hk
      dsimp only [f]
      by_cases hfar : j.val + 1 < k.val
      · rw [finiteJacobi_lower_band α M (e k) (e j) (by exact hfar),
          finiteJacobi_lower_band α N k j hfar, mul_zero, mul_zero]
      · have hkcut : i.val + k.val + p < 2 * N := by omega
        simp only [e, Fin.coe_castLEEmb]
        rw [ih i k hkcut, finiteJacobi_castLE α hNM k j]

/-- Closed power moments stabilize through degree 2m-1 in a block of size m. -/
theorem finiteJacobi_zero_moment_cutoff {R : Type} [Semiring R]
    (α : ℕ → R) (N M p : ℕ) (hNM : N ≤ M) (hp : p < 2 * (N + 1)) :
    (finiteJacobi α (M + 1) ^ p) 0 0 = (finiteJacobi α (N + 1) ^ p) 0 0 := by
  have hNM' : N + 1 ≤ M + 1 := by omega
  have hcut : (0 : Fin (N + 1)).val + (0 : Fin (N + 1)).val + p < 2 * (N + 1) := by
    simpa using hp
  have h := finiteJacobi_pow_cutoff α hNM' p (0 : Fin (N + 1)) 0 hcut
  have hz : Fin.castLE hNM' (0 : Fin (N + 1)) = (0 : Fin (M + 1)) := by
    apply Fin.ext
    simp
  simpa only [hz] using h

end W05
