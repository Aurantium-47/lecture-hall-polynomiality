import Mathlib.Data.Matrix.Mul
import Lean.Elab.Tactic.Omega

namespace W05

/-- In p steps, an upper bandwidth-one matrix cannot move more than p columns right. -/
theorem pow_entry_zero_of_band
    {R : Type} [Semiring R] {N : ℕ}
    (J : Matrix (Fin N) (Fin N) R)
    (hband : ∀ i j, i.val + 1 < j.val → J i j = 0)
    (p : ℕ) (i j : Fin N) (hfar : i.val + p < j.val) :
    (J ^ p) i j = 0 := by
  induction p generalizing i j with
  | zero =>
      have hij : i ≠ j := by
        intro heq
        have hv := congrArg Fin.val heq
        omega
      simpa only [pow_zero] using (Matrix.one_apply_ne hij : (1 : Matrix (Fin N) (Fin N) R) i j = 0)
  | succ p ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro b _hb
      by_cases hleft : i.val + p < b.val
      · rw [ih i b hleft, zero_mul]
      · have hright : b.val + 1 < j.val := by omega
        rw [hband b j hright, mul_zero]

/-- At maximal displacement every step uses the unit upper neighboring entry. -/
theorem pow_entry_maximal_displacement
    {R : Type} [Semiring R] {N : ℕ}
    (J : Matrix (Fin N) (Fin N) R)
    (hband : ∀ i j, i.val + 1 < j.val → J i j = 0)
    (hup : ∀ i j, j.val = i.val + 1 → J i j = 1)
    (p : ℕ) (i j : Fin N) (hfar : j.val = i.val + p) :
    (J ^ p) i j = 1 := by
  induction p generalizing i j with
  | zero =>
      have hij : i = j := Fin.ext (by omega)
      subst j
      simp only [pow_zero, Matrix.one_apply_eq]
  | succ p ih =>
      let b : Fin N := ⟨i.val + p, by omega⟩
      have hb : b.val = i.val + p := rfl
      have hbj : j.val = b.val + 1 := by omega
      rw [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_eq_single b]
      · rw [ih i b hb, hup b j hbj, one_mul]
      · intro c _hc hcb
        by_cases hlow : c.val < b.val
        · have hcj : c.val + 1 < j.val := by omega
          rw [hband c j hcj, mul_zero]
        · have hne : c.val ≠ b.val := fun heq => hcb (Fin.ext heq)
          have hic : i.val + p < c.val := by omega
          rw [pow_entry_zero_of_band J hband p i c hic, zero_mul]
      · intro hbnot
        exact False.elim (hbnot (Finset.mem_univ b))

end W05
