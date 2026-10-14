import W05.JacobiBidiagonal
import W05.JacobiMoments
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators

namespace W05

/-- A genuine single up/down step on the finite nonnegative heights, weighted at descent source. -/
def dyckStepMatrix {R : Type} [Semiring R] (α : ℕ → R) (H : ℕ) :
    Matrix (Fin H) (Fin H) R := fun u v =>
  if v.val = u.val + 1 then 1
  else if u.val = v.val + 1 then α u.val else 0

/-- Even heights in a cutoff retaining the top odd height. -/
def evenHeight (N : ℕ) (i : Fin (N + 1)) : Fin (2 * (N + 1)) :=
  ⟨2 * i.val, by omega⟩

/-- Odd heights in the same finite cutoff. -/
def oddHeight (N : ℕ) (i : Fin (N + 1)) : Fin (2 * (N + 1)) :=
  ⟨2 * i.val + 1, by omega⟩

/-- Exact finite reindexing into even and odd heights. -/
theorem sum_dyck_even_odd {R : Type} [AddCommMonoid R] (N : ℕ)
    (f : Fin (2 * (N + 1)) → R) :
    (∑ k, f k) = ∑ i : Fin (N + 1), (f (evenHeight N i) + f (oddHeight N i)) := by
  let e : Fin (N + 1) × Fin 2 ≃ Fin (2 * (N + 1)) :=
    finProdFinEquiv.trans (finCongr (by omega))
  calc
    (∑ k, f k) = ∑ x : Fin (N + 1) × Fin 2, f (e x) :=
      (Fintype.sum_equiv e (fun x => f (e x)) f (fun _ => rfl)).symm
    _ = ∑ i : Fin (N + 1), (f (e (i, 0)) + f (e (i, 1))) := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have h0 : e (i, 0) = evenHeight N i := by
        apply Fin.ext
        change 0 + 2 * i.val = 2 * i.val
        omega
      have h1 : e (i, 1) = oddHeight N i := by
        apply Fin.ext
        change 1 + 2 * i.val = 2 * i.val + 1
        omega
      rw [h0, h1]

/-- A single legal step changes the parity of the height. -/
theorem dyckStepMatrix_same_parity_zero {R : Type} [Semiring R]
    (α : ℕ → R) (H : ℕ) (i j : Fin H) (h : i.val % 2 = j.val % 2) :
    dyckStepMatrix α H i j = 0 := by
  simp only [dyckStepMatrix]
  split_ifs <;> first | omega | rfl

/-- The even-to-odd step block is the already defined lower bidiagonal matrix. -/
theorem dyckStepMatrix_even_odd {R : Type} [Semiring R]
    (α : ℕ → R) (N : ℕ) (i j : Fin (N + 1)) :
    dyckStepMatrix α (2 * (N + 1)) (evenHeight N i) (oddHeight N j) =
      jacobiLowerBidiagonal α (N + 1) i j := by
  have hdiag : (2 * j.val + 1 = 2 * i.val + 1) ↔ i = j := by
    constructor
    · intro h
      apply Fin.ext
      omega
    · rintro rfl
      rfl
  have hdown : (2 * i.val = (2 * j.val + 1) + 1) ↔ i.val = j.val + 1 := by omega
  simp only [dyckStepMatrix, evenHeight, oddHeight, Fin.val_mk,
    jacobiLowerBidiagonal, Matrix.add_apply, Matrix.one_apply, hdiag, hdown]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- The odd-to-even step block is the already defined upper bidiagonal matrix. -/
theorem dyckStepMatrix_odd_even {R : Type} [Semiring R]
    (α : ℕ → R) (N : ℕ) (i j : Fin (N + 1)) :
    dyckStepMatrix α (2 * (N + 1)) (oddHeight N i) (evenHeight N j) =
      jacobiUpperBidiagonal α (N + 1) i j := by
  have hup : (2 * j.val = (2 * i.val + 1) + 1) ↔ j.val = i.val + 1 := by omega
  have hdown : (2 * i.val + 1 = 2 * j.val + 1) ↔ j.val = i.val := by omega
  simp only [dyckStepMatrix, evenHeight, oddHeight, Fin.val_mk,
    jacobiUpperBidiagonal, hup, hdown]
  by_cases hdiag : j.val = i.val
  · have hne : j.val ≠ i.val + 1 := by omega
    simp [hdiag, hne]
  · simp [hdiag]

/-- Two actual up/down steps contract exactly to the existing finite Jacobi matrix. -/
theorem dyckStepMatrix_sq_even {R : Type} [CommSemiring R]
    (α : ℕ → R) (N : ℕ) (i j : Fin (N + 1)) :
    (dyckStepMatrix α (2 * (N + 1)) ^ 2) (evenHeight N i) (evenHeight N j) =
      finiteJacobi α (N + 1) i j := by
  rw [pow_two, Matrix.mul_apply, sum_dyck_even_odd,
    finiteJacobi_bidiagonal_factorization, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hz := dyckStepMatrix_same_parity_zero α (2 * (N + 1))
    (evenHeight N i) (evenHeight N k) (by simp only [evenHeight, Fin.val_mk]; omega)
  rw [hz, zero_mul, zero_add, dyckStepMatrix_even_odd, dyckStepMatrix_odd_even]

/-- Two actual up/down steps cannot connect heights of opposite parity. -/
theorem dyckStepMatrix_sq_parity {R : Type} [Semiring R]
    (α : ℕ → R) (H : ℕ) (i j : Fin H) (h : i.val % 2 ≠ j.val % 2) :
    (dyckStepMatrix α H ^ 2) i j = 0 := by
  rw [pow_two, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [dyckStepMatrix]
  split_ifs <;> first | omega | simp

/-- All even powers on even heights equal the powers of the unchanged Jacobi matrix. -/
theorem dyckStepMatrix_even_power {R : Type} [CommSemiring R]
    (α : ℕ → R) (N p : ℕ) (i j : Fin (N + 1)) :
    (dyckStepMatrix α (2 * (N + 1)) ^ (2 * p)) (evenHeight N i) (evenHeight N j) =
      (finiteJacobi α (N + 1) ^ p) i j := by
  induction p generalizing i j with
  | zero =>
      have he : evenHeight N i = evenHeight N j ↔ i = j := by
        constructor
        · intro h
          apply Fin.ext
          have hv := congrArg Fin.val h
          dsimp [evenHeight] at hv
          omega
        · rintro rfl
          rfl
      simp only [Nat.mul_zero, pow_zero, Matrix.one_apply, he]
  | succ p ih =>
      rw [show 2 * (p + 1) = 2 * p + 2 by omega, pow_add,
        Matrix.mul_apply, sum_dyck_even_odd]
      conv_rhs => rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k hk
      have hz := dyckStepMatrix_sq_parity α (2 * (N + 1))
        (oddHeight N k) (evenHeight N j) (by
          simp only [oddHeight, evenHeight, Fin.val_mk]
          omega)
      rw [hz, mul_zero, add_zero, ih i k, dyckStepMatrix_sq_even]

/-- The finite single-step matrix gives the current canonical moment at the exact even power. -/
theorem dyckStepMatrix_even_power_zero {R : Type} [CommSemiring R]
    (α : ℕ → R) (n : ℕ) :
    (dyckStepMatrix α (2 * (n + 1)) ^ (2 * n)) 0 0 =
      canonicalJacobiMoment α n := by
  have h := dyckStepMatrix_even_power α n n 0 0
  simpa only [evenHeight, Fin.val_zero, Nat.mul_zero, canonicalJacobiMoment] using h

end W05

