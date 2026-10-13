import W05.JacobiMoments
import Mathlib.Algebra.MvPolynomial.Rename

namespace W05

noncomputable section

/-- Applying a coefficient homomorphism preserves the actual finite Jacobi matrix. -/
theorem finiteJacobi_map {R S : Type} [Semiring R] [Semiring S]
    (f : R →+* S) (α : ℕ → R) (N : ℕ) :
    f.mapMatrix (finiteJacobi α N) = finiteJacobi (fun h => f (α h)) N := by
  ext i j
  change f (finiteJacobi α N i j) = finiteJacobi (fun h => f (α h)) N i j
  simp only [finiteJacobi, apply_ite, map_add, map_mul, map_one, map_zero]

/-- The canonical moment is natural under a genuine coefficient ring homomorphism. -/
theorem canonicalJacobiMoment_map {R S : Type} [Semiring R] [Semiring S]
    (f : R →+* S) (α : ℕ → R) (p : ℕ) :
    f (canonicalJacobiMoment α p) = canonicalJacobiMoment (fun h => f (α h)) p := by
  have hp := map_pow
    (f.mapMatrix : Matrix (Fin (p + 1)) (Fin (p + 1)) R →+*
      Matrix (Fin (p + 1)) (Fin (p + 1)) S)
    (finiteJacobi α (p + 1)) p
  rw [finiteJacobi_map f α (p + 1)] at hp
  have heq := congrArg (fun M : Matrix (Fin (p + 1)) (Fin (p + 1)) S => M 0 0) hp
  exact heq

/-- The signed weights from the source, with X_j representing y_(j+1); alpha_0 is unused. -/
def signedJacobiWeight (h : ℕ) : MvPolynomial ℕ ℤ :=
  if h = 0 then 0 else
    MvPolynomial.C (if 4 ≤ h ∧ Even h then (-1 : ℤ) else 1) *
      MvPolynomial.X (h - 1) * MvPolynomial.X h

/-- A weight in exactly the first p+1 variables; higher positive weights are set to zero. -/
def finiteSignedJacobiWeight (p h : ℕ) : MvPolynomial (Fin (p + 1)) ℤ :=
  if hh : 1 ≤ h ∧ h ≤ p then
    MvPolynomial.C (if 4 ≤ h ∧ Even h then (-1 : ℤ) else 1) *
      MvPolynomial.X ⟨h - 1, by omega⟩ * MvPolynomial.X ⟨h, by omega⟩
  else 0

/-- The prescribed initial weights agree after the exact prefix-variable rename. -/
theorem rename_finiteSignedJacobiWeight (p h : ℕ) (hpos : 1 ≤ h) (hle : h ≤ p) :
    MvPolynomial.rename (fun i : Fin (p + 1) => i.val) (finiteSignedJacobiWeight p h) =
      signedJacobiWeight h := by
  have hh : 1 ≤ h ∧ h ≤ p := ⟨hpos, hle⟩
  have hn : h ≠ 0 := by omega
  simp only [finiteSignedJacobiWeight, dif_pos hh, signedJacobiWeight, if_neg hn,
    map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]

/-- An explicit integer polynomial witness in the specified prefix of variables. -/
def finiteSignedJacobiCandidate (p : ℕ) : MvPolynomial (Fin (p + 1)) ℤ :=
  MvPolynomial.X (0 : Fin (p + 1)) *
    canonicalJacobiMoment (finiteSignedJacobiWeight p) p

theorem finiteSignedJacobiCandidate_zero :
    finiteSignedJacobiCandidate 0 = (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℤ) := by
  simp only [finiteSignedJacobiCandidate, canonicalJacobiMoment_zero, mul_one]

/-- The exact prefix witness maps to the full-variable signed canonical candidate. -/
theorem signedJacobi_prefix_witness (p : ℕ) :
    MvPolynomial.rename (fun i : Fin (p + 1) => i.val) (finiteSignedJacobiCandidate p) =
      MvPolynomial.X 0 * canonicalJacobiMoment signedJacobiWeight p := by
  have hm :
      MvPolynomial.rename (fun i : Fin (p + 1) => i.val)
          (canonicalJacobiMoment (finiteSignedJacobiWeight p) p) =
        canonicalJacobiMoment signedJacobiWeight p := by
    calc
      _ = canonicalJacobiMoment
          (fun h => MvPolynomial.rename (fun i : Fin (p + 1) => i.val)
            (finiteSignedJacobiWeight p h)) p :=
        canonicalJacobiMoment_map
          (MvPolynomial.rename (fun i : Fin (p + 1) => i.val) :
            MvPolynomial (Fin (p + 1)) ℤ →ₐ[ℤ] MvPolynomial ℕ ℤ).toRingHom
          (finiteSignedJacobiWeight p) p
      _ = canonicalJacobiMoment signedJacobiWeight p := by
        apply canonicalJacobiMoment_weights_congr
        intro h hpos hle
        exact rename_finiteSignedJacobiWeight p h hpos hle
  simp only [finiteSignedJacobiCandidate, map_mul, MvPolynomial.rename_X, Fin.val_zero, hm]

end
end W05
