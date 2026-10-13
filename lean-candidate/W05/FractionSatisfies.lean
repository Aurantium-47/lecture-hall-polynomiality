import W05.PolynomialSatisfies
import W05.JacobiPolynomialWitness
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Basic

namespace W05

/-- A genuine coefficient homomorphism preserves the actual negative Toeplitz scalar minor. -/
theorem negativeToeplitzMinor_map {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (P : ℕ → R) (i : ℕ) :
    f (negativeToeplitzMinor P i) = negativeToeplitzMinor (fun n => f (P n)) i := by
  have hm : f.mapMatrix (negativeToeplitzMatrix P i) =
      negativeToeplitzMatrix (fun n => f (P n)) i := by
    ext r c
    change f (-P (i / 2 + c.val - r.val)) = -f (P (i / 2 + c.val - r.val))
    exact map_neg f _
  unfold negativeToeplitzMinor
  rw [map_neg, RingHom.map_det, hm]

noncomputable section

/-- The original concrete positive-index equation family in the specified fraction field. -/
def SatisfiesFraction (P : ℕ → FractionRing (MvPolynomial ℕ ℤ)) : Prop :=
  ∀ i : ℕ, 1 ≤ i →
    -(negativeToeplitzMatrix P i).det =
      algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ)) (prescribedMonomial i)

/-- The image of the explicit polynomial candidate in the original fraction field. -/
def fractionalCanonicalCandidate (n : ℕ) : FractionRing (MvPolynomial ℕ ℤ) :=
  algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ)) (signedCanonicalCandidate n)

/-- The actual matrix and determinant homomorphism bridge proves all original fraction-field equations. -/
theorem fractionalCanonicalCandidate_satisfies : SatisfiesFraction fractionalCanonicalCandidate := by
  unfold SatisfiesFraction
  intro i hi
  change negativeToeplitzMinor
    (fun n => algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ))
      (signedCanonicalCandidate n)) i = _
  rw [← negativeToeplitzMinor_map
    (algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ))) signedCanonicalCandidate i]
  exact congrArg (algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ)))
    (signedCanonicalCandidate_satisfies i hi)

/-- The same explicit Fin(n+1) integer-polynomial witness gives the fraction-field value. -/
theorem fractionalCanonicalCandidate_prefix (n : ℕ) :
    fractionalCanonicalCandidate n =
      algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ))
        (MvPolynomial.rename (fun j : Fin (n + 1) => j.val) (finiteSignedJacobiCandidate n)) := by
  unfold fractionalCanonicalCandidate
  apply congrArg (algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ)))
  exact (signedJacobi_prefix_witness n).symm

/-- Every original prescribed monomial is nonzero, including the auxiliary empty product. -/
theorem prescribedMonomial_ne_zero (i : ℕ) : prescribedMonomial i ≠ 0 := by
  unfold prescribedMonomial
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (MvPolynomial.X_ne_zero (R := ℤ) j.val)

/-- The original prescribed monomial remains nonzero under the actual fraction-field embedding. -/
theorem prescribedMonomial_fraction_ne_zero (i : ℕ) :
    algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ)) (prescribedMonomial i) ≠ 0 := by
  intro h
  apply prescribedMonomial_ne_zero i
  apply IsFractionRing.injective (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ))
  simpa only [map_zero] using h

/-- Existence with all original equations and exact integer prefix witnesses; uniqueness is separate. -/
theorem fraction_solution_exists_with_prefix :
    ∃ P : ℕ → FractionRing (MvPolynomial ℕ ℤ), SatisfiesFraction P ∧
      ∀ n : ℕ, ∃ f : MvPolynomial (Fin (n + 1)) ℤ,
        P n = algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ))
          (MvPolynomial.rename (fun j : Fin (n + 1) => j.val) f) := by
  refine ⟨fractionalCanonicalCandidate, fractionalCanonicalCandidate_satisfies, ?_⟩
  intro n
  exact ⟨finiteSignedJacobiCandidate n, fractionalCanonicalCandidate_prefix n⟩

end
end W05
