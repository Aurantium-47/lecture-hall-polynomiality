import W05.FractionSatisfies

open scoped BigOperators

namespace W05

noncomputable section

/-- The actual natural coefficient map from integer polynomials to the rational-polynomial fraction field. -/
def integerPolynomialToRationalField :
    MvPolynomial ℕ ℤ →+* FractionRing (MvPolynomial ℕ ℚ) :=
  (algebraMap (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ))).comp
    (MvPolynomial.map (Int.castRingHom ℚ))

/-- The prescribed monomial expressed directly in the free variables of the original rational field. -/
def rationalPrescribedMonomial (i : ℕ) : FractionRing (MvPolynomial ℕ ℚ) :=
  ∏ j : Fin i,
    algebraMap (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ))
      (MvPolynomial.X j.val) ^ (i - j.val)

/-- The natural coefficient map takes the integer prescribed monomial to the actual rational free-variable one. -/
theorem rationalPrescribedMonomial_map (i : ℕ) :
    integerPolynomialToRationalField (prescribedMonomial i) = rationalPrescribedMonomial i := by
  unfold integerPolynomialToRationalField prescribedMonomial rationalPrescribedMonomial
  simp only [RingHom.comp_apply, map_prod, map_pow, MvPolynomial.map_X]

/-- The actual rational free-variable prescribed monomials are nonzero without an extra premise. -/
theorem rationalPrescribedMonomial_ne_zero (i : ℕ) : rationalPrescribedMonomial i ≠ 0 := by
  unfold rationalPrescribedMonomial
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply pow_ne_zero
  intro hx
  apply MvPolynomial.X_ne_zero (R := ℚ) j.val
  apply IsFractionRing.injective (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ))
  simpa only [map_zero] using hx

/-- The original concrete equation family in the fraction field of rational-coefficient polynomials. -/
def SatisfiesRational (P : ℕ → FractionRing (MvPolynomial ℕ ℚ)) : Prop :=
  ∀ i : ℕ, 1 ≤ i → -(negativeToeplitzMatrix P i).det = rationalPrescribedMonomial i

/-- The explicit canonical candidate after the natural integer-to-rational coefficient map. -/
def rationalCanonicalCandidate (n : ℕ) : FractionRing (MvPolynomial ℕ ℚ) :=
  integerPolynomialToRationalField (signedCanonicalCandidate n)

/-- Actual matrix/minor homomorphism compatibility proves every original equation in the rational field. -/
theorem rationalCanonicalCandidate_satisfies : SatisfiesRational rationalCanonicalCandidate := by
  unfold SatisfiesRational
  intro i hi
  have h := congrArg integerPolynomialToRationalField (signedCanonicalCandidate_satisfies i hi)
  change integerPolynomialToRationalField (negativeToeplitzMinor signedCanonicalCandidate i) =
    integerPolynomialToRationalField (prescribedMonomial i) at h
  rw [negativeToeplitzMinor_map integerPolynomialToRationalField signedCanonicalCandidate i,
    rationalPrescribedMonomial_map] at h
  exact h

/-- The same explicit integer Fin(n+1) witness, with coefficient inclusion and variable inclusion both visible. -/
theorem rationalCanonicalCandidate_prefix (n : ℕ) :
    rationalCanonicalCandidate n =
      algebraMap (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ)
          (MvPolynomial.rename (fun j : Fin (n + 1) => j.val) (finiteSignedJacobiCandidate n))) := by
  change integerPolynomialToRationalField (signedCanonicalCandidate n) =
    integerPolynomialToRationalField
      (MvPolynomial.rename (fun j : Fin (n + 1) => j.val) (finiteSignedJacobiCandidate n))
  exact congrArg integerPolynomialToRationalField (signedJacobi_prefix_witness n).symm

end
end W05
