import W05.DyckWeight
import W05.RationalCore

open scoped BigOperators

namespace W05

noncomputable section

/-- The actual finite sum of direct descending-step products over all genuine semilength-n Dyck words. -/
def dyckMoment {R : Type} [CommSemiring R] (α : ℕ → R) (n : ℕ) : R :=
  ∑ p : {p : DyckWord // p.semilength = n}, dyckWeight α p.val

/-- The proved structural equivalence and direct weight preservation identify the true Dyck moment. -/
theorem dyckMoment_eq_canonical {R : Type} [CommSemiring R] (α : ℕ → R) (n : ℕ) :
    dyckMoment α n = canonicalJacobiMoment α n := by
  classical
  unfold dyckMoment
  calc
    (∑ p : {p : DyckWord // p.semilength = n}, dyckWeight α p.val) =
        ∑ w : {w : (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0 //
          w.length = 2 * n}, dyckWalkWeight α w.val :=
      Fintype.sum_equiv (dyckWordWalkEquiv n) _ _ (fun p => (dyckToWalk_weight α p).symm)
    _ = ∑ w ∈ (SimpleGraph.pathGraph (2 * (n + 1))).finsetWalkLength
          (2 * n) (0 : Fin (2 * (n + 1))) 0, dyckWalkWeight α w := by
      symm
      exact Finset.sum_subtype
        (p := fun w : (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0 => w.length = 2 * n)
        ((SimpleGraph.pathGraph (2 * (n + 1))).finsetWalkLength (2 * n) 0 0)
        (fun _ => SimpleGraph.mem_finsetWalkLength_iff) (dyckWalkWeight α)
    _ = canonicalJacobiMoment α n := weightedDyckWalk_sum_eq_canonical α n

/-- Semilength zero has the required moment one. -/
theorem dyckMoment_zero {R : Type} [CommSemiring R] (α : ℕ → R) :
    dyckMoment α 0 = 1 := by
  rw [dyckMoment_eq_canonical, canonicalJacobiMoment_zero]

/-- The true Dyck moment is independent of the unused height-zero weight. -/
theorem dyckMoment_congr {R : Type} [CommSemiring R] (α β : ℕ → R)
    (h : ∀ j : ℕ, 0 < j → α j = β j) (n : ℕ) :
    dyckMoment α n = dyckMoment β n := by
  unfold dyckMoment
  apply Finset.sum_congr rfl
  intro p hp
  exact dyckWeight_congr α β h p.val

/-- The original signed identification, including the exterior factor X0 corresponding to y1. -/
theorem signedCanonicalCandidate_eq_dyck (n : ℕ) :
    signedCanonicalCandidate n = MvPolynomial.X 0 * dyckMoment signedJacobiWeight n := by
  rw [dyckMoment_eq_canonical]
  rfl

/-- Every solution of the actual original rational-field equations has the same signed Dyck expression. -/
theorem SatisfiesRational_dyck
    (P : ℕ → FractionRing (MvPolynomial ℕ ℚ)) (hP : SatisfiesRational P) (n : ℕ) :
    P n = integerPolynomialToRationalField
      (MvPolynomial.X 0 * dyckMoment signedJacobiWeight n) := by
  have heq := SatisfiesRational_unique P rationalCanonicalCandidate hP
    rationalCanonicalCandidate_satisfies
  rw [heq]
  unfold rationalCanonicalCandidate
  rw [signedCanonicalCandidate_eq_dyck]

end

end W05

