import W05.RationalTransport
import W05.ToeplitzCorner

namespace W05

/-- Uniqueness is proved directly for arbitrary rational-field solutions of the original equations. -/
theorem SatisfiesRational_unique
    (P Q : ℕ → FractionRing (MvPolynomial ℕ ℚ))
    (hP : SatisfiesRational P) (hQ : SatisfiesRational Q) : P = Q := by
  have hminor (i : ℕ) (hi : 1 ≤ i) : negativeToeplitzMinor P i = negativeToeplitzMinor Q i :=
    (hP i hi).trans (hQ i hi).symm
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 1
    · have hm := hminor (n + 1) (by omega)
      rw [negativeToeplitzMinor_first_two P n hn, negativeToeplitzMinor_first_two Q n hn] at hm
      exact hm
    · have hn2 : 2 ≤ n := by omega
      let N := (n - 2) / 2
      let s := (n - 2) % 2
      have hs : s ≤ 1 := by dsimp [s]; omega
      have hidx : n = 2 * N + 2 + s := by dsimp [N, s]; omega
      have hd := negativeToeplitzMinor_next_difference P Q N s hs
        (fun k hk => ih k (by omega))
      rw [hminor (2 * N + 3 + s) (by omega), sub_self] at hd
      have hprev : negativeToeplitzMinor P (2 * N + 1 + s) ≠ 0 := by
        have hp := hP (2 * N + 1 + s) (by omega)
        change negativeToeplitzMinor P (2 * N + 1 + s) = _ at hp
        rw [hp]
        exact rationalPrescribedMonomial_ne_zero (2 * N + 1 + s)
      have hsign : (-1 : FractionRing (MvPolynomial ℕ ℚ)) ^ (N + 2) ≠ 0 :=
        pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      have hpart : (-1 : FractionRing (MvPolynomial ℕ ℚ)) ^ (N + 2) *
          (P (2 * N + 2 + s) - Q (2 * N + 2 + s)) = 0 :=
        (mul_eq_zero.mp hd.symm).resolve_right hprev
      have hsub : P (2 * N + 2 + s) - Q (2 * N + 2 + s) = 0 :=
        (mul_eq_zero.mp hpart).resolve_left hsign
      simpa only [← hidx] using (sub_eq_zero.mp hsub)

/-- Every original rational-field solution has an integer-coefficient witness in exactly its first n+1 variables. -/
theorem SatisfiesRational_integer_prefix
    (P : ℕ → FractionRing (MvPolynomial ℕ ℚ)) (hP : SatisfiesRational P) (n : ℕ) :
    ∃ f : MvPolynomial (Fin (n + 1)) ℤ,
      P n = algebraMap (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ)
          (MvPolynomial.rename (fun j : Fin (n + 1) => j.val) f)) := by
  have heq := SatisfiesRational_unique P rationalCanonicalCandidate hP rationalCanonicalCandidate_satisfies
  rw [heq]
  exact ⟨finiteSignedJacobiCandidate n, rationalCanonicalCandidate_prefix n⟩

/-- The original rational-field core, with uniqueness and exact integer prefix witnesses for all indices. -/
theorem rational_solution_unique_with_integer_prefix :
    ∃ P : ℕ → FractionRing (MvPolynomial ℕ ℚ), SatisfiesRational P ∧
      (∀ Q : ℕ → FractionRing (MvPolynomial ℕ ℚ), SatisfiesRational Q → Q = P) ∧
      ∀ n : ℕ, ∃ f : MvPolynomial (Fin (n + 1)) ℤ,
        P n = algebraMap (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ))
          (MvPolynomial.map (Int.castRingHom ℚ)
            (MvPolynomial.rename (fun j : Fin (n + 1) => j.val) f)) := by
  refine ⟨rationalCanonicalCandidate, rationalCanonicalCandidate_satisfies, ?_, ?_⟩
  · intro Q hQ
    exact SatisfiesRational_unique Q rationalCanonicalCandidate hQ rationalCanonicalCandidate_satisfies
  · intro n
    exact ⟨finiteSignedJacobiCandidate n, rationalCanonicalCandidate_prefix n⟩

end W05
