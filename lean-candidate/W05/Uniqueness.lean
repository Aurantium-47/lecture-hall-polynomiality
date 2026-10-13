import W05.ToeplitzCorner

namespace W05

/-- The concrete original fraction-field equations determine every sequence entry uniquely. -/
theorem SatisfiesFraction_unique
    (P Q : ℕ → FractionRing (MvPolynomial ℕ ℤ))
    (hP : SatisfiesFraction P) (hQ : SatisfiesFraction Q) : P = Q := by
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
        exact prescribedMonomial_fraction_ne_zero (2 * N + 1 + s)
      have hsign : (-1 : FractionRing (MvPolynomial ℕ ℤ)) ^ (N + 2) ≠ 0 :=
        pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      have hpart : (-1 : FractionRing (MvPolynomial ℕ ℤ)) ^ (N + 2) *
          (P (2 * N + 2 + s) - Q (2 * N + 2 + s)) = 0 :=
        (mul_eq_zero.mp hd.symm).resolve_right hprev
      have hsub : P (2 * N + 2 + s) - Q (2 * N + 2 + s) = 0 :=
        (mul_eq_zero.mp hpart).resolve_left hsign
      simpa only [← hidx] using (sub_eq_zero.mp hsub)

/-- Every solution of the original equations is the explicit canonical fraction-field candidate. -/
theorem fractionalCanonicalCandidate_unique
    (P : ℕ → FractionRing (MvPolynomial ℕ ℤ)) (hP : SatisfiesFraction P) :
    P = fractionalCanonicalCandidate :=
  SatisfiesFraction_unique P fractionalCanonicalCandidate hP fractionalCanonicalCandidate_satisfies

/-- Every original solution, not just the constructed one, has exact integer prefix witnesses. -/
theorem SatisfiesFraction_integer_prefix
    (P : ℕ → FractionRing (MvPolynomial ℕ ℤ)) (hP : SatisfiesFraction P) (n : ℕ) :
    ∃ f : MvPolynomial (Fin (n + 1)) ℤ,
      P n = algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ))
        (MvPolynomial.rename (fun j : Fin (n + 1) => j.val) f) := by
  rw [fractionalCanonicalCandidate_unique P hP]
  exact ⟨finiteSignedJacobiCandidate n, fractionalCanonicalCandidate_prefix n⟩

/-- The original core: a unique solution of all equations, with all-index integer prefix polynomiality. -/
theorem fraction_solution_unique_with_prefix :
    ∃ P : ℕ → FractionRing (MvPolynomial ℕ ℤ), SatisfiesFraction P ∧
      (∀ Q : ℕ → FractionRing (MvPolynomial ℕ ℤ), SatisfiesFraction Q → Q = P) ∧
      ∀ n : ℕ, ∃ f : MvPolynomial (Fin (n + 1)) ℤ,
        P n = algebraMap (MvPolynomial ℕ ℤ) (FractionRing (MvPolynomial ℕ ℤ))
          (MvPolynomial.rename (fun j : Fin (n + 1) => j.val) f) := by
  refine ⟨fractionalCanonicalCandidate, fractionalCanonicalCandidate_satisfies, ?_, ?_⟩
  · intro Q hQ
    exact fractionalCanonicalCandidate_unique Q hQ
  · intro n
    exact ⟨finiteSignedJacobiCandidate n, fractionalCanonicalCandidate_prefix n⟩

end W05
