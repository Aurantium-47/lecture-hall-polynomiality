import W05.ToeplitzSign
import W05.PrescribedProducts

namespace W05

/-- The original minor sign and the signed Hankel sign cancel without dividing by any weight. -/
theorem canonicalMinor_sign_cancel {R : Type} [CommRing R] (N : ℕ) :
    (-1 : R) ^ ((N + 1) * ((N + 1) - 1) / 2 + (N + 1) + 1) *
      (-1 : R) ^ (N * (N - 1) / 2) = 1 := by
  have ht : (N + 1) * ((N + 1) - 1) / 2 = N * (N - 1) / 2 + N := by
    rw [← Finset.sum_range_id (N + 1), Finset.sum_range_succ, Finset.sum_range_id]
  rw [ht, ← pow_add]
  have he : N * (N - 1) / 2 + N + (N + 1) + 1 + N * (N - 1) / 2 =
      2 * (N * (N - 1) / 2 + N + 1) := by omega
  rw [he, pow_mul]
  simp [pow_two]

noncomputable section

/-- The neutral polynomial candidate obtained from the actual signed canonical moments. -/
def signedCanonicalCandidate (n : ℕ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.X 0 * canonicalJacobiMoment signedJacobiWeight n

/-- The original positive-index equations in the integer polynomial ring, with the outer minus. -/
def SatisfiesPolynomial (P : ℕ → MvPolynomial ℕ ℤ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → -(negativeToeplitzMatrix P i).det = prescribedMonomial i

/-- Every odd-indexed original negative Toeplitz equation holds, including index one. -/
theorem signedCanonicalCandidate_minor_odd (N : ℕ) :
    negativeToeplitzMinor signedCanonicalCandidate (2 * N + 1) =
      prescribedMonomial (2 * N + 1) := by
  change negativeToeplitzMinor
    (fun n => (MvPolynomial.X 0 : MvPolynomial ℕ ℤ) *
      canonicalJacobiMoment signedJacobiWeight n) (2 * N + 1) = _
  rw [negativeToeplitzMinor_scale, negativeToeplitzMinor_hankel]
  have hd : (2 * N + 1 + 1) / 2 = N + 1 := by omega
  have hm : (2 * N + 1) % 2 = 1 := by omega
  rw [hd, hm]
  change (MvPolynomial.X 0 : MvPolynomial ℕ ℤ) ^ (N + 1) *
      ((-1 : MvPolynomial ℕ ℤ) ^ ((N + 1) * ((N + 1) - 1) / 2 + (N + 1) + 1) *
        (canonicalJacobiHankel signedJacobiWeight N 0).det) = prescribedMonomial (2 * N + 1)
  rw [mul_left_comm, canonicalJacobiHankel_prescribed_zero, ← mul_assoc,
    canonicalMinor_sign_cancel, one_mul]

/-- Every even positive-indexed original negative Toeplitz equation holds, including index two. -/
theorem signedCanonicalCandidate_minor_even (N : ℕ) :
    negativeToeplitzMinor signedCanonicalCandidate (2 * N + 2) =
      prescribedMonomial (2 * N + 2) := by
  change negativeToeplitzMinor
    (fun n => (MvPolynomial.X 0 : MvPolynomial ℕ ℤ) *
      canonicalJacobiMoment signedJacobiWeight n) (2 * N + 2) = _
  rw [negativeToeplitzMinor_scale, negativeToeplitzMinor_hankel]
  have hd : (2 * N + 2 + 1) / 2 = N + 1 := by omega
  have hm : (2 * N + 2) % 2 = 0 := by omega
  rw [hd, hm]
  change (MvPolynomial.X 0 : MvPolynomial ℕ ℤ) ^ (N + 1) *
      ((-1 : MvPolynomial ℕ ℤ) ^ ((N + 1) * ((N + 1) - 1) / 2 + (N + 1) + 1) *
        (canonicalJacobiHankel signedJacobiWeight N 1).det) = prescribedMonomial (2 * N + 2)
  rw [mul_left_comm, canonicalJacobiHankel_prescribed_one, ← mul_assoc,
    canonicalMinor_sign_cancel, one_mul]

/-- The polynomial candidate satisfies all of the original positive-index equations. -/
theorem signedCanonicalCandidate_satisfies : SatisfiesPolynomial signedCanonicalCandidate := by
  unfold SatisfiesPolynomial
  intro i hi
  change negativeToeplitzMinor signedCanonicalCandidate i = prescribedMonomial i
  have hm : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases hm with he | ho
  · have hn : 1 ≤ i / 2 := by omega
    have hx : i = 2 * (i / 2 - 1) + 2 := by omega
    rw [hx]
    exact signedCanonicalCandidate_minor_even (i / 2 - 1)
  · have hx : i = 2 * (i / 2) + 1 := by omega
    rw [hx]
    exact signedCanonicalCandidate_minor_odd (i / 2)

end
end W05
