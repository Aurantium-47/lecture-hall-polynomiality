import W05.CanonicalHankel
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators

namespace W05

/-- The actual reversing permutation has one inversion for every ordered pair of distinct positions. -/
theorem finRevPerm_sign (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) =
      (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  calc
    (∏ j : Fin n, ∏ k ∈ Finset.Iio j,
        (if Fin.revPerm k < Fin.revPerm j then 1 else -1 : ℤˣ)) =
        ∏ j : Fin n, (-1 : ℤˣ) ^ j.val := by
      apply Finset.prod_congr rfl
      intro j hj
      calc
        _ = ∏ k ∈ Finset.Iio j, (-1 : ℤˣ) := by
          apply Finset.prod_congr rfl
          intro k hk
          have hkj : k < j := Finset.mem_Iio.mp hk
          have hn : ¬ Fin.revPerm k < Fin.revPerm j := by
            change ¬ Fin.rev k < Fin.rev j
            rw [Fin.rev_lt_rev]
            exact not_lt.mpr (le_of_lt hkj)
          simp only [if_neg hn]
        _ = (-1 : ℤˣ) ^ j.val := by rw [Finset.prod_const, Fin.card_Iio]
    _ = (-1 : ℤˣ) ^ (∑ j : Fin n, j.val) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => j) n, Finset.sum_range_id]

/-- The same concrete sign formula after the integer unit is cast to any commutative ring. -/
theorem finRevPerm_sign_cast {R : Type} [CommRing R] (n : ℕ) :
    (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : R) =
      (-1 : R) ^ (n * (n - 1) / 2) := by
  rw [finRevPerm_sign]
  simp only [Units.val_pow_eq_pow_val, Units.coe_neg_one, Int.cast_pow,
    Int.cast_neg, Int.cast_one]

/-- The original scalar minor, retaining the outer negative sign as well as its negative entries. -/
def negativeToeplitzMinor {R : Type} [CommRing R] (P : ℕ → R) (i : ℕ) : R :=
  -(negativeToeplitzMatrix P i).det

/-- Uniform sequence scaling contributes the actual matrix size as exponent, even at zero scalar. -/
theorem negativeToeplitzMinor_scale {R : Type} [CommRing R]
    (a : R) (P : ℕ → R) (i : ℕ) :
    negativeToeplitzMinor (fun n => a * P n) i =
      a ^ ((i + 1) / 2) * negativeToeplitzMinor P i := by
  have hm : negativeToeplitzMatrix (fun n => a * P n) i =
      a • negativeToeplitzMatrix P i := by
    ext r c
    change -(a * P (i / 2 + c.val - r.val)) =
      a * (-P (i / 2 + c.val - r.val))
    exact (mul_neg a _).symm
  unfold negativeToeplitzMinor
  rw [hm, Matrix.det_smul, Fintype.card_fin, mul_neg]

/-- Closed sign in the original minor-to-Hankel relation, including the outer minus sign. -/
theorem negativeToeplitzMinor_hankel {R : Type} [CommRing R]
    (P : ℕ → R) (i : ℕ) :
    negativeToeplitzMinor P i =
      (-1 : R) ^ (((i + 1) / 2) * (((i + 1) / 2) - 1) / 2 + (i + 1) / 2 + 1) *
        Matrix.det (fun r c : Fin ((i + 1) / 2) => P (r.val + c.val + (1 - i % 2)) :
          Matrix (Fin ((i + 1) / 2)) (Fin ((i + 1) / 2)) R) := by
  let d := (i + 1) / 2
  let q := d * (d - 1) / 2
  let H : Matrix (Fin d) (Fin d) R := fun r c => P (r.val + c.val + (1 - i % 2))
  have h : (-1 : R) ^ q * (negativeToeplitzMatrix P i).det =
      (-1 : R) ^ d * H.det := by
    simpa only [finRevPerm_sign_cast] using negativeToeplitzMatrix_det_reverse (R := R) P i
  have hs : (-1 : R) ^ q * (-1 : R) ^ q = 1 := by
    calc
      _ = ((-1 : R) * (-1 : R)) ^ q := (mul_pow _ _ q).symm
      _ = 1 := by simp
  have hd : (negativeToeplitzMatrix P i).det =
      ((-1 : R) ^ q * (-1 : R) ^ d) * H.det := by
    calc
      _ = ((-1 : R) ^ q * (-1 : R) ^ q) * (negativeToeplitzMatrix P i).det := by
        rw [hs, one_mul]
      _ = (-1 : R) ^ q * ((-1 : R) ^ q * (negativeToeplitzMatrix P i).det) :=
        mul_assoc _ _ _
      _ = (-1 : R) ^ q * ((-1 : R) ^ d * H.det) :=
        congrArg (fun x : R => (-1 : R) ^ q * x) h
      _ = ((-1 : R) ^ q * (-1 : R) ^ d) * H.det := (mul_assoc _ _ _).symm
  change -(negativeToeplitzMatrix P i).det = (-1 : R) ^ (q + d + 1) * H.det
  rw [hd, ← pow_add, pow_succ, mul_neg_one, neg_mul]

end W05
