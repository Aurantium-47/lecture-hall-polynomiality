import W05.DyckContraction
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

open scoped BigOperators
open Finset Function

namespace W05

/-- Structural path-graph adjacency is decidable from its exact arithmetic characterization. -/
instance pathGraphAdjDecidable (H : ℕ) : DecidableRel (SimpleGraph.pathGraph H).Adj :=
  fun u v => decidable_of_iff
    (u.val + 1 = v.val ∨ v.val + 1 = u.val) SimpleGraph.pathGraph_adj.symm

/-- The actual step matrix, expressed using structural adjacency rather than nonzero weights. -/
theorem dyckStepMatrix_eq_ite_adj {R : Type} [Semiring R]
    (α : ℕ → R) (H : ℕ) (u v : Fin H) :
    dyckStepMatrix α H u v =
      if (SimpleGraph.pathGraph H).Adj u v then
        (if v.val = u.val + 1 then 1 else α u.val) else 0 := by
  by_cases hu : v.val = u.val + 1
  · have ha : (SimpleGraph.pathGraph H).Adj u v :=
      SimpleGraph.pathGraph_adj.mpr (Or.inl hu.symm)
    simp [dyckStepMatrix, hu, ha]
  · by_cases hd : u.val = v.val + 1
    · have ha : (SimpleGraph.pathGraph H).Adj u v :=
        SimpleGraph.pathGraph_adj.mpr (Or.inr hd.symm)
      simp [dyckStepMatrix, hu, hd, ha]
    · have hn : ¬ (SimpleGraph.pathGraph H).Adj u v := by
        intro h
        rcases SimpleGraph.pathGraph_adj.mp h with hup | hdown <;> omega
      simp [dyckStepMatrix, hu, hd, hn]

/-- Weight of an actual finite path-graph walk: one for an up step, alpha at the source for a down step. -/
def dyckWalkWeight {R : Type} [Monoid R] (α : ℕ → R)
    {H : ℕ} {u v : Fin H} : (SimpleGraph.pathGraph H).Walk u v → R
  | .nil => 1
  | .cons' u v _ _ p =>
      (if v.val = u.val + 1 then 1 else α u.val) * dyckWalkWeight α p

/-- The empty structural walk has weight one, including the zero-length boundary. -/
theorem dyckWalkWeight_nil {R : Type} [Monoid R] (α : ℕ → R)
    (H : ℕ) (u : Fin H) :
    dyckWalkWeight α (SimpleGraph.Walk.nil : (SimpleGraph.pathGraph H).Walk u u) = 1 := rfl

/-- On every legal edge, the recursive directional weight agrees with the real step-matrix entry. -/
theorem dyckWalkWeight_cons {R : Type} [Semiring R] (α : ℕ → R)
    {H : ℕ} {u v w : Fin H} (h : (SimpleGraph.pathGraph H).Adj u v)
    (p : (SimpleGraph.pathGraph H).Walk v w) :
    dyckWalkWeight α (SimpleGraph.Walk.cons h p) =
      dyckStepMatrix α H u v * dyckWalkWeight α p := by
  rw [dyckStepMatrix_eq_ite_adj, if_pos h]
  rfl

/-- Enumerating all structurally legal fixed-length walks gives the real matrix power, even with zero weights. -/
theorem weightedDyckWalk_sum_eq_pow {R : Type} [Semiring R]
    (α : ℕ → R) (H p : ℕ) (u v : Fin H) :
    (∑ w ∈ (SimpleGraph.pathGraph H).finsetWalkLength p u v, dyckWalkWeight α w) =
      (dyckStepMatrix α H ^ p) u v := by
  classical
  induction p generalizing u v with
  | zero =>
      by_cases huv : u = v
      · subst v
        simp [SimpleGraph.finsetWalkLength, dyckWalkWeight]
      · simp [SimpleGraph.finsetWalkLength, huv, Matrix.one_apply]
  | succ p ih =>
      rw [SimpleGraph.finsetWalkLength, Finset.sum_biUnion]
      · simp only [Finset.sum_map, Function.Embedding.coeFn_mk, dyckWalkWeight_cons,
          ← Finset.mul_sum, ih]
        rw [pow_succ', Matrix.mul_apply]
        symm
        apply Finset.sum_congr_set ((SimpleGraph.pathGraph H).neighborSet u)
        · intro k hk
          rfl
        · intro k hk
          change ¬ (SimpleGraph.pathGraph H).Adj u k at hk
          rw [dyckStepMatrix_eq_ite_adj, if_neg hk, zero_mul]
      · rintro ⟨x, hx⟩ - ⟨y, hy⟩ - hxy
        rw [Function.onFun, disjoint_iff_inf_le]
        intro w hw
        simp only [inf_eq_inter, mem_inter, mem_map,
          Function.Embedding.coeFn_mk, exists_prop] at hw
        obtain ⟨⟨px, _, rfl⟩, ⟨py, hpy, hp⟩⟩ := hw
        cases hp
        simp at hxy

/-- The true finite closed-walk weight sum equals the previously verified canonical Jacobi moment. -/
theorem weightedDyckWalk_sum_eq_canonical {R : Type} [CommSemiring R]
    (α : ℕ → R) (n : ℕ) :
    (∑ w ∈ (SimpleGraph.pathGraph (2 * (n + 1))).finsetWalkLength
        (2 * n) (0 : Fin (2 * (n + 1))) 0, dyckWalkWeight α w) =
      canonicalJacobiMoment α n := by
  rw [weightedDyckWalk_sum_eq_pow, dyckStepMatrix_even_power_zero]

end W05

