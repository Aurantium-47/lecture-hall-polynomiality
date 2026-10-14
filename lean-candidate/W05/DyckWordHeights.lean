import W05.DyckWalkSum
import Mathlib.Combinatorics.Enumerative.DyckWord

namespace W05

/-- The next genuine Dyck symbol extends the prefix by exactly one symbol. -/
theorem dyckStep_prefix_append (l : List DyckStep) (k : ℕ) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
      cases k with
      | zero => rfl
      | succ k =>
          have hk' : k < l.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk
          simpa only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append] using
            congrArg (List.cons a) (ih k hk')

/-- The real prefix height of a Dyck word, before symbol k. -/
def dyckHeight (p : DyckWord) (k : ℕ) : ℕ :=
  (p.toList.take k).count DyckStep.U - (p.toList.take k).count DyckStep.D

/-- Prefix nonnegativity makes the natural subtraction exact. -/
theorem dyckHeight_count_identity (p : DyckWord) (k : ℕ) :
    dyckHeight p k + (p.toList.take k).count DyckStep.D =
      (p.toList.take k).count DyckStep.U :=
  Nat.sub_add_cancel (p.count_D_le_count_U k)

theorem dyckHeight_zero (p : DyckWord) : dyckHeight p 0 = 0 := rfl

/-- Total balance gives height zero at the true word length. -/
theorem dyckHeight_length (p : DyckWord) : dyckHeight p p.toList.length = 0 := by
  simp only [dyckHeight, List.take_length, p.count_U_eq_count_D, Nat.sub_self]

/-- Every actual prefix has height at most the semilength; no cutoff premise is imposed. -/
theorem dyckHeight_le_semilength (p : DyckWord) (k : ℕ) :
    dyckHeight p k ≤ p.semilength := by
  have h := congrArg (fun l : List DyckStep => l.count DyckStep.U)
    (List.take_append_drop k p.toList)
  simp only [List.count_append] at h
  change (p.toList.take k).count DyckStep.U - (p.toList.take k).count DyckStep.D ≤
    p.toList.count DyckStep.U
  omega

/-- A real up symbol increases the prefix height by one. -/
theorem dyckHeight_up (p : DyckWord) (k : ℕ) (hk : k < p.toList.length)
    (hu : p.toList[k] = DyckStep.U) :
    dyckHeight p (k + 1) = dyckHeight p k + 1 := by
  have ht := dyckStep_prefix_append p.toList k hk
  have hU : (p.toList.take (k + 1)).count DyckStep.U =
      (p.toList.take k).count DyckStep.U + 1 := by rw [ht]; simp [hu]
  have hD : (p.toList.take (k + 1)).count DyckStep.D =
      (p.toList.take k).count DyckStep.D := by rw [ht]; simp [hu]
  have h0 := dyckHeight_count_identity p k
  have h1 := dyckHeight_count_identity p (k + 1)
  rw [hU, hD] at h1
  omega

/-- A real down symbol starts strictly above zero and decreases height by one without truncation. -/
theorem dyckHeight_down (p : DyckWord) (k : ℕ) (hk : k < p.toList.length)
    (hd : p.toList[k] = DyckStep.D) :
    0 < dyckHeight p k ∧ dyckHeight p (k + 1) + 1 = dyckHeight p k := by
  have ht := dyckStep_prefix_append p.toList k hk
  have hU : (p.toList.take (k + 1)).count DyckStep.U =
      (p.toList.take k).count DyckStep.U := by rw [ht]; simp [hd]
  have hD : (p.toList.take (k + 1)).count DyckStep.D =
      (p.toList.take k).count DyckStep.D + 1 := by rw [ht]; simp [hd]
  have h0 := dyckHeight_count_identity p k
  have h1 := dyckHeight_count_identity p (k + 1)
  rw [hU, hD] at h1
  constructor <;> omega

/-- Genuine word heights in the exact finite graph used by the verified walk sum. -/
def dyckHeightVertex {n : ℕ} (p : {p : DyckWord // p.semilength = n}) (k : ℕ) :
    Fin (2 * (n + 1)) :=
  ⟨dyckHeight p.val k, by
    have h := dyckHeight_le_semilength p.val k
    rw [p.property] at h
    omega⟩

theorem dyckHeightVertex_zero {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    dyckHeightVertex p 0 = 0 := by
  apply Fin.ext
  change dyckHeight p.val 0 = 0
  exact dyckHeight_zero p.val

/-- A semilength-n word ends at the zero vertex after exactly 2n symbols. -/
theorem dyckHeightVertex_end {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    dyckHeightVertex p (2 * n) = 0 := by
  have hl : p.val.toList.length = 2 * n := by
    have h := p.val.two_mul_semilength_eq_length
    rw [p.property] at h
    exact h.symm
  apply Fin.ext
  change dyckHeight p.val (2 * n) = 0
  rw [← hl, dyckHeight_length]

/-- Each genuine Dyck step yields an actual edge of the fixed finite path graph. -/
theorem dyckHeightVertex_adj {n : ℕ} (p : {p : DyckWord // p.semilength = n})
    (k : ℕ) (hk : k < 2 * n) :
    (SimpleGraph.pathGraph (2 * (n + 1))).Adj
      (dyckHeightVertex p k) (dyckHeightVertex p (k + 1)) := by
  have hk' : k < p.val.toList.length := by
    have hl := p.val.two_mul_semilength_eq_length
    rw [p.property] at hl
    omega
  apply SimpleGraph.pathGraph_adj.mpr
  change dyckHeight p.val k + 1 = dyckHeight p.val (k + 1) ∨
    dyckHeight p.val (k + 1) + 1 = dyckHeight p.val k
  rcases DyckStep.dichotomy (p.val.toList[k]) with hu | hd
  · exact Or.inl (dyckHeight_up p.val k hk' hu).symm
  · exact Or.inr (dyckHeight_down p.val k hk' hd).2

end W05

