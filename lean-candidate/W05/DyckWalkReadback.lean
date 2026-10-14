import W05.WalkDyckDecoding

namespace W05

/-- Ordinary walks are determined by their length and ordered vertices; revisits are allowed. -/
theorem pathWalk_eq_of_getVert {H : ℕ} {u v : Fin H}
    (p q : (SimpleGraph.pathGraph H).Walk u v)
    (hlen : p.length = q.length) (hverts : ∀ k : ℕ, p.getVert k = q.getVert k) :
    p = q := by
  revert q
  induction p with
  | nil =>
      intro q hlen hverts
      have hq : q.length = 0 := by simpa only [SimpleGraph.Walk.length_nil] using hlen.symm
      exact (SimpleGraph.Walk.length_eq_zero_iff.mp hq).symm
  | @cons u x v hp p ih =>
      intro q hlen hverts
      cases q with
      | nil =>
          simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hlen
          omega
      | @cons _ y _ hq q =>
          have hxy : x = y := by
            simpa only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero] using hverts 1
          cases hxy
          have hl : p.length = q.length := by
            simp only [SimpleGraph.Walk.length_cons] at hlen
            omega
          have hv : ∀ k : ℕ, p.getVert k = q.getVert k := by
            intro k
            simpa only [SimpleGraph.Walk.getVert_cons_succ] using hverts (k + 1)
          have he := ih q hl hv
          cases he
          rfl

/-- The decoded up/down symbols determine a real walk with its fixed endpoints. -/
theorem walkDyckSteps_injective {H : ℕ} {u v : Fin H} :
    Function.Injective (walkDyckSteps : (SimpleGraph.pathGraph H).Walk u v → List DyckStep) := by
  intro p q hs
  apply pathWalk_eq_of_getVert p q
  · have h := congrArg (fun l : List DyckStep => l.length) hs
    simpa only [walkDyckSteps_length] using h
  · intro k
    have hp := walkDyckSteps_prefix_balance p k
    have hq := walkDyckSteps_prefix_balance q k
    rw [hs] at hp
    apply Fin.ext
    omega

/-- Endpoint transport changes no actual step symbol. -/
theorem walkDyckSteps_copy {H : ℕ} {u v u' v' : Fin H}
    (p : (SimpleGraph.pathGraph H).Walk u v) (hu : u = u') (hv : v = v') :
    walkDyckSteps (p.copy hu hv) = walkDyckSteps p := by
  subst_vars
  rfl

/-- Reading an actual concatenation preserves the order of both symbol lists. -/
theorem walkDyckSteps_append {H : ℕ} {u v w : Fin H}
    (p : (SimpleGraph.pathGraph H).Walk u v)
    (q : (SimpleGraph.pathGraph H).Walk v w) :
    walkDyckSteps (p.append q) = walkDyckSteps p ++ walkDyckSteps q := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp only [SimpleGraph.Walk.cons_append, walkDyckSteps, List.cons_append, ih]

/-- The last genuine edge contributes its actual up/down symbol. -/
theorem walkDyckSteps_concat {H : ℕ} {u v w : Fin H}
    (p : (SimpleGraph.pathGraph H).Walk u v) (h : (SimpleGraph.pathGraph H).Adj v w) :
    walkDyckSteps (p.concat h) =
      walkDyckSteps p ++ [if w.val = v.val + 1 then DyckStep.U else DyckStep.D] := by
  rw [SimpleGraph.Walk.concat, walkDyckSteps_append]
  rfl

/-- The edge made from a true Dyck prefix reads back to the original symbol. -/
theorem dyckHeight_edge_symbol {n : ℕ} (p : {p : DyckWord // p.semilength = n})
    (k : ℕ) (hk : k < p.val.toList.length) :
    (if (dyckHeightVertex p (k + 1)).val = (dyckHeightVertex p k).val + 1
      then DyckStep.U else DyckStep.D) = p.val.toList[k] := by
  change (if dyckHeight p.val (k + 1) = dyckHeight p.val k + 1
    then DyckStep.U else DyckStep.D) = p.val.toList[k]
  rcases DyckStep.dichotomy (p.val.toList[k]) with hu | hd
  · have h := dyckHeight_up p.val k hk hu
    simp only [if_pos h, hu]
  · have h := (dyckHeight_down p.val k hk hd).2
    have hn : dyckHeight p.val (k + 1) ≠ dyckHeight p.val k + 1 := by omega
    simp only [if_neg hn, hd]

/-- Every encoded prefix reads back to the actual prefix of the original Dyck word. -/
theorem walkDyckSteps_dyckPrefixWalk {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    ∀ (k : ℕ) (hk : k ≤ 2 * n),
      walkDyckSteps (dyckPrefixWalk p k hk) = p.val.toList.take k := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      have hkl : k < p.val.toList.length := by
        have h := p.val.two_mul_semilength_eq_length
        rw [p.property] at h
        omega
      rw [dyckPrefixWalk, walkDyckSteps_concat, ih,
        dyckHeight_edge_symbol p k hkl, ← dyckStep_prefix_append p.val.toList k hkl]

/-- The complete encoded walk reads back to the complete original Dyck word. -/
theorem walkDyckSteps_dyckToWalk {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    walkDyckSteps (dyckToWalk p) = p.val.toList := by
  rw [dyckToWalk, walkDyckSteps_copy, walkDyckSteps_dyckPrefixWalk]
  have hl : p.val.toList.length = 2 * n := by
    have h := p.val.two_mul_semilength_eq_length
    rw [p.property] at h
    exact h.symm
  rw [← hl, List.take_length]

end W05

