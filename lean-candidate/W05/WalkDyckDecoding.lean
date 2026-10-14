import W05.DyckWordEncoding

namespace W05

/-- Read genuine path-graph edges as up/down symbols in their actual order. -/
def walkDyckSteps {H : ℕ} {u v : Fin H} :
    (SimpleGraph.pathGraph H).Walk u v → List DyckStep
  | .nil => []
  | .cons' u v _ _ w =>
      (if v.val = u.val + 1 then DyckStep.U else DyckStep.D) :: walkDyckSteps w

theorem walkDyckSteps_length {H : ℕ} {u v : Fin H}
    (w : (SimpleGraph.pathGraph H).Walk u v) :
    (walkDyckSteps w).length = w.length := by
  induction w with
  | nil => rfl
  | cons h w ih =>
      simp only [walkDyckSteps, List.length_cons, SimpleGraph.Walk.length_cons, ih]

/-- The true vertex height is determined by every decoded prefix; this includes saturated prefixes. -/
theorem walkDyckSteps_prefix_balance {H : ℕ} {u v : Fin H}
    (w : (SimpleGraph.pathGraph H).Walk u v) (k : ℕ) :
    u.val + ((walkDyckSteps w).take k).count DyckStep.U =
      (w.getVert k).val + ((walkDyckSteps w).take k).count DyckStep.D := by
  induction w generalizing k with
  | nil => simp [walkDyckSteps, SimpleGraph.Walk.getVert]
  | @cons u v z h w ih =>
      cases k with
      | zero => simp [walkDyckSteps, SimpleGraph.Walk.getVert]
      | succ k =>
          have hp := ih k
          have ha := SimpleGraph.pathGraph_adj.mp h
          by_cases hu : v.val = u.val + 1
          · simp only [walkDyckSteps, if_pos hu, List.take_succ_cons,
              SimpleGraph.Walk.getVert_cons_succ, List.count_cons,
              beq_self_eq_true, ite_true, beq_iff_eq, reduceCtorEq, ite_false]
            omega
          · have hd : u.val = v.val + 1 := by rcases ha with h | h <;> omega
            simp only [walkDyckSteps, if_neg hu, List.take_succ_cons,
              SimpleGraph.Walk.getVert_cons_succ, List.count_cons,
              beq_self_eq_true, ite_true, beq_iff_eq, reduceCtorEq, ite_false]
            omega

/-- Prefix nonnegativity follows from real finite vertex heights, not from a premise. -/
theorem walkDyckSteps_prefix_le {H : ℕ} {u v : Fin H}
    (w : (SimpleGraph.pathGraph H).Walk u v) (k : ℕ) :
    ((walkDyckSteps w).take k).count DyckStep.D ≤
      u.val + ((walkDyckSteps w).take k).count DyckStep.U := by
  have h := walkDyckSteps_prefix_balance w k
  omega

/-- Decode a real zero-to-zero walk into a genuine DyckWord, proving both defining conditions. -/
def walkToDyck {n : ℕ}
    (w : (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0) : DyckWord where
  toList := walkDyckSteps w
  count_U_eq_count_D := by
    have h := walkDyckSteps_prefix_balance w w.length
    have ht : (walkDyckSteps w).take w.length = walkDyckSteps w := by
      rw [← walkDyckSteps_length w, List.take_length]
    simpa only [ht, SimpleGraph.Walk.getVert_length, Fin.val_zero, zero_add] using h
  count_D_le_count_U k := by
    simpa only [Fin.val_zero, zero_add] using walkDyckSteps_prefix_le w k

/-- Empty walks decode to the empty actual Dyck word. -/
theorem walkToDyck_nil (n : ℕ) :
    walkToDyck (SimpleGraph.Walk.nil :
      (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0) = 0 := by
  apply DyckWord.ext
  rfl

/-- A real walk of length 2n decodes to semilength n, including n=0. -/
theorem walkToDyck_semilength {n : ℕ}
    (w : {w : (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0 //
      w.length = 2 * n}) :
    (walkToDyck w.val).semilength = n := by
  have hl : (walkToDyck w.val).toList.length = 2 * n := by
    change (walkDyckSteps w.val).length = 2 * n
    rw [walkDyckSteps_length, w.property]
  have h := (walkToDyck w.val).two_mul_semilength_eq_length
  omega

/-- The reverse map has the exact semilength target without extra graph or balance assumptions. -/
def walkToFixedDyck {n : ℕ}
    (w : {w : (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0 //
      w.length = 2 * n}) : {p : DyckWord // p.semilength = n} :=
  ⟨walkToDyck w.val, walkToDyck_semilength w⟩

/-- Decoding recovers each actual walk vertex as the genuine Dyck prefix height. -/
theorem walkToDyck_height {n : ℕ}
    (w : (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0) (k : ℕ) :
    dyckHeight (walkToDyck w) k = (w.getVert k).val := by
  have h := walkDyckSteps_prefix_balance w k
  have hh := dyckHeight_count_identity (walkToDyck w) k
  change dyckHeight (walkToDyck w) k + ((walkDyckSteps w).take k).count DyckStep.D =
    ((walkDyckSteps w).take k).count DyckStep.U at hh
  simp only [Fin.val_zero, zero_add] at h
  omega

/-- The height bound n for a real length-2n closed walk is derived, not assumed. -/
theorem fixedWalk_height_le {n : ℕ}
    (w : {w : (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0 //
      w.length = 2 * n}) (k : ℕ) :
    (w.val.getVert k).val ≤ n := by
  have h := dyckHeight_le_semilength (walkToDyck w.val) k
  rw [walkToDyck_semilength w, walkToDyck_height] at h
  exact h

end W05

