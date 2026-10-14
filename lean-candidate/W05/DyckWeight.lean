import W05.DyckWalkEquiv

open scoped BigOperators

namespace W05

/-- Direct weight of the actual symbol at k: a down step uses its source height. -/
def dyckStepWeight {R : Type} [Monoid R] (α : ℕ → R) (p : DyckWord) (k : ℕ) : R :=
  if p.toList[k]? = some DyckStep.D then α (dyckHeight p k) else 1

/-- Direct product of the original step weights over all actual symbols of a genuine Dyck word. -/
def dyckWeight {R : Type} [CommMonoid R] (α : ℕ → R) (p : DyckWord) : R :=
  ∏ k ∈ Finset.range p.toList.length, dyckStepWeight α p k

/-- The actual empty Dyck word has empty product one. -/
theorem dyckWeight_zero {R : Type} [CommMonoid R] (α : ℕ → R) :
    dyckWeight α 0 = 1 := by
  change (∏ k ∈ Finset.range 0, dyckStepWeight α 0 k) = 1
  simp

/-- Only positive-height weights occur in a genuine Dyck word. -/
theorem dyckWeight_congr {R : Type} [CommMonoid R] (α β : ℕ → R)
    (h : ∀ j : ℕ, 0 < j → α j = β j) (p : DyckWord) :
    dyckWeight α p = dyckWeight β p := by
  unfold dyckWeight
  apply Finset.prod_congr rfl
  intro k hk
  have hkl : k < p.toList.length := Finset.mem_range.mp hk
  unfold dyckStepWeight
  rw [List.getElem?_eq_getElem hkl]
  by_cases hd : p.toList[k] = DyckStep.D
  · simp only [Option.some.injEq, if_pos hd]
    exact h _ (dyckHeight_down p k hkl hd).1
  · simp only [Option.some.injEq, if_neg hd]

/-- Transporting the endpoints of a walk leaves every real edge weight unchanged. -/
theorem dyckWalkWeight_copy {R : Type} [Monoid R] (α : ℕ → R)
    {H : ℕ} {u v u' v' : Fin H} (p : (SimpleGraph.pathGraph H).Walk u v)
    (hu : u = u') (hv : v = v') :
    dyckWalkWeight α (p.copy hu hv) = dyckWalkWeight α p := by
  subst_vars
  rfl

/-- Walk concatenation multiplies the actual ordered products. -/
theorem dyckWalkWeight_append {R : Type} [Monoid R] (α : ℕ → R)
    {H : ℕ} {u v w : Fin H} (p : (SimpleGraph.pathGraph H).Walk u v)
    (q : (SimpleGraph.pathGraph H).Walk v w) :
    dyckWalkWeight α (p.append q) = dyckWalkWeight α p * dyckWalkWeight α q := by
  induction p with
  | nil => simp [dyckWalkWeight]
  | cons h p ih =>
      simp only [SimpleGraph.Walk.cons_append, dyckWalkWeight, ih, mul_assoc]

/-- A real last edge contributes the weight at its departure height when it descends. -/
theorem dyckWalkWeight_concat {R : Type} [Monoid R] (α : ℕ → R)
    {H : ℕ} {u v w : Fin H} (p : (SimpleGraph.pathGraph H).Walk u v)
    (h : (SimpleGraph.pathGraph H).Adj v w) :
    dyckWalkWeight α (p.concat h) =
      dyckWalkWeight α p * (if w.val = v.val + 1 then 1 else α v.val) := by
  rw [SimpleGraph.Walk.concat, dyckWalkWeight_append]
  simp only [dyckWalkWeight, mul_one]

/-- The existing encoding assigns precisely the direct original weight to each actual symbol. -/
theorem dyckStepWeight_edge {R : Type} [Monoid R] (α : ℕ → R)
    {n : ℕ} (p : {p : DyckWord // p.semilength = n})
    (k : ℕ) (hk : k < p.val.toList.length) :
    (if (dyckHeightVertex p (k + 1)).val = (dyckHeightVertex p k).val + 1
      then 1 else α (dyckHeightVertex p k).val) = dyckStepWeight α p.val k := by
  change (if dyckHeight p.val (k + 1) = dyckHeight p.val k + 1
    then 1 else α (dyckHeight p.val k)) =
      (if p.val.toList[k]? = some DyckStep.D then α (dyckHeight p.val k) else 1)
  rw [List.getElem?_eq_getElem hk]
  rcases DyckStep.dichotomy (p.val.toList[k]) with hu | hd
  · have hh := dyckHeight_up p.val k hk hu
    simp [hu, hh]
  · have hh := (dyckHeight_down p.val k hk hd).2
    have hn : dyckHeight p.val (k + 1) ≠ dyckHeight p.val k + 1 := by omega
    simp [hd, hn]

/-- Every actual encoded prefix preserves the direct product of the original Dyck step weights. -/
theorem dyckPrefixWalk_weight {R : Type} [CommMonoid R] (α : ℕ → R)
    {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    ∀ (k : ℕ) (hk : k ≤ 2 * n),
      dyckWalkWeight α (dyckPrefixWalk p k hk) =
        ∏ j ∈ Finset.range k, dyckStepWeight α p.val j := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [dyckPrefixWalk, dyckWalkWeight]
  | succ k ih =>
      intro hk
      have hkl : k < p.val.toList.length := by
        have h := p.val.two_mul_semilength_eq_length
        rw [p.property] at h
        omega
      rw [dyckPrefixWalk, dyckWalkWeight_concat, ih,
        dyckStepWeight_edge α p k hkl, Finset.prod_range_succ]

/-- The actual forward map of the proved equivalence preserves the original direct Dyck weight. -/
theorem dyckToWalk_weight {R : Type} [CommMonoid R] (α : ℕ → R)
    {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    dyckWalkWeight α (dyckToWalk p) = dyckWeight α p.val := by
  rw [dyckToWalk, dyckWalkWeight_copy, dyckPrefixWalk_weight]
  unfold dyckWeight
  have hl : p.val.toList.length = 2 * n := by
    have h := p.val.two_mul_semilength_eq_length
    rw [p.property] at h
    exact h.symm
  rw [hl]

end W05

