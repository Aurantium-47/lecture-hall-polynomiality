import W05.DyckWordHeights

namespace W05

/-- Encode the first k actual Dyck symbols as a finite path-graph walk. -/
def dyckPrefixWalk {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    (k : ℕ) → (hk : k ≤ 2 * n) →
      (SimpleGraph.pathGraph (2 * (n + 1))).Walk
        (dyckHeightVertex p 0) (dyckHeightVertex p k)
  | 0, _ => .nil
  | k + 1, hk =>
      (dyckPrefixWalk p k (by omega)).concat (dyckHeightVertex_adj p k (by omega))

/-- The encoding traverses one actual graph edge for each original symbol. -/
theorem dyckPrefixWalk_length {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    ∀ (k : ℕ) (hk : k ≤ 2 * n), (dyckPrefixWalk p k hk).length = k := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      rw [dyckPrefixWalk, SimpleGraph.Walk.length_concat, ih]

/-- The genuine Dyck word gives a zero-to-zero walk after all its symbols. -/
def dyckToWalk {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0 :=
  (dyckPrefixWalk p (2 * n) (le_refl _)).copy
    (dyckHeightVertex_zero p) (dyckHeightVertex_end p)

theorem dyckToWalk_length {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    (dyckToWalk p).length = 2 * n := by
  simp only [dyckToWalk, SimpleGraph.Walk.length_copy, dyckPrefixWalk_length]

/-- A real map from Dyck words of fixed semilength into the exact finite walks of length 2n. -/
def dyckToFixedWalk {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    {w : (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0 // w.length = 2 * n} :=
  ⟨dyckToWalk p, dyckToWalk_length p⟩

end W05

