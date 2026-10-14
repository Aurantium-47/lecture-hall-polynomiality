import W05.DyckWalkReadback

namespace W05

/-- Decoding after the actual forward encoding gives back the original Dyck word. -/
theorem walkToFixedDyck_dyckToFixedWalk {n : ℕ} (p : {p : DyckWord // p.semilength = n}) :
    walkToFixedDyck (dyckToFixedWalk p) = p := by
  apply Subtype.ext
  apply DyckWord.ext
  change walkDyckSteps (dyckToWalk p) = p.val.toList
  exact walkDyckSteps_dyckToWalk p

/-- Encoding after the actual decoding gives back every structural fixed-length walk. -/
theorem dyckToFixedWalk_walkToFixedDyck {n : ℕ}
    (w : {w : (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0 // w.length = 2 * n}) :
    dyckToFixedWalk (walkToFixedDyck w) = w := by
  apply Subtype.ext
  change dyckToWalk (walkToFixedDyck w) = w.val
  apply walkDyckSteps_injective
  rw [walkDyckSteps_dyckToWalk]
  rfl

/-- The genuine equivalence of Dyck words of fixed semilength and all specified finite closed walks. -/
def dyckWordWalkEquiv (n : ℕ) :
    {p : DyckWord // p.semilength = n} ≃
      {w : (SimpleGraph.pathGraph (2 * (n + 1))).Walk 0 0 // w.length = 2 * n} where
  toFun := dyckToFixedWalk
  invFun := walkToFixedDyck
  left_inv := walkToFixedDyck_dyckToFixedWalk
  right_inv := dyckToFixedWalk_walkToFixedDyck

end W05

