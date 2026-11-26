import Bilevel.ChiCanonicalFrontierAdvance
import Bilevel.TransportHierarchyPreSpace

/-! Reachable split leaves consume the globally next source prefix.
Completed old leaves use their retained full frame; no next source vector
is required for every unreached future leaf. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiTreeProgress ChiHierarchyIndex ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem frontier_leaf_source_prefix {G : Geometry E}
    {old new : ℕ → List ℕ → ℕ} {j : ℕ} {I : List ℕ}
    (h : FrontierAdvance G old new 0 j I) (hmono : old j I≤new j I)
    (k : Fin ((G j I).n+1)) (hk : k.val<old j I+1) : k.val<new j I := by
  change (G j I).n<old j I ∨ old j I<new j I at h
  rcases h with h|h
  · have hb := k.isLt
    omega
  · omega

theorem canonical_reachable_source_prefix (G : Geometry E) (counts : ℕ → ℕ)
    (hsize : ∀ j I,(G j I).n=counts (j+1)) (q : ℕ)
    (i : Fin (counts 0+1)) (hi : i.val≤counter counts 1 q 0 [])
    (k : Fin ((G 0 [i.val]).n+1))
    (hk : k.val<canonicalCounter counts 0 q 0 [i.val]+1) :
    k.val<canonicalCounter counts 0 (q+1) 0 [i.val] :=
  frontier_leaf_source_prefix (canonical_frontierAdvance G counts hsize 0 q i hi)
    (canonicalCounter_success_bounds counts 0 q 0 [i.val]).1 k hk

end Bilevel.TransportHierarchy
