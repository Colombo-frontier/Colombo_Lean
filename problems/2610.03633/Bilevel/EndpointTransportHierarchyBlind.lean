import Bilevel.EndpointTransportHierarchySupport

/-! Every point in the physical known space retains the old target blind
tail and flat unfinished terminal releases. These quantitative conclusions
also apply to the nonlinear inverse once its membership is proved. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier

theorem PhysicalPrefixGeometry.target_blind_at_point {J n D : ℕ} {Q : Rotations n D}
    {G : Geometry (Block D)} {P : ChiFine.Parameters}
    {W : Fin J → Submodule ℝ (Block D)} {Z : Index n → Submodule ℝ (Block D)}
    {r : ℕ → List ℕ → ℕ} (h : PhysicalPrefixGeometry Q G P W Z r)
    (I : List ℕ) (x : HybridTangent (Blocks J (Block D)) n D)
    (hx : x∈physicalTangentKnown W Z) :
    ∀ k : Fin ((G J I).n+1),r J I≤k.val →
      |(physicalCoordinates Q (G J I) x.snd).snd k|≤(G J I).width/8 :=
  physical_target_blind Q (G J I) (h.radius_pos I) (Z (Fin.last (n+1))) (r J I)
    ((G J I).width/8) (h.target_blind I) x.snd (((mem_physicalTangentKnown W Z x).mp hx).2 _)

theorem PhysicalPrefixGeometry.unfinished_release_flat {J n D : ℕ} {Q : Rotations n D}
    {G : Geometry (Block D)} {P : ChiFine.Parameters}
    {W : Fin J → Submodule ℝ (Block D)} {Z : Index n → Submodule ℝ (Block D)}
    {r : ℕ → List ℕ → ℕ} (h : PhysicalPrefixGeometry Q G P W Z r)
    (I : List ℕ) (hr : r J I≤(G J I).n)
    (x : HybridTangent (Blocks J (Block D)) n D) (hx : x∈physicalTangentKnown W Z) :
    physicalRelease Q (G J I) x.snd=0 ∧ fderiv ℝ (physicalRelease Q (G J I)) x.snd=0 :=
  physical_release_flat_on_product Q (G J I) (h.width_pos I) (h.radius_pos I)
    (h.parent_pos J I le_rfl) (h.width_le_parent J I le_rfl) (r J I) hr Z
    (h.target_blind I) x.snd ((mem_physicalTangentKnown W Z x).mp hx).2

end Bilevel.EndpointTransportResponse
