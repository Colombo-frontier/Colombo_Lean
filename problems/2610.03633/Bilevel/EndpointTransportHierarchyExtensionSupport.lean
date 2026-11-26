import Bilevel.EndpointTransportHierarchySupport
import Bilevel.EndpointTransportRadialSupport
import Bilevel.ChiExtensionHiddenSupport

/-! The complete actual physical hierarchy extension preserves the product
known space at every restricted point. Compact coarse terms, all fine
atoms, and all public radial channels are differentiated explicitly. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem PhysicalPrefixGeometry.level_width_pos {J n D : ℕ} {Q : Rotations n D}
    {G : Geometry (Block D)} {P : ChiFine.Parameters}
    {W : Fin J → Submodule ℝ (Block D)} {Z : Index n → Submodule ℝ (Block D)}
    {r : ℕ → List ℕ → ℕ} (h : PhysicalPrefixGeometry Q G P W Z r)
    (k : ℕ) (I : List ℕ) (hk : k≤J) : 0<(G k I).width := by
  by_cases he : k=J
  · simpa only [he] using h.width_pos I
  · exact (h.ancestors k I (by omega)).width_pos

theorem physicalHierarchyExtension_tangent_support {J n D s : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (r : ℕ → List ℕ → ℕ) (h : PhysicalPrefixGeometry Q G P W Z r)
    (rM : ℕ) (a : E) (hmw : 0<M.width)
    (hmacro : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates a k|≤M.width/8)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM →
      FrontierKnown G r (Submodule.comap (Q 0).toLinearMap (Z 0)) J 0 [i.val])
    (x : HybridTangent (Blocks J (Block D)) n D) (q : Normals s)
    (hx : x∈physicalTangentKnown W Z) :
    gradient (fun y => physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn
      (pack (pack a y) q)) x∈physicalTangentKnown W Z := by
  have hwidth (i : Fin J) : 0<(G (i.val+1) []).width := h.level_width_pos _ [] (by omega)
  have hc (i : Fin J) : ContDiff ℝ 3 (physicalHierarchyCoarse Q M G P J i) :=
    outerPhysicalCoarseFamily_contDiff J Q M (baseMacroProjection J n D) G
      (baseOrdinaryProjection J n D) (basePhysicalProjection J n D) P J i
  have hw (i : Fin J) : 0<coarseWidth G (i.val+1) := coarseWidth_pos G _ (hwidth i)
  have hp : ContDiff ℝ 3 (fun y : HybridTangent (Blocks J (Block D)) n D => pack (pack a y) q) :=
    (packLinear (X:=PhysicalBase E J n D) (Y:=Normals s)).contDiff.comp
      (((packLinear (X:=E) (Y:=HybridTangent (Blocks J (Block D)) n D)).contDiff.comp
        (contDiff_const.prodMk contDiff_id)).prodMk contDiff_const)
  change gradient (fun y =>
    hidden coarseIndex (physicalHierarchyCoarse Q M G P J) (fun i => coarseWidth G (i.val+1))
      fineIndex (physicalHierarchyFine Q M G P J) (1/dn) (pack (pack a y) q)+
    radialSum radialIndex (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
      (publicRadialCurvature n ρ) (publicRadialRadius n R) dn (pack (pack a y) q)) x∈_
  apply gradient_add_mem (physicalTangentKnown W Z)
    ((hidden_contDiff coarseIndex (physicalHierarchyCoarse Q M G P J) _ hc hw fineIndex
      (physicalHierarchyFine Q M G P J) (1/dn)).comp hp)
    ((radialSum_contDiff radialIndex (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
      (publicRadialCurvature n ρ) (publicRadialRadius n R) dn).comp hp) x
  · apply hidden_tangent_slice_support coarseIndex (physicalHierarchyCoarse Q M G P J) _ hc hw
      fineIndex (physicalHierarchyFine Q M G P J) (1/dn) a q (physicalTangentKnown W Z) x
    · exact fun i => physicalHierarchyCoarse_tangent_support Q M G P W Z r h i a x hx
    · exact fun p _ => physicalHierarchyFine_tangent_support Q M G P W Z r h rM a hmw hmacro hfront p x hx
  · exact physical_radialSum_support radialIndex ρ R dn hR a x q W Z hx

theorem physicalHierarchyExtension_lower_support {J n D s : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (r : ℕ → List ℕ → ℕ) (h : PhysicalPrefixGeometry Q G P W Z r)
    (rM : ℕ) (a : E) (hmw : 0<M.width)
    (hmacro : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates a k|≤M.width/8)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM →
      FrontierKnown G r (Submodule.comap (Q 0).toLinearMap (Z 0)) J 0 [i.val])
    (z : HybridVariables (Blocks J (Block D)) (Normals s) n D) (hz : z∈physicalNormalKnown W Z s) :
    gradient (lowerSlice (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn) a) z∈
      physicalNormalKnown W Z s := by
  have hf := physicalHierarchyExtension_contDiff Q M G P J s coarseIndex radialIndex fineIndex ρ R dn
    (fun i => h.level_width_pos (i.val+1) [] (by omega))
  apply (gradient_physicalNormalKnown_iff W Z z (lowerSlice_contDiff hf a)).mpr
  exact physicalHierarchyExtension_tangent_support Q M G P coarseIndex radialIndex fineIndex ρ R dn hR
    W Z r h rM a hmw hmacro hfront z.fst z.snd ((mem_jointKnown _ _ z).mp hz).1

end Bilevel.EndpointTransportResponse
