import Bilevel.EndpointTransportHierarchyExtensionSupport
import Bilevel.EndpointTransportInverseSlice
import Bilevel.ParametricScalarInverse

/-! Actual nonlinear physical hierarchy inverse confinement. The support
premise of the generic restricted-inverse theorem is discharged here from
the constructed coarse/fine/radial hierarchy. No hidden-force/width ratio
or assumed oracle equality is used. Observer realization remains separate. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiExtension NearIdentityInverse
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

theorem physicalExtension_gradient_lipschitz {T V : Type*}
    [NormedAddCommGroup T] [InnerProductSpace ℝ T] [CompleteSpace T]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {D : ℕ} {f : Joint (Joint E T) V → ℝ} (hf : ContDiff ℝ 3 f)
    (δ : NNReal) (hb : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤(δ:ℝ)) :
    LipschitzWith δ (gradient (physicalExtension (U:=U) (D:=D) f)) :=
  ParametricScalarInverse.gradient_lipschitz (physicalExtension_contDiff hf) δ
    (fun z => (physicalExtension_jet_bound hf z 2 (by norm_num)).trans (hb _))

theorem physicalHierarchy_inverse_mem {J n D s : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (r : ℕ → List ℕ → ℕ) (h : PhysicalPrefixGeometry Q G P W Z r)
    (δ : NNReal) (hδ : δ<1)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2
      (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn) z‖≤(δ:ℝ))
    (hG : LipschitzWith δ (gradient (physicalExtension (U:=U) (D:=D)
      (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn))))
    (rM : ℕ) (x : HybridOuter E U D) (hmw : 0<M.width)
    (hmacro : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates x.fst.fst k|≤M.width/8)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM →
      FrontierKnown G r (Submodule.comap (Q 0).toLinearMap (Z 0)) J 0 [i.val])
    (y : HybridVariables (Blocks J (Block D)) (Normals s) n D) (hy : y∈physicalNormalKnown W Z s) :
    jointSolution hG hδ x y∈physicalNormalKnown W Z s := by
  have hf := physicalHierarchyExtension_contDiff Q M G P J s coarseIndex radialIndex fineIndex ρ R dn
    (fun i => h.level_width_pos (i.val+1) [] (by omega))
  apply physicalExtension_inverse_mem hf δ hb hδ hG (physicalNormalKnown W Z s) x y hy
  intro z
  exact physicalHierarchyExtension_lower_support Q M G P coarseIndex radialIndex fineIndex ρ R dn hR
    W Z r h rM x.fst.fst hmw hmacro hfront z z.property

theorem physicalHierarchy_restricted_inverse {J n D s : ℕ} (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (coarseIndex radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
    (W : Fin J → Submodule ℝ (Block D)) (Z : Index n → Submodule ℝ (Block D))
    (r : ℕ → List ℕ → ℕ) (h : PhysicalPrefixGeometry Q G P W Z r)
    (hf : ContDiff ℝ 3 (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn))
    (δ : NNReal) (hδ : δ<1)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2
      (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn) z‖≤(δ:ℝ))
    (hG : LipschitzWith δ (gradient (physicalExtension (U:=U) (D:=D)
      (physicalHierarchyExtension Q M G P J s coarseIndex radialIndex fineIndex ρ R dn))))
    (rM : ℕ) (x : HybridOuter E U D) (hmw : 0<M.width)
    (hmacro : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates x.fst.fst k|≤M.width/8)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM →
      FrontierKnown G r (Submodule.comap (Q 0).toLinearMap (Z 0)) J 0 [i.val])
    (y : physicalNormalKnown W Z s) :
    (restrictedInverse (physicalNormalKnown W Z s) hδ
      (lowerSlice_gradient_lipschitz hf δ hb x.fst.fst) y ⟨1,by norm_num⟩ :
      HybridVariables (Blocks J (Block D)) (Normals s) n D)=jointSolution hG hδ x y := by
  apply physicalExtension_restricted_inverse hf δ hb hδ hG (physicalNormalKnown W Z s) x y
  exact physicalHierarchyExtension_lower_support Q M G P coarseIndex radialIndex fineIndex ρ R dn hR
    W Z r h rM x.fst.fst hmw hmacro hfront _
    (restrictedInverse (physicalNormalKnown W Z s) hδ
      (lowerSlice_gradient_lipschitz hf δ hb x.fst.fst) y ⟨1,by norm_num⟩).property

end Bilevel.EndpointTransportResponse
