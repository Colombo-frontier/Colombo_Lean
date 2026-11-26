import Bilevel.EndpointTransportVirtualFormula

/-! Exact selected-coarse recursions, retaining the cancellation between
the deepest payload and its fine frontier before comparing prefixes. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry PartialLegendre ChiPrefixEvaluation

theorem physicalCoarseCarrier_succ {m n D : ℕ} (Q : Rotations n D) (G : Geometry (Block D))
    (P : ChiFine.Parameters) (d j t : ℕ) (I : List ℕ)
    (x : HybridTangent (Blocks m (Block D)) n D) :
    physicalCoarseCarrier m Q G jointFstLinear jointSndLinear P (d+1) j I (t+1) x=
      ∑ i : Fin ((G j I).n+1),(G j I).selector i (block m j x.fst)*
        physicalCoarseCarrier m Q G jointFstLinear jointSndLinear P d (j+1) (child I i.val) t x := by
  by_cases ht : t=d
  · subst t
    simp only [physicalCoarseCarrier,physicalCarrier,if_pos rfl,if_true,selectedPhysicalFineFrontier,
      ChiLiftedCarrier.selectFamily,ChiLiftedCarrier.selector,jointSelector,Function.comp_apply,
      mul_sub,Finset.sum_sub_distrib]
    rfl
  · have htd : t+1≠d+1 := by omega
    simp only [physicalCoarseCarrier,physicalCarrier,if_neg ht,if_neg htd,sub_zero,
      ChiLiftedCarrier.selector,jointSelector,Function.comp_apply]
    rfl

theorem virtualPhysicalCoarseCarrier_succ {m n D : ℕ} (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (r sourceCount : ℕ → List ℕ → ℕ) (columns : ∀ k I,Fin ((G k I).n+1) → Block D)
    (S T : ∀ k I,Fin ((G k I).n+1) → Physical n D)
    (d j t : ℕ) (I : List ℕ) (x : HybridTangent (Blocks m (Block D)) n D) :
    virtualPhysicalCoarseCarrier G P r sourceCount columns S T (d+1) j I (t+1) x=
      ∑ i : Fin ((G j I).n+1),virtualSelector (G j I) (r j I) (columns j I) i (block m j x.fst)*
        virtualPhysicalCoarseCarrier G P r sourceCount columns S T d (j+1) (child I i.val) t x := by
  by_cases ht : t=d
  · subst t
    simp only [virtualPhysicalCoarseCarrier,virtualPhysicalCarrier,if_pos rfl,if_true,
      virtualPhysicalFrontier,virtualPhysicalSelect,mul_sub,Finset.sum_sub_distrib]
  · have htd : t+1≠d+1 := by omega
    simp only [virtualPhysicalCoarseCarrier,virtualPhysicalCarrier,if_neg ht,if_neg htd,sub_zero]

end Bilevel.EndpointTransportResponse
