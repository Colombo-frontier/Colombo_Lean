import Bilevel.EndpointTransportNormalExtension
import Bilevel.EndpointTransportUpperBase

/-! Exact all-point normal trace of the actual physical hybrid objective.
No response equation is assumed in this identity. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiRecursive ChiCarrier ChiOuter ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physical_outer_expanded {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℕ → ℝ) (j : ℕ) (z : PhysicalBase E m n D) :
    physicalOuter Q M ν G ρ R (j+1) z.fst (padded z.snd.fst) z.snd.snd=
      macroValue M.n M.ell M.width ν M.radius M.frame z.fst+
        outerReleaseCorrection m M (fun i => G 0 [i.val]) (baseOrdinaryCoordinates m n D z)+
        (∑ t : Fin (j+2),outerPhysicalCarrier m Q M (baseMacroProjection m n D) G
          (baseOrdinaryProjection m n D) (basePhysicalProjection m n D) (j+1) t.val z)+
        physicalPublic ρ R (j+1) 0 (padded z.snd.fst) z.snd.snd := by
  rw [outer_physical_carrier_trace]
  simp only [physicalOuter,show j+1≠0 by omega,if_false]
  change macroValue M.n M.ell M.width ν M.radius M.frame z.fst+
    (∑ i : Fin (M.n+1),(((G 0 [i.val]).release (block m 0 z.snd.fst)-1)*wrappedResidual M i z.fst+
      physicalRecursive Q G (j+1) 0 [i.val] (padded z.snd.fst) z.snd.snd*wrappedSelector M i z.fst))+
        physicalPublic ρ R (j+1) 0 (padded z.snd.fst) z.snd.snd=
    macroValue M.n M.ell M.width ν M.radius M.frame z.fst+
    (∑ i : Fin (M.n+1),wrappedResidual M i z.fst*((G 0 [i.val]).release (block m 0 z.snd.fst)-1))+
    (∑ i : Fin (M.n+1),wrappedSelector M i z.fst*physicalRecursive Q G (j+1) 0 [i.val] (padded z.snd.fst) z.snd.snd)+
        physicalPublic ρ R (j+1) 0 (padded z.snd.fst) z.snd.snd
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ i : Fin (M.n+1),((G 0 [i.val]).release (block m 0 z.snd.fst)-1)*wrappedResidual M i z.fst)=
      ∑ i : Fin (M.n+1),wrappedResidual M i z.fst*((G 0 [i.val]).release (block m 0 z.snd.fst)-1) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ i : Fin (M.n+1),physicalRecursive Q G (j+1) 0 [i.val] (padded z.snd.fst) z.snd.snd*wrappedSelector M i z.fst)=
      ∑ i : Fin (M.n+1),wrappedSelector M i z.fst*physicalRecursive Q G (j+1) 0 [i.val] (padded z.snd.fst) z.snd.snd := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1,h2]
  ring

theorem physicalHierarchyExtension_objective_trace {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (j s : ℕ)
    (coarseIndex radialIndex : Fin (j+1) → Fin s) (fineIndex : Fin s)
    (ρ R : ℕ → ℝ) (dn : ℝ) (hdn : dn≠0) (hw : ∀ i : Fin (j+1),0<(G (i.val+1) []).width)
    (hR : ∀ i : Fin (j+1),0<R (i.val+1)) (x : PhysicalBase E (j+1) n D) :
    physicalUpperBase (j+1) Q M ν G (j+1) (ρ 0) (R 0) x+
      dn*normalReadout s (gradient (fun q : Normals s =>
        physicalHierarchyExtension Q M G P (j+1) s coarseIndex radialIndex fineIndex ρ R dn (pack x q)) 0)=
      physicalOuter Q M ν G ρ R (j+1) x.fst (padded x.snd.fst) x.snd.snd := by
  have ht := physicalHierarchyExtension_carrier_trace Q M G P j s coarseIndex radialIndex fineIndex ρ R dn hdn hw hR x
  rw [physical_outer_expanded]
  unfold physicalUpperBase physicalBaseLower
  change _+(_+_+RadialWrapper.bowl (ρ 0) (R 0) (block (j+1) 0 x.snd.fst))+_=_
  rw [show baseMacroProjection (j+1) n D x=x.fst from rfl]
  linarith only [ht]

end Bilevel.EndpointTransportResponse
