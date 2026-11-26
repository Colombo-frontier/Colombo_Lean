import Bilevel.EndpointTransportQuadraticCore
import Bilevel.ChiVirtualUpperValues
import Bilevel.EndpointTransportReleaseSupport

/-! Exact old-macro/target-prefix evaluation of the physical macro release.
The one-sided macro chain is retained together with its cancellation term. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ChiPrefixEvaluation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def prefixPhysicalMacro {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (kids : Fin (M.n+1) → Node (Block D)) (rM : ℕ) (r : Fin (M.n+1) → ℕ)
    (macroColumns : Fin (M.n+1) → E)
    (targetColumns : ∀ i,Fin ((kids i).n+1) → Physical n D) (z : Joint E (Physical n D)) : ℝ :=
  virtualMacroValue M ν rM macroColumns z.fst+
    ∑ i : Fin (M.n+1),virtualOuterResidual M rM macroColumns i z.fst*
      (virtualRelease (targetNode Q (kids i)) (r i) (targetColumns i) z.snd-1)

theorem physical_macro_release_eq_prefix {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (kids : Fin (M.n+1) → Node (Block D)) (rM : ℕ) (r : Fin (M.n+1) → ℕ)
    (macroColumns : Fin (M.n+1) → E)
    (targetColumns : ∀ i,Fin ((kids i).n+1) → Physical n D)
    (hmacro : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (htarget : ∀ i,∀ k : Fin ((kids i).n+1),k.val<r i →
      targetColumns i k=endpointFrame Q (kids i).frame (Fin.last (n+1)) (basis k))
    (hmw : 0<M.width) (hhp : ∀ i,0<(kids i).parentWidth)
    (hw : ∀ i,(kids i).width≤(kids i).parentWidth)
    (hfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r i≤(kids i).n)
    (z : Joint E (Physical n D))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤M.width/4)
    (hblind : ∀ i,∀ k : Fin ((kids i).n+1),r i≤k.val →
      |(physicalCoordinates Q (kids i) z.snd).snd k|≤(kids i).width/4) :
    macroValue M.n M.ell M.width ν M.radius M.frame z.fst+
      physicalMacroReleaseCorrection M (jointFstLinear (A:=E) (B:=Physical n D)) kids
        (jointSndLinear (A:=E) (B:=Physical n D)) Q z=
      prefixPhysicalMacro Q M ν kids rM r macroColumns targetColumns z := by
  let q : Fin (M.n+1) → ℝ := fun i => physicalRelease Q (kids i) z.snd
  have hq : ∀ i : Fin (M.n+1),rM≤ i.val → q i=0 := by
    intro i hi
    exact ((targetNode Q (kids i)).release_flat_of_blind_terminal (hhp i) (hw i) z.snd
      (hblind i (Fin.last _) (hfuture i hi))).1
  have hrel (i : Fin (M.n+1)) : q i=virtualRelease (targetNode Q (kids i)) (r i) (targetColumns i) z.snd :=
    actual_release_eq_virtual (targetNode Q (kids i)) (r i) (targetColumns i) (htarget i)
      (hhp i) (hw i) z.snd (hblind i)
  change macroValue M.n M.ell M.width ν M.radius M.frame z.fst+
    (∑ i : Fin (M.n+1),wrappedResidual M i z.fst*(q i-1))=_
  rw [macro_release_closed_formula,closedChain_prefix_value M.n rM M.ell M.width hmw q hq _ hmBlind]
  have hread : readout M.n rM M.radius macroColumns z.fst=retain M.n rM (M.coordinates z.fst) :=
    readout_eq_retained M.n rM M.radius macroColumns M.frame hmacro z.fst
  rw [← hread,← virtual_macro_release_closed_formula]
  unfold prefixPhysicalMacro
  simp only [hrel]

end Bilevel.EndpointTransportResponse
