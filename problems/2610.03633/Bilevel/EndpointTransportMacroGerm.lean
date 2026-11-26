import Bilevel.EndpointTransportMacroPrefix
import Bilevel.ChiUniformBlindNeighborhood
import Bilevel.ChiVirtualUpperGerm

/-! Actual full physical macro-release gradient from the retained macro
and target prefixes. The common neighborhood retains the cancellation. -/
noncomputable section
set_option autoImplicit false
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ChiPrefixEvaluation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physical_macro_release_eventuallyEq_prefix {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
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
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤3*M.width/16)
    (hblind : ∀ i,∀ k : Fin ((kids i).n+1),r i≤k.val →
      |(physicalCoordinates Q (kids i) z.snd).snd k|≤3*(kids i).width/16)
    (hmR : 0<M.radius) (hR : ∀ i,0<(kids i).radius)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδN : ∀ i,δ≤(kids i).width/16) :
    (fun y : Joint E (Physical n D) => macroValue M.n M.ell M.width ν M.radius M.frame y.fst+
      physicalMacroReleaseCorrection M (jointFstLinear (A:=E) (B:=Physical n D)) kids
        (jointSndLinear (A:=E) (B:=Physical n D)) Q y) =ᶠ[𝓝 z]
      prefixPhysicalMacro Q M ν kids rM r macroColumns targetColumns := by
  have hm := eventually_blind_uniform (fun _ : Unit => M) (fun _ => hmR)
    (fun _ => jointFstLinear (A:=E) (B:=Physical n D))
    (fun _ => ChiPrimitive.jointFstLinear_norm)
    (fun _ => rM) (fun _ => M.width/4) δ hδ z (by
      intro _ k hk
      change |M.coordinates z.fst k|≤M.width/4-δ
      have hb := hmBlind k hk
      linarith)
  have hn := eventually_blind_uniform (fun i => targetNode Q (kids i))
    (fun i => mul_pos (gamma_positive n) (hR i))
    (fun _ => jointSndLinear (A:=E) (B:=Physical n D))
    (fun _ => ChiPrimitive.jointSndLinear_norm)
    r (fun i => (kids i).width/4) δ hδ z (by
      intro i k hk
      change |(physicalCoordinates Q (kids i) z.snd).snd k|≤(kids i).width/4-δ
      have hb := hblind i k hk
      have hd := hδN i
      linarith)
  filter_upwards [hm,hn] with y hym hyn
  exact physical_macro_release_eq_prefix Q M ν kids rM r macroColumns targetColumns hmacro htarget
    hmw hhp hw hfuture y (hym ()) hyn

end Bilevel.EndpointTransportResponse
