import Bilevel.ChiVirtualInactiveFullValues
import Bilevel.ChiUniformBlindNeighborhood

/-! Complete fixed inactive extension evaluation from the old prefix.
The last-atom cancellation is performed before the multiscale finite sum. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Topology
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiExtensionCalibration ZeroChainSchedule
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ) (r : ℕ → List ℕ → ℕ)
  (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
  (hmPrefix : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
  (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<r j I → columns j I k=(D j I).frame (basis k))
  (hmw : 0<M.width) (hh : ∀ j I,j≤J → 0<(D j I).width)
  (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hβ : 0<(D J []).width) (hθ : 1≤θ)
  (hell : ∀ I,0≤(D J I).ell) (hwidth : ∀ I,(D J I).width=(D J []).width)
  (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (rad R : ℕ → ℝ) (dn : ℝ) (z : Full (Joint E (Blocks m F)) s)
  (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst.fst k|≤3*M.width/16)
  (hblind : ∀ j I,j≤J → ∀ k : Fin ((D j I).n+1),r j I≤k.val →
    |(D j I).coordinates (block m j z.fst.snd) k|≤3*(D j I).width/16)
  (hz : ∀ I,∀ k : Fin ((D J I).n+1),r J I≤k.val →
    |(D J I).coordinates (block m J z.fst.snd) k|≤width c (D J []).width θ (levels θ)/16)

include hmPrefix hprefix hmw hh hc hcs hβ hθ hell hwidth hmBlind hblind hz in
theorem actual_inactive_eventuallyEq_virtual
    (hhp : ∀ t,t<J → ∀ I,0<(D (t+1) I).parentWidth)
    (hw : ∀ t,t<J → ∀ I,(D (t+1) I).width≤(D (t+1) I).parentWidth)
    (hfuture : ∀ t,t<J → ∀ I,∀ i : Fin ((D t I).n+1),r t I ≤ i.val →
      r (t+1) (child I i.val)≤(D (t+1) (child I i.val)).n)
    (hmR : 0<M.radius) (hDR : ∀ j I,j≤J → 0<(D j I).radius)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδD : ∀ j I,j≤J → δ≤(D j I).width/16)
    (hδW : δ≤width c (D J []).width θ (levels θ)/16) :
    hierarchyInactiveExtension m M D J c θ hc hβ hθ s index radialIndex fineIndex rad R dn =ᶠ[𝓝 z]
      virtualInactive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn := by
  have hm := eventually_blind_uniform (fun _ : Unit => M) (fun _ => hmR)
    (fun _ => fullMacro (E:=E) (F:=F) m s) (fun _ => fullMacro_norm_le m s)
    (fun _ => rM) (fun _ => M.width/4) δ hδ z (by
      intro _ k hk
      change |M.coordinates z.fst.fst k|≤M.width/4-δ
      have hb := hmBlind k hk
      linarith)
  have hn := eventually_blind_uniform
    (fun i : Fin (J+1) × List ℕ => D i.1.val i.2)
    (fun i => hDR _ _ (by have := i.1.isLt;omega))
    (fun i => fullBlock (E:=E) (F:=F) m s i.1.val) (fun i => fullBlock_norm_le m s i.1.val)
    (fun i => r i.1.val i.2) (fun i => (D i.1.val i.2).width/4) δ hδ z (by
      intro i k hk
      change |(D i.1.val i.2).coordinates (block m i.1.val z.fst.snd) k|≤(D i.1.val i.2).width/4-δ
      have hi : i.1.val≤J := by have := i.1.isLt;omega
      have hb := hblind i.1.val i.2 hi k hk
      have hd := hδD i.1.val i.2 hi
      linarith)
  have hl := eventually_blind_uniform (fun I : List ℕ => D J I) (fun I => hDR J I le_rfl)
    (fun _ => fullBlock (E:=E) (F:=F) m s J) (fun _ => fullBlock_norm_le m s J)
    (r J) (fun _ => width c (D J []).width θ (levels θ)/8) δ hδ z (by
      intro I k hk
      change |(D J I).coordinates (block m J z.fst.snd) k|≤width c (D J []).width θ (levels θ)/8-δ
      have hb := hz I k hk
      linarith)
  filter_upwards [hm,hn,hl] with y hym hyn hyl
  apply actual_inactive_eq_virtual m M D J rM r macroColumns columns hmPrefix hprefix hmw hh
    c θ hc hcs hβ hθ hell hwidth s index radialIndex fineIndex rad R dn y
    (hym ()) (fun j I hj k hk => hyn (⟨j,by omega⟩,I) k hk) hyl hhp hw hfuture

end Bilevel.ChiPrefixEvaluation
