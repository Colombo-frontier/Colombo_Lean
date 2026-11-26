import Bilevel.ChiVirtualInactiveValues
import Bilevel.ChiVirtualFormula

/-! Complete fixed inactive extension evaluation from the old prefix.
The last-atom cancellation is performed before the multiscale finite sum. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
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
  (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst.fst k|≤M.width/4)
  (hblind : ∀ j I,j≤J → ∀ k : Fin ((D j I).n+1),r j I≤k.val →
    |(D j I).coordinates (block m j z.fst.snd) k|≤(D j I).width/4)
  (hz : ∀ I,∀ k : Fin ((D J I).n+1),r J I≤k.val →
    |(D J I).coordinates (block m J z.fst.snd) k|≤width c (D J []).width θ (levels θ)/8)

include hmPrefix hprefix hmw hh hcs hell hwidth hmBlind hblind hz

theorem actual_inactiveNormal_eq_virtual :
    outerInactiveNormal m M D J c θ hc hβ hθ s fineIndex z=
      (∑ p ∈ Finset.range (levels θ+1),virtualOuterLeaf m M D rM r macroColumns columns
        (pieceLeaf D c θ p) J z.fst*SmallGapProfiles.normal (width c (D J []).width θ p) (z.snd fineIndex))-
        virtualSignal m M D J rM r macroColumns columns c θ s fineIndex z := by
  change outerInactiveNormal m M D J c θ hc hβ hθ s fineIndex (pack z.fst z.snd)=_
  simp only [outerInactiveNormal,outerFineNormal,fineTerm_sum,outerFineData,outerSignalNormal,
    normalTerm_formula,virtualSignal]
  rw [← weighted_last_sub,← weighted_last_sub]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have he := actual_outerInactiveAtom_eq_virtual m M D J rM r macroColumns columns hmPrefix hprefix hmw hh z.fst
    hmBlind (fun j I hj => hblind j I (by omega)) c θ hc hcs hθ hell hwidth hz p
      (by have := Finset.mem_range.mp hp;omega)
  rw [virtualOuterLeaf_inactive] at he
  exact he

include hc hβ hθ in
theorem actual_inactive_eq_virtual
    (hhp : ∀ t,t<J → ∀ I,0<(D (t+1) I).parentWidth)
    (hw : ∀ t,t<J → ∀ I,(D (t+1) I).width≤(D (t+1) I).parentWidth)
    (hfuture : ∀ t,t<J → ∀ I,∀ i : Fin ((D t I).n+1),r t I ≤ i.val →
      r (t+1) (child I i.val)≤(D (t+1) (child I i.val)).n) :
    hierarchyInactiveExtension m M D J c θ hc hβ hθ s index radialIndex fineIndex rad R dn z=
      virtualInactive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn z := by
  have hcoarse : coarseSum index (coarseFamily m M D J) (coarseWidths D J) z=
      ∑ i : Fin J,virtualCoarse m M D rM r macroColumns columns J i z.fst *
        SmallGapProfiles.normal (coarseWidth D (i.val+1)) (z.snd (index i)) := by
    unfold coarseSum
    apply Finset.sum_congr rfl
    intro i _
    change normalTerm s (index i) _ _ (pack z.fst z.snd)=_
    rw [normalTerm_formula,actual_coarse_eq_virtual m M D J rM r macroColumns columns hmPrefix hprefix
      hmw hh z.fst hmBlind hblind hhp hw hfuture]
    rfl
  have hf := actual_inactiveNormal_eq_virtual m M D J rM r macroColumns columns hmPrefix hprefix hmw hh
    c θ hc hcs hβ hθ hell hwidth s fineIndex z hmBlind hblind hz
  unfold hierarchyInactiveExtension hierarchyInactiveHidden sourceCoarseExtension virtualInactive virtualActive
  rw [hcoarse,hf]
  ring

end Bilevel.ChiPrefixEvaluation
