import Bilevel.ChiVirtualCoarseValues
import Bilevel.ChiVirtualOuterFineValues
import Bilevel.ChiVirtualFormula

/-! Actual full active extension equals its disclosed-data evaluator on the
blind region, after the one-frontier retained-prefix advance. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ChiTreeProgress PrimitiveGeometry ChiExtension
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem actual_active_eq_virtual (m : ℕ) (M : Node E) (D : Geometry F) (J rM sM : ℕ)
    (r a : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hmPrefix : ∀ k : Fin (M.n+1),k.val<sM → macroColumns k=M.frame (basis k))
    (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<a j I → columns j I k=(D j I).frame (basis k))
    (hms : rM≤sM) (hra : ∀ j I,r j I≤a j I)
    (hmw : 0<M.width) (hh : ∀ j I,j≤J → 0<(D j I).width)
    (hhp : ∀ t,t<J → ∀ I,0<(D (t+1) I).parentWidth)
    (hw : ∀ t,t<J → ∀ I,(D (t+1) I).width≤(D (t+1) I).parentWidth)
    (hfuture : ∀ t,t<J → ∀ I,∀ i : Fin ((D t I).n+1),a t I ≤ i.val →
      a (t+1) (child I i.val)≤(D (t+1) (child I i.val)).n)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM → FrontierAdvance D r a J 0 [i.val])
    (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hβ : 0<(D J []).width) (hθ : 1≤θ)
    (hell : ∀ I,0≤(D J I).ell) (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (rad R : ℕ → ℝ) (dn : ℝ) (z : Full (Joint E (Blocks m F)) s)
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst.fst k|≤M.width/4)
    (hblind : ∀ j I,j≤J → ∀ k : Fin ((D j I).n+1),r j I≤k.val →
      |(D j I).coordinates (block m j z.fst.snd) k|≤(D j I).width/4) :
    hierarchyExtension m M D J c θ hc hβ hθ s index radialIndex fineIndex rad R dn z=
      virtualActive m M D J sM a macroColumns columns c θ s index radialIndex fineIndex rad R dn z := by
  unfold hierarchyExtension total virtualActive
  congr 1
  unfold ChiExtension.hidden coarseSum
  congr 1
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply Finset.sum_congr rfl
    intro i _
    change normalTerm s (index i) _ _ (pack z.fst z.snd)=_
    rw [normalTerm_formula,actual_coarse_eq_virtual m M D J sM a macroColumns columns hmPrefix hprefix
      hmw hh z.fst (fun k hk => hmBlind k (hms.trans hk))
      (fun j I hj k hk => hblind j I hj k ((hra j I).trans hk)) hhp hw hfuture]
  · rw [fineTerm_sum]
    apply Finset.sum_congr rfl
    intro p _
    change normalTerm s fineIndex (outerFinePiece m M D J c θ p)
      (ZeroChainSchedule.width c (D J []).width θ p) (pack z.fst z.snd)=_
    rw [normalTerm_formula,actual_outerFinePiece_eq_virtual m M D J rM sM r a macroColumns columns hmPrefix hprefix
      hms hra hmw hh z.fst hmBlind hblind hfront c θ hc hcs hθ hell]

end Bilevel.ChiPrefixEvaluation
