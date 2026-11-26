import Bilevel.ChiVirtualUpperFormula
import Bilevel.ChiOuterClosedPrefix

/-! Exact upper-base values from the OLD disclosed prefix. Macro and inner
closed-carrier cancellations are both performed before prefix evaluation. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem macro_release_closed_formula (M : Node E) (ν : ℝ) (q : Fin (M.n+1) → ℝ) (u : E) :
    macroValue M.n M.ell M.width ν M.radius M.frame u+
      (∑ i : Fin (M.n+1),wrappedResidual M i u*(q i-1))=
      closedChain M.n M.ell M.width q (M.coordinates u)+RadialWrapper.bowl ν M.radius u := by
  simp only [macroValue,RadialWrapper.wrapped,ChiOuter.chain,ZeroChainResidualScaled.scaled,
    wrappedResidual,closedChain,closedValue,Node.coordinates,WrappedChain.coordinates,Finset.mul_sum,mul_add]
  ring

omit [CompleteSpace E] in
theorem virtual_macro_release_closed_formula (M : Node E) (ν : ℝ) (rM : ℕ)
    (macroColumns : Fin (M.n+1) → E) (q : Fin (M.n+1) → ℝ) (u : E) :
    virtualMacroValue M ν rM macroColumns u+
      (∑ i : Fin (M.n+1),virtualOuterResidual M rM macroColumns i u*(q i-1))=
      closedChain M.n M.ell M.width q (readout M.n rM M.radius macroColumns u)+
        RadialWrapper.bowl ν M.radius u := by
  simp only [virtualMacroValue,ChiOuter.chain,ZeroChainResidualScaled.scaled,
    virtualOuterResidual,closedChain,closedValue,Finset.mul_sum,mul_add]
  ring

theorem actual_macro_release_eq_virtual (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hmPrefix : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (hprefix : ∀ I,∀ k : Fin ((D 0 I).n+1),k.val<r 0 I → columns 0 I k=(D 0 I).frame (basis k))
    (hmw : 0<M.width) (hhp : ∀ I,0<(D 0 I).parentWidth)
    (hw : ∀ I,(D 0 I).width≤(D 0 I).parentWidth)
    (hfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r 0 [i.val]≤(D 0 [i.val]).n)
    (z : Joint E (Blocks m F))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤M.width/4)
    (hblind : ∀ I,∀ k : Fin ((D 0 I).n+1),r 0 I≤k.val →
      |(D 0 I).coordinates (block m 0 z.snd) k|≤(D 0 I).width/4) :
    macroValue M.n M.ell M.width ν M.radius M.frame z.fst+
      outerReleaseCorrection m M (fun i => D 0 [i.val]) z=
    virtualMacroValue M ν rM macroColumns z.fst+
      virtualOuterReleaseCorrection m M D rM r macroColumns columns z := by
  let q : Fin (M.n+1) → ℝ := fun i => (D 0 [i.val]).release (block m 0 z.snd)
  have hq : ∀ i : Fin (M.n+1),rM≤ i.val → q i=0 := by
    intro i hi
    exact ((D 0 [i.val]).release_flat_of_blind_terminal (hhp _) (hw _) _
      (hblind _ (Fin.last _) (hfuture i hi))).1
  have hrel (i : Fin (M.n+1)) : q i=
      virtualRelease (D 0 [i.val]) (r 0 [i.val]) (columns 0 [i.val]) (block m 0 z.snd) :=
    actual_release_eq_virtual _ _ _ (hprefix _) (hhp _) (hw _) _ (hblind _)
  change macroValue M.n M.ell M.width ν M.radius M.frame z.fst+
      (∑ i : Fin (M.n+1),wrappedResidual M i z.fst*(q i-1))=_
  rw [macro_release_closed_formula,closedChain_prefix_value M.n rM M.ell M.width hmw q hq _ hmBlind]
  have hread : readout M.n rM M.radius macroColumns z.fst=retain M.n rM (M.coordinates z.fst) :=
    readout_eq_retained M.n rM M.radius macroColumns M.frame hmPrefix z.fst
  rw [← hread]
  rw [← virtual_macro_release_closed_formula]
  unfold virtualOuterReleaseCorrection
  simp only [hrel]

theorem actual_upperBase_eq_virtual (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (J : ℕ)
    (hJ : 0<J) (ρ R : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hmPrefix : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<r j I → columns j I k=(D j I).frame (basis k))
    (hmw : 0<M.width) (hh : ∀ j I,j≤J → 0<(D j I).width)
    (hhp : ∀ j I,j≤1 → 0<(D j I).parentWidth)
    (hw : ∀ j I,j≤1 → (D j I).width≤(D j I).parentWidth)
    (hmfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r 0 [i.val]≤(D 0 [i.val]).n)
    (hfuture : ∀ I,∀ i : Fin ((D 0 I).n+1),r 0 I≤ i.val →
      r 1 (child I i.val)≤(D 1 (child I i.val)).n)
    (z : Joint E (Blocks m F))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤M.width/4)
    (hblind : ∀ j I,j≤J → ∀ k : Fin ((D j I).n+1),r j I≤k.val →
      |(D j I).coordinates (block m j z.snd) k|≤(D j I).width/4) :
    upperBase m M ν D J ρ R z=virtualUpperBase m M ν D J ρ R rM r macroColumns columns z := by
  have hm := actual_macro_release_eq_virtual m M ν D rM r macroColumns columns hmPrefix (hprefix 0)
    hmw (fun I => hhp 0 I (by omega)) (fun I => hw 0 I (by omega)) hmfuture z hmBlind
    (fun I => hblind 0 I (by omega))
  have hc := actual_outerClosed_eq_virtual m M D J rM r macroColumns columns hmPrefix hprefix hmw hh
    z hmBlind hblind 0 hJ (fun I => hhp 1 I le_rfl) (fun I => hw 1 I le_rfl) hfuture
  change _+(_+_+_)=_+(_+_+_)
  linarith only [hm,hc]

end Bilevel.ChiPrefixEvaluation
