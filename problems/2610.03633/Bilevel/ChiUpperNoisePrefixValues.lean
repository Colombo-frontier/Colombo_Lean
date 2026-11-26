import Bilevel.ChiUpperNoiseOracle
import Bilevel.ChiUpperNoiseNodePrefix
import Bilevel.ChiVirtualUpperValues
import Bilevel.ChiVirtualOuterFineValues

/-! Actual direct upper-noise scalar replies from old/new finite prefixes.
Macro cancellation is included; only reachable active leaves need advance. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem actual_direct_carrier_eq_virtual (m : ℕ) (M : Node E) (D : Geometry F) (rM sM : ℕ)
    (r a : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hm : ∀ k : Fin (M.n+1),k.val<sM → macroColumns k=M.frame (basis k))
    (hp : ∀ I,∀ k : Fin ((D 0 I).n+1),k.val<a 0 I → columns 0 I k=(D 0 I).frame (basis k))
    (hms : rM≤sM) (hra : ∀ I,r 0 I≤a 0 I)
    (hmw : 0<M.width) (hh : ∀ I,0<(D 0 I).width)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM → (D 0 [i.val]).n<r 0 [i.val] ∨ r 0 [i.val]<a 0 [i.val])
    (z : Joint E (Blocks m F))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤M.width/4)
    (hblind : ∀ I,∀ k : Fin ((D 0 I).n+1),r 0 I≤k.val →
      |(D 0 I).coordinates (block m 0 z.snd) k|≤(D 0 I).width/4) :
    outerCarrier m M D 0 0 z=virtualOuterCarrier m M D sM a macroColumns columns 0 0 z := by
  unfold outerCarrier outerSelected virtualOuterCarrier
  apply Finset.sum_congr rfl
  intro i _
  change wrappedSelector M i z.fst*((D 0 [i.val]).H (block m 0 z.snd)-(D 0 [i.val]).H 0)=_
  have hsel := actual_outerSelector_eq_virtual M sM macroColumns hm hmw i z.fst
    (fun k hk => hmBlind k (hms.trans hk))
  by_cases hi : i.val≤rM
  · rw [hsel]
    change _*_= _*(virtualH (D 0 [i.val]) (a 0 [i.val]) (columns 0 [i.val]) (block m 0 z.snd)-
      virtualH (D 0 [i.val]) (a 0 [i.val]) (columns 0 [i.val]) 0)
    rw [actual_direct_payload_eq_virtual (D 0 [i.val]) (r 0 [i.val]) (a 0 [i.val])
      (columns 0 [i.val]) (hp _) (hh _) (hra _) (hfront i hi) _ (hblind _),actual_zero_eq_virtual]
  · have hz : wrappedSelector M i z.fst=0 :=
      outer_selector_future_zero M.n rM _ (fun k hk =>
        ZeroChainResidualScaled.scaled_coordinate_small M.width hmw (M.coordinates z.fst) k
          (hmBlind k hk)) i (by omega)
    rw [← hsel,hz,zero_mul,zero_mul]

theorem direct_core_eq_virtual (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (rM sM : ℕ) (r a : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hm : ∀ k : Fin (M.n+1),k.val<sM → macroColumns k=M.frame (basis k))
    (hp : ∀ I,∀ k : Fin ((D 0 I).n+1),k.val<a 0 I → columns 0 I k=(D 0 I).frame (basis k))
    (hms : rM≤sM) (hra : ∀ I,r 0 I≤a 0 I)
    (hmw : 0<M.width) (hh : ∀ I,0<(D 0 I).width)
    (hhp : ∀ I,0<(D 0 I).parentWidth) (hw : ∀ I,(D 0 I).width≤(D 0 I).parentWidth)
    (hfuture : ∀ i : Fin (M.n+1),sM≤ i.val → a 0 [i.val]≤(D 0 [i.val]).n)
    (hfront : ∀ i : Fin (M.n+1),i.val≤rM → (D 0 [i.val]).n<r 0 [i.val] ∨ r 0 [i.val]<a 0 [i.val])
    (z : Joint E (Blocks m F))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤M.width/4)
    (hblind : ∀ I,∀ k : Fin ((D 0 I).n+1),r 0 I≤k.val →
      |(D 0 I).coordinates (block m 0 z.snd) k|≤(D 0 I).width/4) :
    ChiUpperNoise.core m M ν D ρ R z=
      virtualUpperBase m M ν D 0 (ρ 0) (R 0) sM a macroColumns columns z := by
  have hmacro := actual_macro_release_eq_virtual m M ν D sM a macroColumns columns hm hp hmw hhp hw
    hfuture z (fun k hk => hmBlind k (hms.trans hk))
      (fun I k hk => hblind I k ((hra I).trans hk))
  have hcarrier := actual_direct_carrier_eq_virtual m M D rM sM r a macroColumns columns hm hp
    hms hra hmw hh hfront z hmBlind hblind
  rw [ChiUpperNoise.core_eq_upperBase]
  unfold upperBase baseLower virtualUpperBase
  linarith only [hmacro,hcarrier]

def virtualDirectInactive (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F) (z : Joint E (Blocks m F)) : ℝ :=
  virtualUpperBase m M ν D 0 (ρ 0) (R 0) rM r macroColumns columns z-
    virtualOuterLeaf m M D rM r macroColumns columns (signalLeaf D ((D 0 []).width/16)) 0 z

theorem direct_inactive_core_eq_virtual (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (rM : ℕ) (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hm : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (hp : ∀ I,∀ k : Fin ((D 0 I).n+1),k.val<r 0 I → columns 0 I k=(D 0 I).frame (basis k))
    (hmw : 0<M.width) (hh : ∀ I,0<(D 0 I).width)
    (hhp : ∀ I,0<(D 0 I).parentWidth) (hw : ∀ I,(D 0 I).width≤(D 0 I).parentWidth)
    (hwidth : ∀ I,(D 0 I).width=(D 0 []).width)
    (hfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r 0 [i.val]≤(D 0 [i.val]).n)
    (z : Joint E (Blocks m F))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤M.width/4)
    (hblind : ∀ I,∀ k : Fin ((D 0 I).n+1),r 0 I≤k.val →
      |(D 0 I).coordinates (block m 0 z.snd) k|≤(D 0 []).width/16) :
    ChiUpperNoise.inactiveCore m M ν D ρ R z=
      virtualDirectInactive m M ν D ρ R rM r macroColumns columns z := by
  have hb (I : List ℕ) (k : Fin ((D 0 I).n+1)) (hk : r 0 I≤k.val) :
      |(D 0 I).coordinates (block m 0 z.snd) k|≤(D 0 I).width/4 := by
    have h := hblind I k hk
    rw [hwidth I]
    have hw0 := hh []
    linarith
  have hmacro := actual_macro_release_eq_virtual m M ν D rM r macroColumns columns hm hp hmw hhp hw
    hfuture z hmBlind hb
  have hcarrier : outerCarrier m M D 0 0 z-ChiUpperNoise.signal m M D z=
      virtualOuterCarrier m M D rM r macroColumns columns 0 0 z-
        virtualOuterLeaf m M D rM r macroColumns columns (signalLeaf D ((D 0 []).width/16)) 0 z := by
    simp only [outerCarrier,ChiUpperNoise.signal,outerFineSignal,outerSelected,virtualOuterCarrier,virtualOuterLeaf]
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_sub,← mul_sub]
    change wrappedSelector M i z.fst*((D 0 [i.val]).H (block m 0 z.snd)-(D 0 [i.val]).H 0-
      ChiFine.signalResidual (D 0 [i.val]).n (D 0 [i.val]).ell (D 0 [i.val]).width ((D 0 []).width/16)
        ((D 0 [i.val]).coordinates (block m 0 z.snd)))=_
    rw [actual_outerSelector_eq_virtual M rM macroColumns hm hmw i z.fst hmBlind]
    congr 1
    change _=virtualH (D 0 [i.val]) (r 0 [i.val]) (columns 0 [i.val]) (block m 0 z.snd)-
      virtualH (D 0 [i.val]) (r 0 [i.val]) (columns 0 [i.val]) 0-
      signalLeaf D ((D 0 []).width/16) 0 [i.val]
        (readout (D 0 [i.val]).n (r 0 [i.val]) (D 0 [i.val]).radius (columns 0 [i.val]) (block m 0 z.snd))
    rw [← actual_zero_eq_virtual]
    unfold Node.H virtualH signalLeaf ChiFine.signalResidual
    rw [readout_eq_retained _ _ _ _ _ (hp [i.val])]
    have he := direct_inactive_payload_value_eq_retain (D 0 [i.val]).n (r 0 [i.val])
      (D 0 [i.val]).ell (D 0 [i.val]).width (D 0 [i.val]).receiver (D 0 [i.val]).nu
      (D 0 [i.val]).force (D 0 [i.val]).parentWidth (D 0 [i.val]).tailRadius ((D 0 []).width/16)
      (hh _) (div_pos (hh []) (by norm_num)) (by rw [hwidth [i.val]]) ((D 0 [i.val]).coordinates (block m 0 z.snd)) (hblind _)
    dsimp only [Node.coordinates] at he ⊢
    linarith only [he]
  unfold ChiUpperNoise.inactiveCore virtualDirectInactive
  rw [ChiUpperNoise.core_eq_upperBase]
  unfold upperBase baseLower virtualUpperBase
  linarith only [hmacro,hcarrier]

end Bilevel.ChiPrefixEvaluation

