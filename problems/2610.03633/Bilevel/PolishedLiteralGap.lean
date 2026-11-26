import Bilevel.PolishedLiteralMicroMean
import Bilevel.PolishedLiteralSize
import Bilevel.ChiBoundedChainReceiverBounds
import Bilevel.WrappedChainGap

/-! Explicit global value and gap bounds for the literal additive mean.
The literal exponential activation contributes its factor exp(1) to each
chain and to the selected sum. Only the unselected public radial bowls are
used for coercivity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Bilevel.PolishedLiteral.Parameters
open PrimitiveGeometry ChiRecursive ChiBoundedChain RadialWrapper ZeroChainPotential
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (P : Parameters (X:=X) (U:=U))

omit [CompleteSpace U] in
private theorem literal_macro_zero :
    PolishedLiteral.macroValue P.macroNode.n P.macroNode.ell P.macroNode.width
      P.macroRadial P.macroNode.radius P.macroNode.frame 0 =
      -(P.macroNode.ell*P.macroNode.width^2)*phi 0 := by
  simp [PolishedLiteral.macroValue,wrapped,compress,bowl,chain,ZeroChainResidualScaled.scaled,value_zero]

def microBudget : ℝ := ((P.n:ℝ)+1)*Real.exp 1*gaussianBound*(P.L*P.β^2)+
  (P.receiver*(3*P.ν*P.macroNode.width+P.force))*(3*P.macroNode.width)

def gapBudget : ℝ := ((P.macroNode.n:ℝ)+1)*Real.exp 1*gaussianBound*(P.macroNode.ell*P.macroNode.width^2)+
  Real.exp 1*P.microBudget

omit [CompleteSpace X] [CompleteSpace U] in
theorem microBudget_nonneg (hL : 0≤P.L) (hA : 0≤P.receiver) (hν : 0≤P.ν)
    (hg : 0≤P.force) (hb : 0≤P.macroNode.width) : 0≤P.microBudget := by
  unfold microBudget gaussianBound
  positivity

omit [CompleteSpace X] in
theorem microCore_lower (hL : 0≤P.L) (hA : 0≤P.receiver) (hν : 0≤P.ν)
    (hg : 0≤P.force) (hβ : 0<P.β) (hb : 0<P.macroNode.width)
    (i : Fin (P.macroNode.n+1)) (u : U) : -P.microBudget≤P.microCore i u := by
  have hc := PolishedLiteral.chain_lower P.n P.L P.β hL (P.coordinates i u)
  have hd := (abs_le.mp (positiveReceiver_abs_bound P.receiver P.ν P.force P.β
    P.macroNode.width (P.terminal i u) hA hν hg hβ hb)).1
  dsimp only [microBudget,microCore]
  linarith

theorem selectedCore_lower (hL : 0≤P.L) (hA : 0≤P.receiver) (hν : 0≤P.ν)
    (hg : 0≤P.force) (hβ : 0<P.β) (hb : 0<P.macroNode.width)
    (z : Joint X U) :
    -(Real.exp 1*P.microBudget)≤∑ i : Fin (P.macroNode.n+1),
      PolishedLiteral.wrappedSelector P.macroNode i z.fst*P.microCore i z.snd := by
  have hB := P.microBudget_nonneg hL hA hν hg hb.le
  have hs := PolishedLiteral.selector_sum_le_exp_one P.macroNode.n
    (P.macroNode.width⁻¹ • P.macroNode.coordinates z.fst)
  have hl := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin (P.macroNode.n+1)))) =>
    mul_le_mul_of_nonneg_left (P.microCore_lower hL hA hν hg hβ hb i z.snd)
      (PolishedLiteral.selector_nonneg P.macroNode.n i
        (P.macroNode.width⁻¹ • P.macroNode.coordinates z.fst)))
  change (∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedSelector P.macroNode i z.fst*(-P.microBudget))≤_ at hl
  rw [← Finset.sum_mul] at hl
  have hprod := mul_le_mul_of_nonpos_right hs (neg_nonpos.mpr hB)
  simpa only [mul_neg] using hprod.trans hl

theorem releaseCorrection_nonneg (hℓ : 0≤P.macroNode.ell) (z : Joint X U) :
    0≤∑ i : Fin (P.macroNode.n+1),
      PolishedLiteral.wrappedResidual P.macroNode i z.fst*(P.microRelease i z.snd-1) := by
  apply Finset.sum_nonneg
  intro i _
  have hr : PolishedLiteral.wrappedResidual P.macroNode i z.fst≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (PolishedLiteral.residualTerm_nonpos P.macroNode.n i _)
  have hq : P.microRelease i z.snd≤1 := Real.smoothTransition.le_one _
  exact mul_nonneg_of_nonpos_of_nonpos hr (by linarith)

theorem meanBase_lower (hℓ : 0≤P.macroNode.ell) (hL : 0≤P.L) (hA : 0≤P.receiver)
    (hν : 0≤P.ν) (hg : 0≤P.force) (hβ : 0<P.β) (hb : 0<P.macroNode.width)
    (z : Joint X U) :
    bowl P.macroRadial P.macroNode.radius z.fst+bowl P.ν P.radius z.snd-P.gapBudget≤P.meanBase z := by
  have hc := PolishedLiteral.chain_lower P.macroNode.n P.macroNode.ell P.macroNode.width hℓ
    (WrappedChain.coordinates P.macroNode.n P.macroNode.radius P.macroNode.frame z.fst)
  have hm := P.selectedCore_lower hL hA hν hg hβ hb z
  have hr := P.releaseCorrection_nonneg hℓ z
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib] at hr
  dsimp only [meanBase,macroCarrier,gapBudget,PolishedLiteral.macroValue,wrapped]
  dsimp only [WrappedChain.coordinates] at hc
  linarith

omit [CompleteSpace U] in
theorem macroCarrier_zero : P.macroCarrier 0=0 := by
  have hc : P.macroNode.coordinates 0=0 := P.macroNode.coordinates_zero
  have hr := normalizedResidual_zero P.macroNode.n
  have hs : (∑ i : Fin (P.macroNode.n+1),PolishedLiteral.residualTerm P.macroNode.n i 0)=-phi 0 := by
    unfold normalizedResidual at hr
    linarith
  rw [macroCarrier,P.literal_macro_zero]
  simp only [PolishedLiteral.wrappedResidual,hc,smul_zero,← Finset.mul_sum,hs]
  ring

omit [CompleteSpace X] in
theorem microCore_zero (i : Fin (P.macroNode.n+1)) : P.microCore i 0=-(P.L*P.β^2)*phi 0 := by
  have hc : P.coordinates i 0=0 := by simp [coordinates,WrappedChain.coordinates,compress]
  simp only [microCore,terminal,hc,PiLp.zero_apply,positiveReceiver,primitive_zero,add_zero,
    PolishedLiteral.chain,ZeroChainResidualScaled.scaled,smul_zero,PolishedLiteral.value_zero]
  ring

theorem meanBase_zero_nonpos (hL : 0≤P.L) : P.meanBase 0≤0 := by
  have hr (i : Fin (P.macroNode.n+1)) : P.microRelease i 0=0 := by
    have hc : P.coordinates i 0=0 := by simp [coordinates,WrappedChain.coordinates,compress]
    simp only [microRelease,terminal,hc,PiLp.zero_apply,zero_div]
    exact releaseGate_zero (by norm_num)
  change P.macroCarrier 0+bowl P.ν P.radius (0:U)+
    (∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedSelector P.macroNode i 0*P.microCore i 0)+
    (∑ i : Fin (P.macroNode.n+1),PolishedLiteral.wrappedResidual P.macroNode i 0*P.microRelease i 0)≤0
  have hbow : bowl P.ν P.radius (0:U)=0 := by simp [bowl]
  rw [P.macroCarrier_zero]
  simp only [hr,mul_zero,Finset.sum_const_zero,add_zero,zero_add,hbow]
  apply Finset.sum_nonpos
  intro i _
  rw [P.microCore_zero]
  exact mul_nonpos_of_nonneg_of_nonpos (PolishedLiteral.selector_nonneg P.macroNode.n i _)
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hL (sq_nonneg _))) (phi_nonneg 0))

theorem outerMean_gap_to_infimum (κ : ℝ) (hℓ : 0≤P.macroNode.ell) (hL : 0≤P.L)
    (hA : 0≤P.receiver) (hν : 0≤P.ν) (hmacro : 0≤P.macroRadial) (hg : 0≤P.force)
    (hβ : 0<P.β) (hb : 0<P.macroNode.width) :
    P.outerMean κ 0-sInf (Set.range (P.outerMean κ))≤P.gapBudget := by
  have hlow (z : Joint X U) : -P.gapBudget≤P.outerMean κ z := by
    have h := P.meanBase_lower hℓ hL hA hν hg hβ hb (pack z.fst (κ • z.snd))
    have h0 := bowl_nonnegative P.macroRadial P.macroNode.radius hmacro z.fst
    have h1 := bowl_nonnegative P.ν P.radius hν (κ • z.snd)
    change bowl P.macroRadial P.macroNode.radius z.fst+bowl P.ν P.radius (κ • z.snd)-P.gapBudget≤P.outerMean κ z at h
    linarith
  have hi : -P.gapBudget≤sInf (Set.range (P.outerMean κ)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨z,rfl⟩
    exact hlow z
  have hz : P.outerMean κ 0≤0 := by
    simpa only [outerMean,show (0:Joint X U).fst=0 from rfl,
      show (0:Joint X U).snd=0 from rfl,smul_zero,show pack (0:X) (0:U)=0 from rfl]
      using P.meanBase_zero_nonpos hL
  linarith

end Bilevel.PolishedLiteral.Parameters
