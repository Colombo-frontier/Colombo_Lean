import Bilevel.PolishedLiteralSignalResidual
import Bilevel.PolishedLiteralLowerBudgets
import Bilevel.ChiConservativeScalar

/-! The actual globally fixed conservative signal and inactive potential
for the manuscript's literal mean, with its actual smooth normal profile. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped RealInnerProductSpace
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry PolishedLiteralCompensated
namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def signal (δ w : ℝ) (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) : ℝ :=
  P.μ/(2*P.L^2)*(P.selectedResidual (uProj (Joint X U) y)^2-P.selectedFlatResidual δ (uProj (Joint X U) y)^2)-
    P.μ/P.L*P.residualDifference δ (uProj (Joint X U) y)*PolishedLiteralCompensated.normal w (sProj (Joint X U) y)

def signalU (δ w : ℝ) (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) : Joint X U :=
  (P.μ/P.L^2) • (P.residualDifference δ (uProj (Joint X U) y) • gradient P.selectedResidual (uProj (Joint X U) y)+
    P.selectedFlatResidual δ (uProj (Joint X U) y) • gradient (P.residualDifference δ) (uProj (Joint X U) y))-
  (P.μ/P.L*PolishedLiteralCompensated.normal w (sProj (Joint X U) y)) • gradient (P.residualDifference δ) (uProj (Joint X U) y)

def signalS (δ w : ℝ) (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) : ℝ :=
  -(P.μ/P.L)*P.residualDifference δ (uProj (Joint X U) y)*deriv (PolishedLiteralCompensated.normal w) (sProj (Joint X U) y)

def signalY (δ w : ℝ) (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) : PolishedLiteralCompensated.LowerSpace (Joint X U) := PolishedLiteralCompensated.pack (Joint X U) (P.signalU δ w y) (P.signalS δ w y) 0

def inactivePerturbation (δ w : ℝ) (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) : ℝ := P.data.perturbation y-P.signal δ w y

theorem signal_contDiff (δ w : ℝ) (hw : 0<w) : ContDiff ℝ 3 (P.signal δ w) := by
  exact (contDiff_const.mul (((P.selectedResidual_contDiff.comp (uProj (Joint X U)).contDiff).pow 2).sub
    (((P.selectedFlatResidual_contDiff δ).comp (uProj (Joint X U)).contDiff).pow 2))).sub
    ((contDiff_const.mul ((P.residualDifference_contDiff δ).comp (uProj (Joint X U)).contDiff)).mul
      ((PolishedLiteralCompensated.normal_contDiff w hw).comp (sProj (Joint X U)).contDiff))

theorem inactivePerturbation_contDiff (δ w : ℝ) (hw : 0<w) : ContDiff ℝ 3 (P.inactivePerturbation δ w) :=
  P.data.perturbation_contDiff.sub (P.signal_contDiff δ w hw)

theorem signal_hasGradientAt (δ w : ℝ) (hw : 0<w) (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) : HasGradientAt (P.signal δ w) (P.signalY δ w y) y := by
  have hr := ((P.selectedResidual_contDiff.differentiable (by norm_num) _).hasGradientAt.hasFDerivAt).comp y
    (uProj (Joint X U)).hasFDerivAt
  have ht := (((P.selectedFlatResidual_contDiff δ).differentiable (by norm_num) _).hasGradientAt.hasFDerivAt).comp y
    (uProj (Joint X U)).hasFDerivAt
  have hd := (((P.residualDifference_contDiff δ).differentiable (by norm_num) _).hasGradientAt.hasFDerivAt).comp y
    (uProj (Joint X U)).hasFDerivAt
  have hq := (((PolishedLiteralCompensated.normal_contDiff w hw).differentiable
    (by norm_num) (sProj (Joint X U) y)).hasDerivAt.hasFDerivAt).comp y (sProj (Joint X U)).hasFDerivAt
  have h := (((hr.mul hr).sub (ht.mul ht)).const_mul (P.μ/(2*P.L^2))).sub
    ((hd.const_mul (P.μ/P.L)).mul hq)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  · funext v
    simp only [signal,pow_two,Function.comp_apply]
  apply ContinuousLinearMap.ext
  intro v
  simp only [signalY,signalU,signalS,InnerProductSpace.toDual_apply,inner_pack,inner_sub_left,
    inner_add_left,real_inner_smul_left,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.one_apply,smul_eq_mul,
    zero_mul,add_zero,Function.comp_apply]
  rw [P.residualDifference_gradient δ]
  simp only [Parameters.residualDifference,Pi.sub_apply,inner_sub_left]
  ring



theorem signalY_raw_bound (δ w B : ℝ) (hB : 1≤B)
    (hμ : 0<P.μ) (hL : 0<P.L) (hβ : 0<P.β)
    (hw : 0<w) (hδ : 0<δ)
    (hb : ∀ z : Joint X U,|P.residualDifference δ z|≤B*P.L*P.β*δ ∧
      |P.selectedFlatResidual δ z|≤B*P.L*P.β^2 ∧
      ‖gradient P.selectedResidual z‖≤B*P.L*P.β ∧
      ‖gradient (P.residualDifference δ) z‖≤B*P.L*P.β)
    (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) :
    ‖P.signalY δ w y‖≤P.μ*B^2*(P.β^2*δ+P.β^3)+
      P.μ*PolishedLiteralCompensated.C*B*P.β*(w+δ) := by
  have hC := PolishedLiteralCompensated.C_pos
  have hB0 : 0≤B := by linarith
  obtain ⟨hd,ht,hr,hg⟩ := hb (uProj (Joint X U) y)
  have hq : |PolishedLiteralCompensated.normal w (sProj (Joint X U) y)|≤PolishedLiteralCompensated.C*w := by
    simpa only [Fin.val_zero,iteratedDeriv_zero,pow_zero,div_one] using
      PolishedLiteralCompensated.normal_C_bound w (sProj (Joint X U) y) hw 0
  have hq' : |deriv (PolishedLiteralCompensated.normal w) (sProj (Joint X U) y)|≤PolishedLiteralCompensated.C := by
    have hh := PolishedLiteralCompensated.normal_C_bound w (sProj (Joint X U) y) hw 1
    simpa only [Fin.val_one,iteratedDeriv_one,pow_one,mul_div_cancel_right₀ _ hw.ne'] using hh
  have hu : ‖P.signalU δ w y‖≤
      P.μ/P.L^2*((B*P.L*P.β*δ)*(B*P.L*P.β)+(B*P.L*P.β^2)*(B*P.L*P.β))+
      (P.μ/P.L*(PolishedLiteralCompensated.C*w))*(B*P.L*P.β) := by
    unfold signalU
    apply (norm_sub_le _ _).trans
    rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hμ (sq_pos_of_pos hL)),
      Real.norm_eq_abs,abs_mul,abs_of_pos (div_pos hμ hL)]
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_add_le _ _).trans
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul hd hr (norm_nonneg _) (by positivity))
        (mul_le_mul ht hg (norm_nonneg _) (by positivity))
    · exact mul_le_mul (mul_le_mul_of_nonneg_left hq (by positivity)) hg (norm_nonneg _) (by positivity)
  have hs : |P.signalS δ w y|≤P.μ/P.L*(B*P.L*P.β*δ)*PolishedLiteralCompensated.C := by
    unfold signalS
    rw [abs_mul,abs_mul,abs_neg,abs_of_pos (div_pos hμ hL)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by positivity)) hq' (abs_nonneg _) (by positivity)
  have hraw : ‖P.signalY δ w y‖≤
      P.μ*B^2*(P.β^2*δ+P.β^3)+P.μ*PolishedLiteralCompensated.C*B*P.β*(w+δ) := by
    have hh := (PolishedLiteralCompensated.pack_norm_le (P.signalU δ w y) (P.signalS δ w y) 0).trans
      (by simpa only [abs_zero,add_zero] using add_le_add hu hs)
    apply hh.trans_eq
    field_simp
    ring
  exact hraw

theorem signalY_bound_of_residual_bounds (δ w B : ℝ) (hB : 1≤B)
    (hμ : 0<P.μ) (hL : 0<P.L) (hβ : 0<P.β) (hβ1 : P.β≤1)
    (hw : 0<w) (hw1 : w≤1) (hδ : 0<δ) (hδ1 : δ≤1)
    (hb : ∀ z : Joint X U,|P.residualDifference δ z|≤B*P.L*P.β*δ ∧
      |P.selectedFlatResidual δ z|≤B*P.L*P.β^2 ∧
      ‖gradient P.selectedResidual z‖≤B*P.L*P.β ∧
      ‖gradient (P.residualDifference δ) z‖≤B*P.L*P.β)
    (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) :
    ‖P.signalY δ w y‖≤(2*B^2+2*PolishedLiteralCompensated.C*B)*P.μ*P.β := by
  have hC := PolishedLiteralCompensated.C_pos
  have hB0 : 0≤B := by linarith
  obtain ⟨hd,ht,hr,hg⟩ := hb (uProj (Joint X U) y)
  have hq : |PolishedLiteralCompensated.normal w (sProj (Joint X U) y)|≤PolishedLiteralCompensated.C*w := by
    simpa only [Fin.val_zero,iteratedDeriv_zero,pow_zero,div_one] using
      PolishedLiteralCompensated.normal_C_bound w (sProj (Joint X U) y) hw 0
  have hq' : |deriv (PolishedLiteralCompensated.normal w) (sProj (Joint X U) y)|≤PolishedLiteralCompensated.C := by
    have hh := PolishedLiteralCompensated.normal_C_bound w (sProj (Joint X U) y) hw 1
    simpa only [Fin.val_one,iteratedDeriv_one,pow_one,mul_div_cancel_right₀ _ hw.ne'] using hh
  have hu : ‖P.signalU δ w y‖≤
      P.μ/P.L^2*((B*P.L*P.β*δ)*(B*P.L*P.β)+(B*P.L*P.β^2)*(B*P.L*P.β))+
      (P.μ/P.L*(PolishedLiteralCompensated.C*w))*(B*P.L*P.β) := by
    unfold signalU
    apply (norm_sub_le _ _).trans
    rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hμ (sq_pos_of_pos hL)),
      Real.norm_eq_abs,abs_mul,abs_of_pos (div_pos hμ hL)]
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_add_le _ _).trans
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul hd hr (norm_nonneg _) (by positivity))
        (mul_le_mul ht hg (norm_nonneg _) (by positivity))
    · exact mul_le_mul (mul_le_mul_of_nonneg_left hq (by positivity)) hg (norm_nonneg _) (by positivity)
  have hs : |P.signalS δ w y|≤P.μ/P.L*(B*P.L*P.β*δ)*PolishedLiteralCompensated.C := by
    unfold signalS
    rw [abs_mul,abs_mul,abs_neg,abs_of_pos (div_pos hμ hL)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by positivity)) hq' (abs_nonneg _) (by positivity)
  have hraw : ‖P.signalY δ w y‖≤
      P.μ*B^2*(P.β^2*δ+P.β^3)+P.μ*PolishedLiteralCompensated.C*B*P.β*(w+δ) := by
    have hh := (PolishedLiteralCompensated.pack_norm_le (P.signalU δ w y) (P.signalS δ w y) 0).trans
      (by simpa only [abs_zero,add_zero] using add_le_add hu hs)
    apply hh.trans_eq
    field_simp
    ring
  have hb2 : P.β^2≤P.β := by nlinarith
  have hb3 : P.β^3≤P.β := by nlinarith [mul_le_mul_of_nonneg_left hb2 hβ.le]
  have hdterm : P.β^2*δ≤P.β := (mul_le_mul_of_nonneg_left hδ1 (sq_nonneg P.β)).trans (by simpa using hb2)
  have hwterm : P.β*(w+δ)≤2*P.β := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left (add_le_add hdterm hb3) (show 0≤P.μ*B^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hwterm (show 0≤P.μ*PolishedLiteralCompensated.C*B by positivity)
  apply hraw.trans
  convert add_le_add h1 h2 using 1 <;> ring


theorem signalY_scaled_bound (δ w θ B : ℝ) (hB : 1≤B)
    (hμ : 0<P.μ) (hL : 0<P.L) (hβ : 0<P.β) (hθ : 1≤θ) (hscale : P.β*θ≤1)
    (hw : 0<w) (hws : w≤Real.exp 2*P.β/θ) (hδ : 0<δ) (hδw : δ≤w)
    (hb : ∀ z : Joint X U,|P.residualDifference δ z|≤B*P.L*P.β*δ ∧
      |P.selectedFlatResidual δ z|≤B*P.L*P.β^2 ∧
      ‖gradient P.selectedResidual z‖≤B*P.L*P.β ∧
      ‖gradient (P.residualDifference δ) z‖≤B*P.L*P.β)
    (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) :
    ‖P.signalY δ w y‖≤(B^2*(Real.exp 2+1)+2*PolishedLiteralCompensated.C*B*Real.exp 2)*P.μ*P.β^2/θ := by
  have hraw := P.signalY_raw_bound δ w B hB hμ hL hβ hw hδ hb y
  have hθ0 : 0<θ := lt_of_lt_of_le zero_lt_one hθ
  have hβ1 : P.β≤1 := by nlinarith [mul_le_mul_of_nonneg_left hθ hβ.le]
  have hβθ : P.β≤1/θ := (le_div_iff₀ hθ0).mpr (by nlinarith only [hscale])
  have ht1 := hδw.trans hws
  have hτterm : P.β^2*δ≤Real.exp 2*P.β^2/θ := by
    have hh := mul_le_mul_of_nonneg_left ht1 (sq_nonneg P.β)
    have hhh := mul_le_mul_of_nonneg_right hβ1
      (show 0≤Real.exp 2*P.β^2/θ by positivity)
    ring_nf at hh hhh ⊢
    exact hh.trans hhh
  have hβterm : P.β^3≤P.β^2/θ := by
    have hh := mul_le_mul_of_nonneg_left hβθ (sq_nonneg P.β)
    convert hh using 1
    ring
  have hwt : P.β*(w+δ)≤2*Real.exp 2*P.β^2/θ := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hws ht1) hβ.le
    convert hh using 1
    ring
  apply hraw.trans
  have h1 := mul_le_mul_of_nonneg_left (add_le_add hτterm hβterm) (show 0≤P.μ*B^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hwt (show 0≤P.μ*PolishedLiteralCompensated.C*B by
    have := PolishedLiteralCompensated.C_pos;positivity)
  convert add_le_add h1 h2 using 1 <;> ring

theorem inactivePerturbation_source (δ : ℝ) (y : PolishedLiteralCompensated.LowerSpace (Joint X U)) :
    P.inactivePerturbation δ (P.w P.J) y=
      P.μ/(2*P.L^2)*(P.selectedFlatResidual δ (uProj (Joint X U) y))^2-
      P.μ/P.L*((∑ j ∈ Finset.range P.J,P.selectedPiece j (uProj (Joint X U) y)*
        PolishedLiteralCompensated.normal (P.w j) (sProj (Joint X U) y))+
        (P.selectedPiece P.J (uProj (Joint X U) y)-P.residualDifference δ (uProj (Joint X U) y))*
          PolishedLiteralCompensated.normal (P.w P.J) (sProj (Joint X U) y)) := by
  simp only [inactivePerturbation,signal,Parameters.data,PolishedLiteralCompensated.Data.perturbation,
    Finset.sum_range_succ]
  ring

def signalFull (δ w : ℝ) : FullMeanSpace (X:=X) (U:=U) → ℝ :=
  P.signal δ w ∘ fullLowerEmbed

def inactiveSourceLower (δ w : ℝ) : FullMeanSpace (X:=X) (U:=U) → ℝ :=
  P.sourceLower-P.signalFull δ w

theorem signalFull_contDiff (δ w : ℝ) (hw : 0<w) : ContDiff ℝ 3 (P.signalFull δ w) :=
  (P.signal_contDiff δ w hw).comp (fullLowerEmbed (X:=X) (U:=U)).contDiff

theorem inactiveSourceLower_contDiff (δ w : ℝ) (hw : 0<w) : ContDiff ℝ 3 (P.inactiveSourceLower δ w) :=
  P.sourceLower_contDiff.sub (P.signalFull_contDiff δ w hw)

theorem signalFull_gradient_bound (δ w : ℝ) (hw : 0<w) (q : FullMeanSpace (X:=X) (U:=U)) :
    ‖gradient (P.signalFull δ w) q‖≤‖P.signalY δ w (fullLowerEmbed q)‖ := by
  have hf := (P.signal_contDiff δ w hw).differentiable (by norm_num) (fullLowerEmbed q)
  have ht := (fullLowerEmbed (X:=X) (U:=U)).differentiableAt (x:=q)
  rw [GradientJetBounds.gradient_norm_eq]
  change ‖fderiv ℝ (P.signal δ w ∘ fullLowerEmbed) q‖≤_
  rw [fderiv_comp q hf ht,(fullLowerEmbed (X:=X) (U:=U)).fderiv]
  have hop := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ (P.signal δ w) (fullLowerEmbed q))
    (fullLowerEmbed (X:=X) (U:=U))
  have hmult := mul_le_mul_of_nonneg_left (fullLowerEmbed_norm (X:=X) (U:=U))
    (norm_nonneg (fderiv ℝ (P.signal δ w) (fullLowerEmbed q)))
  have he : ‖fderiv ℝ (P.signal δ w) (fullLowerEmbed q)‖=‖P.signalY δ w (fullLowerEmbed q)‖ := by
    rw [← GradientJetBounds.gradient_norm_eq,(P.signal_hasGradientAt δ w hw _).gradient]
  exact hop.trans (by simpa only [mul_one,he] using hmult)

theorem source_gradient_difference_eq_signal (δ w : ℝ) (hw : 0<w) (q : FullMeanSpace (X:=X) (U:=U)) :
    gradient P.sourceLower q-gradient (P.inactiveSourceLower δ w) q=gradient (P.signalFull δ w) q := by
  have he : P.inactiveSourceLower δ w=fun z => P.sourceLower z-P.signalFull δ w z := rfl
  rw [he]
  simp only [gradient]
  rw [fderiv_sub (P.sourceLower_contDiff.differentiable (by norm_num) q)
    ((P.signalFull_contDiff δ w hw).differentiable (by norm_num) q),map_sub]
  abel

end Parameters

theorem literal_conservative_gradient_envelope : ∃ K : ℝ,0<K ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (δ w : ℝ),
      0<P.μ → 0<P.L → 0<P.β → P.β≤1 → 0<δ → δ≤P.β/16 → 0<w → w≤1 →
      P.β≤P.radius → P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      ∀ q : FullMeanSpace (X:=X) (U:=U),
      ‖gradient P.sourceLower q-gradient (P.inactiveSourceLower δ w) q‖≤K*P.μ*P.β := by
  obtain ⟨B,hB,hb⟩ := signal_residual_c1_bounds
  let K := 2*B^2+2*PolishedLiteralCompensated.C*B
  have hK : 0<K := by
    have hN := PolishedLiteralCompensated.C_pos
    dsimp [K]
    positivity
  refine ⟨K,hK,?_⟩
  intro X U _ _ _ _ _ _ P δ w hμ hL hβ hβ1 hδ hδs hw hw1 hR hβb hbR q
  rw [P.source_gradient_difference_eq_signal δ w hw]
  apply (P.signalFull_gradient_bound δ w hw q).trans
  apply P.signalY_bound_of_residual_bounds δ w B hB hμ hL hβ hβ1 hw hw1 hδ (by linarith)
  exact hb X U P δ hL.le hβ hδ hδs hR hβb hbR

end Bilevel.PolishedLiteral
