import Bilevel.MultiscaleSignalResidual

/-! The exact informative scalar potential of the multiscale oracle and its
actual gradient. Its global envelope uses the small final flattening error,
not a global amplitude estimate for the difference. -/

noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean SmallGapProfiles SmallGapLiftSupport
open scoped RealInnerProductSpace
set_option maxHeartbeats 600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Parameters
variable {n : ℕ} (P : Parameters (E := E) n)

def signal (y : LowerSpace E) : ℝ :=
  P.μ/(2*P.L^2)*(P.residual (uProj E y)^2-P.inactiveResidual (uProj E y)^2)-
    P.μ/P.L*P.residualDifference (uProj E y)*normal P.finalWidth (sProj E y)

def signalU (y : LowerSpace E) : E :=
  (P.μ/P.L^2) • (P.residualDifference (uProj E y) • gradient P.residual (uProj E y)+
    P.inactiveResidual (uProj E y) • gradient P.residualDifference (uProj E y))-
  (P.μ/P.L*normal P.finalWidth (sProj E y)) • gradient P.residualDifference (uProj E y)

def signalS (y : LowerSpace E) : ℝ :=
  -(P.μ/P.L)*P.residualDifference (uProj E y)*deriv (normal P.finalWidth) (sProj E y)

def signalY (y : LowerSpace E) : LowerSpace E := pack E (P.signalU y) (P.signalS y) 0

def inactivePerturbation (y : LowerSpace E) : ℝ := P.data.perturbation y-P.signal y

theorem signal_contDiff : ContDiff ℝ 3 P.signal := by
  exact (contDiff_const.mul (((P.residual_contDiff.comp (uProj E).contDiff).pow 2).sub
    ((P.inactiveResidual_contDiff.comp (uProj E).contDiff).pow 2))).sub
    ((contDiff_const.mul (P.residualDifference_contDiff.comp (uProj E).contDiff)).mul
      ((normal_contDiff P.finalWidth P.finalWidth_pos).comp (sProj E).contDiff))

theorem inactivePerturbation_contDiff : ContDiff ℝ 3 P.inactivePerturbation :=
  P.data.perturbation_contDiff.sub P.signal_contDiff

theorem signal_hasGradientAt (y : LowerSpace E) : HasGradientAt P.signal (P.signalY y) y := by
  have hr := ((P.residual_contDiff.differentiable (by norm_num) _).hasGradientAt.hasFDerivAt).comp y
    (uProj E).hasFDerivAt
  have ht := ((P.inactiveResidual_contDiff.differentiable (by norm_num) _).hasGradientAt.hasFDerivAt).comp y
    (uProj E).hasFDerivAt
  have hd := ((P.residualDifference_contDiff.differentiable (by norm_num) _).hasGradientAt.hasFDerivAt).comp y
    (uProj E).hasFDerivAt
  have hq := (((normal_contDiff P.finalWidth P.finalWidth_pos).differentiable
    (by norm_num) (sProj E y)).hasDerivAt.hasFDerivAt).comp y (sProj E).hasFDerivAt
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
  rw [P.residualDifference_gradient]
  simp only [residualDifference,inner_sub_left]
  ring

theorem inactivePerturbation_source (y : LowerSpace E) :
    P.inactivePerturbation y = P.μ/(2*P.L^2)*P.inactiveResidual (uProj E y)^2-
      P.μ/P.L*((∑ j ∈ Finset.range (ZeroChainSchedule.levels P.θ),
        P.pieces j (uProj E y)*normal (ZeroChainSchedule.width P.c P.β P.θ j) (sProj E y))+
        (P.pieces (ZeroChainSchedule.levels P.θ) (uProj E y)-P.residualDifference (uProj E y))*
          normal P.finalWidth (sProj E y)) := by
  simp only [inactivePerturbation,CompensatedMean.Data.perturbation,data,signal,
    Finset.sum_range_succ,finalWidth]
  ring

theorem signalY_bound_of_residual_bounds (B : ℝ) (hB : 1 ≤ B)
    (hscale : P.β*P.θ ≤ 1)
    (hb : ∀ u, |P.residualDifference u| ≤ B*P.L*P.β*P.signalResolution ∧
      |P.inactiveResidual u| ≤ B*P.L*P.β^2 ∧
      ‖gradient P.residual u‖ ≤ B*P.L*P.β ∧
      ‖gradient P.residualDifference u‖ ≤ B*P.L*P.β) (y : LowerSpace E) :
    ‖P.signalY y‖ ≤ (B^2*(Real.exp 2+1)+2*C*B*Real.exp 2)*P.μ*P.β^2/P.θ := by
  have hμ := P.μ_pos
  have hL := P.L_pos
  have hβ := P.β_pos
  have hθ : 0 < P.θ := by linarith [P.θ_ge_one]
  have hτ := P.signalResolution_pos
  have hw := P.finalWidth_pos
  have hC := C_pos
  have hBb : 0 ≤ B := by linarith
  have hβ1 : P.β ≤ 1 := by nlinarith [P.θ_ge_one]
  have hβθ : P.β ≤ 1/P.θ := (le_div_iff₀ hθ).mpr (by nlinarith only [hscale])
  obtain ⟨hd,ht,hr,hg⟩ := hb (uProj E y)
  obtain ⟨hq,hq',_⟩ := normal_jet_bounds P.finalWidth (sProj E y) hw
  have hu : ‖P.signalU y‖ ≤
      P.μ/P.L^2*((B*P.L*P.β*P.signalResolution)*(B*P.L*P.β)+(B*P.L*P.β^2)*(B*P.L*P.β))+
      (P.μ/P.L*(C*P.finalWidth))*(B*P.L*P.β) := by
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
  have hs : |P.signalS y| ≤ P.μ/P.L*(B*P.L*P.β*P.signalResolution)*C := by
    unfold signalS
    rw [abs_mul,abs_mul,abs_neg,abs_of_pos (div_pos hμ hL)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by positivity)) hq' (abs_nonneg _) (by positivity)
  have hraw : ‖P.signalY y‖ ≤
      P.μ*B^2*(P.β^2*P.signalResolution+P.β^3)+P.μ*C*B*P.β*(P.finalWidth+P.signalResolution) := by
    have hh := (pack_norm_le (P.signalU y) (P.signalS y) 0).trans (by simpa only [abs_zero,add_zero] using add_le_add hu hs)
    apply hh.trans_eq
    field_simp
    ring
  have ht1 := P.signalResolution_le_width.trans P.finalWidth_scale
  have hw1 := P.finalWidth_scale
  have hτterm : P.β^2*P.signalResolution ≤ Real.exp 2*P.β^2/P.θ := by
    have hh := mul_le_mul_of_nonneg_left ht1 (sq_nonneg P.β)
    have hhh := mul_le_mul_of_nonneg_right hβ1 (show 0 ≤ Real.exp 2*P.β^2/P.θ by positivity)
    ring_nf at hh hhh ⊢
    exact hh.trans hhh
  have hβterm : P.β^3 ≤ P.β^2/P.θ := by
    have hh := mul_le_mul_of_nonneg_left hβθ (sq_nonneg P.β)
    convert hh using 1
    ring
  have hwt : P.β*(P.finalWidth+P.signalResolution) ≤ 2*Real.exp 2*P.β^2/P.θ := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hw1 ht1) hβ.le
    convert hh using 1
    ring
  apply hraw.trans
  have h1 := mul_le_mul_of_nonneg_left (add_le_add hτterm hβterm) (show 0 ≤ P.μ*B^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hwt (show 0 ≤ P.μ*C*B by positivity)
  convert add_le_add h1 h2 using 1 <;> ring

end Parameters

theorem informative_gradient_envelope : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n), P.β*P.θ ≤ 1 →
      ∀ y, ‖P.signalY y‖ ≤ K*P.μ*P.β^2/P.θ := by
  obtain ⟨B,hB,hb⟩ := signal_residual_bounds
  let K := B^2*(Real.exp 2+1)+2*C*B*Real.exp 2
  have hK : 1 ≤ K := by
    have he := Real.exp_pos (2:ℝ)
    have hC := C_one_le
    dsimp [K]
    nlinarith [sq_nonneg B,mul_nonneg (show 0 ≤ C*B by positivity) he.le]
  refine ⟨K,hK,fun E _ _ _ n P hs y => ?_⟩
  apply P.signalY_bound_of_residual_bounds B hB hs _ y
  intro u
  obtain ⟨_,ht,hd,hr,_,hg⟩ := hb E n P u
  exact ⟨hd,ht,hr,hg⟩

end Bilevel.MultiscaleMean
