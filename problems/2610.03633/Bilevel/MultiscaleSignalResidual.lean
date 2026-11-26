import Bilevel.MultiscaleMeanCore
import Bilevel.GradientJetBounds

/-! The actual final-resolution flattened residual used by the inactive
oracle, with amplitude, gradient, and approximation bounds. -/

noncomputable section
namespace Bilevel.MultiscaleMean
open ZeroChain ZeroChainSchedule ZeroChainFlatteningBounds ZeroChainFlatteningError

theorem wrapped_flat_bounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (a β δ R : ℝ), 0 ≤ a → 0 < β → 0 < δ → δ ≤ β/16 → 0 < R →
      ∀ (U : Space n →ₗᵢ[ℝ] E) (u : E),
        |flattenedResidual n a β δ (WrappedChain.coordinates n R U u)| ≤ C*a ∧
        ‖gradient (flattenedResidual n a β δ ∘ WrappedChain.coordinates n R U) u‖ ≤ C*a/β ∧
        |ZeroChainWrappedResidual.residual n a β R U u-
          flattenedResidual n a β δ (WrappedChain.coordinates n R U u)| ≤ C*a*δ/β := by
  obtain ⟨B,hB,hb⟩ := amplitude_derivative_bounds
  let C := B+errorConstant
  have hBC : B ≤ C := le_add_of_nonneg_right errorConstant_pos.le
  have heC : errorConstant ≤ C := by dsimp [C]; linarith
  refine ⟨C,hB.trans hBC,fun E _ _ _ n a β δ R ha hβ hδ hδβ hR U u => ?_⟩
  let f := flattenedResidual n a β δ
  let H := WrappedChain.coordinates n R U
  have hf : ContDiff ℝ 3 f := flattenedResidual_contDiff n a β δ
  have hH : ContDiff ℝ 3 H := ZeroChainWrappedResidual.coordinates_contDiff n R U
  have hh := hb n a β δ ha hβ hδ (by linarith) (H u)
  refine ⟨hh.1.trans (mul_le_mul_of_nonneg_right hBC ha),?_,?_⟩
  · have hfn : ‖fderiv ℝ f (H u)‖ ≤ B*a/β := by
      have ht := hh.2 0
      change ‖iteratedFDeriv ℝ 1 f (H u)‖ ≤ B*a/(β*δ^0) at ht
      rw [pow_zero,mul_one,← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero] at ht
      exact ht
    have hHn : ‖fderiv ℝ H u‖ ≤ 1 := by
      have ht := ZeroChainWrappedResidual.coordinates_jet_le n R U u 1 (by norm_num)
      rw [← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero,
        ← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero,
        (RadialWrapper.compress_hasFDerivAt R u).fderiv] at ht
      exact ht.trans (RadialWrapper.compressDerivative_opNorm_le R hR u)
    rw [GradientJetBounds.gradient_norm_eq,
      ((hf.differentiable (by norm_num) (H u)).hasFDerivAt.comp u (hH.differentiable (by norm_num) u).hasFDerivAt).fderiv]
    calc
      _ ≤ ‖fderiv ℝ f (H u)‖*‖fderiv ℝ H u‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (B*a/β)*1 := mul_le_mul hfn hHn (norm_nonneg _) (by positivity)
      _ ≤ C*a/β := by
        simpa only [mul_one] using
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBC ha) hβ.le)
  · have ht := scaled_error n a β δ ha hβ hδ hδβ (H u)
    exact ht.trans (by
      apply div_le_div_of_nonneg_right _ hβ.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right heC ha) hδ.le)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Parameters
variable {n : ℕ} (P : Parameters (E := E) n)

def finalWidth : ℝ := width P.c P.β P.θ (levels P.θ)
def signalResolution : ℝ := P.finalWidth/8
def inactiveResidual (u : E) : ℝ :=
  flattenedResidual n P.amplitude P.β P.signalResolution (WrappedChain.coordinates n P.R P.U u)
def residualDifference (u : E) : ℝ := P.residual u-P.inactiveResidual u

omit [CompleteSpace E] in
theorem finalWidth_pos : 0 < P.finalWidth :=
  width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one _

omit [CompleteSpace E] in
theorem finalWidth_le : P.finalWidth ≤ P.c*P.β := by
  apply mul_le_of_le_one_right (mul_nonneg P.c_pos.le P.β_pos.le)
  exact Real.rpow_le_one_of_one_le_of_nonpos P.θ_ge_one (neg_nonpos.mpr (bExponent_nonneg _))

omit [CompleteSpace E] in
theorem finalWidth_scale : P.finalWidth ≤ Real.exp 2*P.β/P.θ := by
  have hβ := P.β_pos
  apply (final_width_bounds P.c P.β P.θ P.c_pos.le P.β_pos.le P.θ_ge_one).2.trans
  apply div_le_div_of_nonneg_right _ (by linarith [P.θ_ge_one])
  have hh := mul_le_mul_of_nonneg_left (show P.c ≤ 1 by linarith [P.c_small])
    (show 0 ≤ Real.exp 2*P.β by positivity)
  nlinarith only [hh]

omit [CompleteSpace E] in
theorem signalResolution_pos : 0 < P.signalResolution := div_pos P.finalWidth_pos (by norm_num)

omit [CompleteSpace E] in
theorem signalResolution_small : P.signalResolution ≤ P.β/16 := by
  have hβ := P.β_pos
  have hh := P.finalWidth_le
  have hc := mul_le_mul_of_nonneg_right P.c_small P.β_pos.le
  dsimp [signalResolution]
  linarith

omit [CompleteSpace E] in
theorem signalResolution_le_width : P.signalResolution ≤ P.finalWidth := by
  have hp := P.finalWidth_pos
  dsimp [signalResolution]
  linarith

theorem inactiveResidual_contDiff : ContDiff ℝ 3 P.inactiveResidual :=
  (flattenedResidual_contDiff n P.amplitude P.β P.signalResolution).comp
    (ZeroChainWrappedResidual.coordinates_contDiff n P.R P.U)

theorem residualDifference_contDiff : ContDiff ℝ 3 P.residualDifference :=
  P.residual_contDiff.sub P.inactiveResidual_contDiff

theorem residualDifference_gradient (u : E) : gradient P.residualDifference u =
    gradient P.residual u-gradient P.inactiveResidual u := by
  change gradient (fun v => P.residual v-P.inactiveResidual v) u = _
  rw [gradient,fderiv_sub (P.residual_contDiff.differentiable (by norm_num) u)
    (P.inactiveResidual_contDiff.differentiable (by norm_num) u),map_sub]
  rfl

end Parameters

/-- Uniform bounds for the actual carried residual, final flattening, and
their difference. The difference amplitude retains the final resolution. -/
theorem signal_residual_bounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n) (u : E),
        |P.residual u| ≤ C*P.L*P.β^2 ∧
        |P.inactiveResidual u| ≤ C*P.L*P.β^2 ∧
        |P.residualDifference u| ≤ C*P.L*P.β*P.signalResolution ∧
        ‖gradient P.residual u‖ ≤ C*P.L*P.β ∧
        ‖gradient P.inactiveResidual u‖ ≤ C*P.L*P.β ∧
        ‖gradient P.residualDifference u‖ ≤ C*P.L*P.β := by
  obtain ⟨A,hA,ha⟩ := ZeroChainWrappedResidual.residual_uniform_bounds
  obtain ⟨B,hB,hb⟩ := wrapped_flat_bounds
  let C := 2*(A+B)
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨C,by dsimp [C]; linarith,fun E _ _ _ n P u => ?_⟩
  have hL := P.L_pos
  have hβ := P.β_pos
  have hτ := P.signalResolution_pos
  have hη := P.η_nonneg
  have hr := ha E n P.amplitude P.β P.R P.amplitude_nonneg hβ P.β_le_R P.U u
  have hf := hb E n P.amplitude P.β P.signalResolution P.R P.amplitude_nonneg hβ hτ
    P.signalResolution_small (P.β_pos.trans_le P.β_le_R) P.U u
  have hamp : P.amplitude ≤ P.L*P.β^2 := by
    have hh := mul_le_mul_of_nonneg_right P.η_le_one (show 0 ≤ P.L*P.β^2 by positivity)
    dsimp [Parameters.amplitude]
    nlinarith only [hh]
  have hga : ‖gradient P.residual u‖ ≤ A*P.L*P.β := by
    have hh := hr.2 0
    change ‖iteratedFDeriv ℝ 1 P.residual u‖ ≤ A*P.amplitude/P.β^1 at hh
    rw [pow_one,← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero,
      ← GradientJetBounds.gradient_norm_eq] at hh
    apply hh.trans
    apply (div_le_iff₀ hβ).mpr
    have hm := mul_le_mul_of_nonneg_left hamp (show 0 ≤ A by linarith)
    nlinarith only [hm]
  have hgb : ‖gradient P.inactiveResidual u‖ ≤ B*P.L*P.β := by
    apply hf.2.1.trans
    apply (div_le_iff₀ hβ).mpr
    have hm := mul_le_mul_of_nonneg_left hamp (show 0 ≤ B by linarith)
    nlinarith only [hm]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · apply hr.1.trans
    calc
      A*P.amplitude ≤ A*(P.L*P.β^2) := mul_le_mul_of_nonneg_left hamp (by linarith)
      _ ≤ C*P.L*P.β^2 := by nlinarith [mul_le_mul_of_nonneg_right hAC (show 0 ≤ P.L*P.β^2 by positivity)]
  · apply hf.1.trans
    calc
      B*P.amplitude ≤ B*(P.L*P.β^2) := mul_le_mul_of_nonneg_left hamp (by linarith)
      _ ≤ C*P.L*P.β^2 := by nlinarith [mul_le_mul_of_nonneg_right hBC (show 0 ≤ P.L*P.β^2 by positivity)]
  · apply hf.2.2.trans
    apply (div_le_iff₀ hβ).mpr
    have hm := mul_le_mul_of_nonneg_left hamp (show 0 ≤ B*P.signalResolution by positivity)
    have hc := mul_le_mul_of_nonneg_right hBC (show 0 ≤ P.L*P.β^2*P.signalResolution by positivity)
    nlinarith only [hm,hc]
  · exact hga.trans (by nlinarith [mul_le_mul_of_nonneg_right hAC (show 0 ≤ P.L*P.β by positivity)])
  · exact hgb.trans (by nlinarith [mul_le_mul_of_nonneg_right hBC (show 0 ≤ P.L*P.β by positivity)])
  · rw [P.residualDifference_gradient]
    apply (norm_sub_le _ _).trans
    have hh := add_le_add hga hgb
    dsimp [C]
    nlinarith [mul_nonneg (show 0 ≤ A+B by linarith) (show 0 ≤ P.L*P.β by positivity)]

end Bilevel.MultiscaleMean
