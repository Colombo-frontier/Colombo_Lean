import SampleReuse.CurvatureCalibration
import SampleReuse.CurvatureRadialExclusion

open SecondOrder MeasureTheory

namespace SampleReuse
noncomputable section

def calibratedCurvatureLoss {d T : ℕ}
    (P : Parameters) (γ : ℝ) (U : Point (T+1) →ₗᵢ[ℝ] Point d) : Point d → ℝ :=
  radialGlobalization
    (curvatureFrameCore U (curvatureAmplitude (curvatureScaleK P) γ)
      (curvatureInputDilation (curvatureScaleK P) γ))
    (curvatureWallSlope P) (curvatureRadius P γ)

theorem curvatureJetBudget_nonneg (P : Parameters) {γ : ℝ} (hγ : 0 < γ)
    (j : ℕ) (hj : j ≤ 3) : 0 ≤ curvatureJetBudget P γ j := by
  interval_cases j
  · exact div_nonneg P.gap_pos.le (by norm_num)
  · exact mul_nonneg (curvatureGradientConstant_nonneg P) (Real.sqrt_nonneg _)
  · exact mul_nonneg curvatureHessianConstant_pos.le hγ.le
  · exact (curvatureThirdConstant_pos P).le

theorem calibratedCurvatureCore_jet {d T : ℕ}
    (P : Parameters) (U : Point (T+1) →ₗᵢ[ℝ] Point d)
    {γ : ℝ} (hγ : 0 < γ)
    (hn : curvatureAmplitude (curvatureScaleK P) γ*(T+1:ℕ) ≤ P.gap/8)
    (x : Point d) (j : ℕ) (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (curvatureFrameCore U (curvatureAmplitude (curvatureScaleK P) γ)
      (curvatureInputDilation (curvatureScaleK P) γ)) x‖ ≤ curvatureJetBudget P γ j := by
  have hK := curvatureScaleK_pos P
  have hh := scaled_frame_core_derivative_rates U hK hγ P.gap_pos.le hn x
  interval_cases j
  · rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    have hr := curvatureFrameCore_range U (curvatureAmplitude_pos hK hγ).le
      (curvatureInputDilation (curvatureScaleK P) γ) x
    change |curvatureFrameCore U (curvatureAmplitude (curvatureScaleK P) γ)
      (curvatureInputDilation (curvatureScaleK P) γ) x| ≤ P.gap/2
    exact abs_le.mpr ⟨by nlinarith only [hr.1,hn],hr.2.trans (by linarith [P.gap_pos])⟩
  · rw [norm_first_iteratedFDeriv,← norm_gradient_eq_fderiv]
    exact hh.1
  · rw [← norm_fderiv_gradient]
    exact hh.2.1
  · exact hh.2.2

theorem calibrated_curvature_scalar_budgets (P : Parameters) {γ ε : ℝ}
    (hγ : 0 < γ) (hε : ε < P.gradientBound/8)
    (hB : curvatureGradientConstant P*Real.sqrt γ < P.gradientBound/8)
    (hX : curvatureTransverseRatio P γ < 1)
    {T : ℕ} (hn : curvatureAmplitude (curvatureScaleK P) γ*(T+1:ℕ) ≤ P.gap/8) :
    8*γ ≤ curvatureAmplitude (curvatureScaleK P) γ*
      (curvatureInputDilation (curvatureScaleK P) γ)^2*Real.exp (-(9:ℝ)/4) ∧
    2*curvatureWallSlope P/curvatureRadius P γ ≤ γ ∧
    4*(curvatureAmplitude (curvatureScaleK P) γ*
      (curvatureInputDilation (curvatureScaleK P) γ)^2*curvatureCoreConstant)/
      (curvatureInputDilation (curvatureScaleK P) γ*curvatureRadius P γ) ≤ γ ∧
    ε < curvatureWallSlope P-curvatureAmplitude (curvatureScaleK P) γ*
      curvatureInputDilation (curvatureScaleK P) γ*
        (curvatureCoreConstant*Real.sqrt (T+1:ℕ)) := by
  have hK := curvatureScaleK_pos P
  have hR := curvatureRadiusScale_pos P
  refine ⟨(curvature_scale_negative hK hγ).ge,?_,?_,?_⟩
  · unfold curvatureRadius
    rw [div_div_eq_mul_div]
    apply (div_le_iff₀ hR).mpr
    unfold curvatureRadiusScale
    nlinarith
  · rw [curvature_scale_two hK hγ]
    have he : 4*(curvatureKappa*γ*curvatureCoreConstant)/
        (curvatureInputDilation (curvatureScaleK P) γ*curvatureRadius P γ) =
        curvatureTransverseRatio P γ*γ := by
      unfold curvatureInputDilation curvatureRadius curvatureTransverseRatio curvatureHessianConstant
      field_simp
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_right hX.le hγ.le).trans_eq (one_mul γ)
  · have hh := mul_le_mul_of_nonneg_left
      (curvature_scale_gradient hK hγ P.gap_pos.le (T+1) hn) curvatureCoreConstant_pos.le
    change curvatureGradientConstant P*Real.sqrt γ < P.gradientBound/8 at hB
    unfold curvatureGradientConstant at hB
    unfold curvatureWallSlope
    nlinarith only [hh,hB,hε]

/-- Full `lem:global`: actual common deterministic loss, all model fields, and
stationary-output completion, with a single threshold uniform in frame/dimension. -/
theorem calibrated_curvature_globalization (P : Parameters) :
    ∃ η : ℝ, 0 < η ∧ ∀ γ : ℝ, 0 < γ → γ < η → ∀ ε : ℝ, ε < P.gradientBound/8 →
      ∀ (d T : ℕ) (U : Point (T+1) →ₗᵢ[ℝ] Point d),
      curvatureAmplitude (curvatureScaleK P) γ*(T+1:ℕ) ≤ P.gap/8 →
      Admissible (PMF.pure ()).toMeasure P (calibratedCurvatureLoss P γ U)
        (fun _ : Unit => calibratedCurvatureLoss P γ U) 0 ∧
      (∀ x, IsSOSP (calibratedCurvatureLoss P γ U) ε γ x →
        ‖x‖ < curvatureRadius P γ ∧ ∀ j : Fin (T+1),
          1 < |curvatureFrameMap U (curvatureInputDilation (curvatureScaleK P) γ) x j|) := by
  obtain ⟨η,hη,hbud⟩ := curvature_small_tolerance_budgets P
  refine ⟨η,hη,fun γ hγ hγη ε hε d T U hn => ?_⟩
  have hh := hbud γ hγ hγη
  have hK := curvatureScaleK_pos P
  have hA := (curvatureAmplitude_pos hK hγ).le
  have hβ := curvatureInputDilation_pos hK hγ
  have hb := (curvatureWallSlope_pos P).le
  have hR : 0 < curvatureRadius P γ := div_pos (curvatureRadiusScale_pos P) hγ
  have hj := curvature_budget_identities P hγ
  constructor
  · apply radial_deterministic_admissible P (curvatureFrameCore_contDiff U _ _ 3)
      (curvatureFrameCore_zero U _ _) hb hR (D := P.gap/2)
      (by linarith [P.gap_pos]) (B := curvatureJetBudget P γ)
    · intro x
      have hr := (curvatureFrameCore_range U hA (curvatureInputDilation (curvatureScaleK P) γ) x).1
      nlinarith only [hr,hn]
    · linarith [P.gap_pos]
    · exact curvatureJetBudget_nonneg P hγ
    · exact calibratedCurvatureCore_jet P U hγ hn
    · exact hj.1.le.trans hh.1.le
    · exact hj.2.1.le.trans hh.2.1.le
    · exact hj.2.2.le.trans hh.2.2.1.le
  · intro x hs
    have hscl := calibrated_curvature_scalar_budgets P hγ hε hh.2.2.2.1 hh.2.2.2.2 hn
    exact curvature_radial_sosp_completed U hA hβ hb hR hγ
      hscl.1 hscl.2.1 hscl.2.2.1 hscl.2.2.2 hs

end
end SampleReuse
