import Bilevel.PolishedLiteralFlatEnvelope

/-! Global envelopes for the actual informative residual difference. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain
namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

theorem residualDifference_gradient (δ : ℝ) (z : Joint X U) :
    gradient (P.residualDifference δ) z=gradient P.selectedResidual z-gradient (P.selectedFlatResidual δ) z := by
  change gradient (fun y => P.selectedResidual y-P.selectedFlatResidual δ y) z=_
  simp only [gradient]
  rw [fderiv_sub (P.selectedResidual_contDiff.differentiable (by norm_num) z)
    ((P.selectedFlatResidual_contDiff δ).differentiable (by norm_num) z),map_sub]

end Parameters

theorem signal_residual_c1_bounds : ∃ B : ℝ,1≤B ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (δ : ℝ),
      0≤P.L → 0<P.β → 0<δ → δ≤P.β/16 → P.β≤P.radius →
      P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      ∀ z : Joint X U,
        |P.residualDifference δ z|≤B*P.L*P.β*δ ∧
        |P.selectedFlatResidual δ z|≤B*P.L*P.β^2 ∧
        ‖gradient P.selectedResidual z‖≤B*P.L*P.β ∧
        ‖gradient (P.residualDifference δ) z‖≤B*P.L*P.β := by
  obtain ⟨Cr,hCr,hr⟩ := selected_residual_joint_jet_bounds
  obtain ⟨Cf,hCf,hf⟩ := selected_flat_joint_c1_bounds
  obtain ⟨Ce,hCe,he⟩ := selected_flat_error_bound
  let B := 1+Cr+Cf+Ce
  have hB : 1≤B := by dsimp [B];linarith
  have hCrB : Cr≤B := by dsimp [B];linarith
  have hCfB : Cf≤B := by dsimp [B];linarith
  have hCeB : Ce≤B := by dsimp [B];linarith
  have hSumB : Cr+Cf≤B := by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro X U _ _ _ _ _ _ P δ hL hβ hδ hδs hR hβb hbR z
  have hr1 := hr X U P hL hβ hR hβb hbR z 1 (by norm_num)
  have hf0 := hf X U P δ hL hβ hδ hδs hR hβb hbR z 0 (by norm_num)
  have hf1 := hf X U P δ hL hβ hδ hδs hR hβb hbR z 1 (by norm_num)
  have hsr (C : ℝ) : C*P.L*P.β^2/P.β=C*P.L*P.β := by field_simp;ring
  simp only [pow_one,← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero,
    ← GradientJetBounds.gradient_norm_eq,hsr] at hr1 hf1
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one] at hf0
  have hd := he X U P δ hL hβ hδ hδs z
  have hsum := (norm_sub_le (gradient P.selectedResidual z) (gradient (P.selectedFlatResidual δ) z)).trans
    (add_le_add hr1 hf1)
  rw [← P.residualDifference_gradient] at hsum
  refine ⟨hd.trans ?_,hf0.trans ?_,hr1.trans ?_,hsum.trans ?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_right hCeB (show 0≤P.L*P.β*δ by positivity)]
  · nlinarith only [mul_le_mul_of_nonneg_right hCfB (show 0≤P.L*P.β^2 by positivity)]
  · nlinarith only [mul_le_mul_of_nonneg_right hCrB (show 0≤P.L*P.β by positivity)]
  · nlinarith only [mul_le_mul_of_nonneg_right hSumB (show 0≤P.L*P.β by positivity)]

end Bilevel.PolishedLiteral
