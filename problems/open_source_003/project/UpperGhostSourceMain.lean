import UpperGhostModelRisk

/-! The original ghost proof route with the exact source U2 and 17 eps / 48
ghost error allowance, for the same original public algorithm and reply ledger. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open Task006.UpperPublicParameters
namespace Task006.Full

theorem tunedUpper_ghost_tail_lt_one {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    (d : ℝ) * Real.exp (-tunedUpperScale d L R eps) < 1 := by
  let A := upperAspect L R eps
  let T := tunedUpperRounds d L R eps
  let q := (d : ℝ) * Real.exp (-tunedUpperScale d L R eps)
  have hA : 4 ≤ A := (regime_aspect h).1
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast tunedUpperRounds_pos h
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hb := (public_log_budget h.1 (by linarith : 2 ≤ A) (regime_aspect h).2).2.2
  have hTq : (T : ℝ) * q ≤ (A⁻¹)^2 := by
    convert hb using 1 <;> dsimp only [T, q, A, tunedUpperRounds, tunedUpperScale] <;> ring
  have hi : (A⁻¹)^2 ≤ (1/16:ℝ) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<16) (show 16 ≤ A^2 by nlinarith)
    simpa only [one_div, inv_pow] using hh
  change q < 1
  nlinarith

namespace SampleInstance
variable {d : ℕ} {L R eps : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (h : Regime d L R eps) (I : SampleInstance d L R Ω μ)

noncomputable def tunedGhostLaw : Measure (GhostState (UpperGhostState d)) :=
  I.upperGhostLaw (tunedUpperParameters d L R eps h) h.2.2.1.le h.2.1
    (by have hd := h.1; omega) (tunedUpperScale d L R eps) (tunedUpperScale_ge_one h)
    (tunedUpper_ghost_tail_lt_one h) (tunedUpperRounds d L R eps)

theorem source_upper_ghost_error :
    Integrable (I.upperGhostGap (tunedUpperParameters d L R eps h) (tunedUpperRounds d L R eps)) (I.tunedGhostLaw h) ∧
      (∫ j, I.upperGhostGap (tunedUpperParameters d L R eps h) (tunedUpperRounds d L R eps) j ∂I.tunedGhostLaw h) ≤ 17 * eps / 48 := by
  have he := I.upperGhost_expected_risk_le (tunedUpperParameters d L R eps h)
    (by have hd := h.1; omega) (tunedUpperRounds_pos h) h.2.2.1 h.2.1
    (tunedUpperParameters_rho_pos h) (tunedUpperParameters_clip_pos h)
    (tunedUpperScale d L R eps) (tunedUpperScale_ge_one h) (tunedUpper_ghost_tail_lt_one h)
  exact ⟨he.1, he.2.trans (tunedUpper_ghost_accuracy h)⟩

theorem source_upper_ghost_failure :
    (I.tunedGhostLaw h).real ghostFailed ≤ ((upperAspect L R eps)⁻¹)^2 := by
  have he := I.upperGhostLaw_failure (tunedUpperParameters d L R eps h) h.2.2.1.le h.2.1
    (by have hd := h.1; omega) (tunedUpperScale d L R eps) (tunedUpperScale_ge_one h)
    (tunedUpper_ghost_tail_lt_one h) (tunedUpperRounds d L R eps)
  have hb := (public_log_budget h.1 (by linarith [(regime_aspect h).1] : 2 ≤ upperAspect L R eps)
    (regime_aspect h).2).2.2
  have hb' : (tunedUpperRounds d L R eps:ℝ) * ((d:ℝ)*Real.exp (-tunedUpperScale d L R eps)) ≤
      ((upperAspect L R eps)⁻¹)^2 := by
    convert hb using 1 <;> dsimp only [tunedUpperRounds, tunedUpperScale] <;> ring
  exact he.trans hb'

theorem source_upper_actual_error :
    (∫ w, (tunedUpperAlgorithm d L R eps h).realizedGap I w
      ∂(upperSeedLaw d (tunedUpperRounds d L R eps)).prod (iidHandleLaw μ)) ≤
        17 * eps / 48 + 2 * eps / (L * R / eps) := by
  have ht := I.upperGhost_actual_risk_transfer (tunedUpperParameters d L R eps h)
    (by have hd := h.1; omega) (tunedUpperRounds_pos h) h.2.2.1.le h.2.1
    (tunedUpperScale d L R eps) (tunedUpperScale_ge_one h) (tunedUpper_ghost_tail_lt_one h)
  have hg := (I.source_upper_ghost_error h).2
  have hc := tunedUpper_ghost_tail_correction h
  have hc' : 2*L*R*((tunedUpperRounds d L R eps:ℝ)*((d:ℝ)*Real.exp (-tunedUpperScale d L R eps))) ≤
      2*eps/(L*R/eps) := by
    convert hc using 1 <;> ring
  change (∫ w, (tunedUpperAlgorithm d L R eps h).realizedGap I w
      ∂(upperSeedLaw d (tunedUpperRounds d L R eps)).prod (iidHandleLaw μ)) ≤
    (∫ j, I.upperGhostGap (tunedUpperParameters d L R eps h) (tunedUpperRounds d L R eps) j ∂I.tunedGhostLaw h) +
      2*L*R*((tunedUpperRounds d L R eps:ℝ)*((d:ℝ)*Real.exp (-tunedUpperScale d L R eps))) at ht
  linarith

theorem source_upper_actual_error_lt :
    (∫ w, (tunedUpperAlgorithm d L R eps h).realizedGap I w
      ∂(upperSeedLaw d (tunedUpperRounds d L R eps)).prod (iidHandleLaw μ)) < eps := by
  have hb := I.source_upper_actual_error h
  have ha := (regime_aspect h).1
  have heps := h.2.2.2.1
  have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*eps) (by norm_num : (0:ℝ)<4) ha
  change 2*eps/(L*R/eps) ≤ 2*eps/4 at hh
  linarith

end SampleInstance
#print axioms SampleInstance.source_upper_ghost_error
#print axioms SampleInstance.source_upper_actual_error_lt
end Task006.Full
