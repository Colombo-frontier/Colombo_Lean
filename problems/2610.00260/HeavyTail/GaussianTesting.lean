import HeavyTail.GaussianLowerMoments
import Mathlib.MeasureTheory.Measure.Real

/-! Testing inequalities derived from an actual likelihood density and its
second moment. No testing conclusion or total-variation premise is assumed. -/

open MeasureTheory
open scoped ENNReal
namespace HeavyTail.GaussianLower
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

omit [IsProbabilityMeasure Q] in
theorem likelihood_centered_second {L : Ω → ℝ}
    (hL2 : Integrable (fun ω ↦ L ω ^ 2) P) (hmean : (∫ ω, L ω ∂P) = 1) :
    (∫ ω, (L ω - 1) ^ 2 ∂P) = (∫ ω, L ω ^ 2 ∂P) - 1 := by
  have hi := integrable_of_integral_eq_one hmean
  have htwo : Integrable (fun ω ↦ 2 * L ω) P := hi.const_mul 2
  have hsub : Integrable (fun ω ↦ L ω ^ 2 - 2 * L ω) P := hL2.sub htwo
  have he (ω : Ω) : (L ω - 1) ^ 2 = (L ω ^ 2 - 2 * L ω) + 1 := by ring
  simp_rw [he]
  rw [integral_add hsub (integrable_const _), integral_sub hL2 htwo,
    integral_const_mul, hmean, integral_const]
  simp
  ring

omit [IsProbabilityMeasure Q] in
theorem likelihood_centered_square_integrable {L : Ω → ℝ}
    (hL2 : Integrable (fun ω ↦ L ω ^ 2) P) (hmean : (∫ ω, L ω ∂P) = 1) :
    Integrable (fun ω ↦ (L ω - 1) ^ 2) P := by
  have hi := integrable_of_integral_eq_one hmean
  have h : Integrable (fun ω ↦ L ω ^ 2 - 2 * L ω + 1) P :=
    (hL2.sub (hi.const_mul 2)).add (integrable_const 1)
  convert h using 1
  funext ω
  ring

omit [IsProbabilityMeasure Q] in
theorem likelihood_L1_le_eighth {L : Ω → ℝ} (hL : Measurable L)
    (hL2 : Integrable (fun ω ↦ L ω ^ 2) P) (hmean : (∫ ω, L ω ∂P) = 1)
    (hsecond : (∫ ω, L ω ^ 2 ∂P) ≤ (65 / 64 : ℝ)) :
    (∫ ω, |L ω - 1| ∂P) ≤ (1 / 8 : ℝ) := by
  have h := probability_moment_le_of_second_bound (hL.sub measurable_const)
    (likelihood_centered_square_integrable hL2 hmean)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (show (∫ ω, (L ω - 1) ^ 2 ∂P) ≤ (1 / 8 : ℝ) ^ 2 by
      rw [likelihood_centered_second hL2 hmean]
      linarith)
  simpa only [Real.rpow_one] using h

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
theorem density_real_event {L : Ω → ℝ} (hL0 : ∀ ω, 0 ≤ L ω)
    (hLi : Integrable L P) {S : Set Ω} (hS : MeasurableSet S) :
    (P.withDensity (fun ω ↦ ENNReal.ofReal (L ω))).real S = ∫ ω in S, L ω ∂P := by
  rw [measureReal_def, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal hLi.restrict (Filter.Eventually.of_forall hL0),
    ENNReal.toReal_ofReal (integral_nonneg hL0)]

omit [IsProbabilityMeasure Q] in
theorem likelihood_event_difference_le_eighth {L : Ω → ℝ}
    (hL : Measurable L) (hL0 : ∀ ω, 0 ≤ L ω)
    (hL2 : Integrable (fun ω ↦ L ω ^ 2) P) (hmean : (∫ ω, L ω ∂P) = 1)
    (hsecond : (∫ ω, L ω ^ 2 ∂P) ≤ (65 / 64 : ℝ))
    (hQP : Q = P.withDensity (fun ω ↦ ENNReal.ofReal (L ω)))
    {S : Set Ω} (hS : MeasurableSet S) : Q.real S - P.real S ≤ (1 / 8 : ℝ) := by
  have hi := integrable_of_integral_eq_one hmean
  have hci : Integrable (fun ω ↦ L ω - 1) P := hi.sub (integrable_const 1)
  have he : Q.real S - P.real S = ∫ ω in S, L ω - 1 ∂P := by
    rw [hQP, density_real_event hL0 hi hS, integral_sub hi.restrict (integrable_const _),
      integral_const]
    simp
  rw [he]
  calc
    _ ≤ |∫ ω in S, L ω - 1 ∂P| := le_abs_self _
    _ ≤ ∫ ω in S, |L ω - 1| ∂P := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := P.restrict S) (fun ω ↦ L ω - 1))
    _ ≤ ∫ ω, |L ω - 1| ∂P := integral_mono_measure P.restrict_le_self
      (Filter.Eventually.of_forall fun ω ↦ abs_nonneg _) hci.abs
    _ ≤ 1 / 8 := likelihood_L1_le_eighth hL hL2 hmean hsecond

/-- Every measurable test has the stated sum of errors under the two actual laws. -/
theorem likelihood_binary_testing_lower {L : Ω → ℝ}
    (hL : Measurable L) (hL0 : ∀ ω, 0 ≤ L ω)
    (hL2 : Integrable (fun ω ↦ L ω ^ 2) P) (hmean : (∫ ω, L ω ∂P) = 1)
    (hsecond : (∫ ω, L ω ^ 2 ∂P) ≤ (65 / 64 : ℝ))
    (hQP : Q = P.withDensity (fun ω ↦ ENNReal.ofReal (L ω)))
    {S : Set Ω} (hS : MeasurableSet S) : (7 / 8 : ℝ) ≤ P.real S + Q.real Sᶜ := by
  have h := likelihood_event_difference_le_eighth hL hL0 hL2 hmean hsecond hQP hS
  rw [measureReal_compl hS, measureReal_univ_eq_one]
  linarith

end
end HeavyTail.GaussianLower
