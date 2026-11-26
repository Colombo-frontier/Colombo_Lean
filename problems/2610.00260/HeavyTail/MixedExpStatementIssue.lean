import HeavyTail.GaussianEstimates
import HeavyTail.ScalarClipping

/-! The standalone statement of manuscript `lem:mixed-exp` omits η ≥ 0.
Its proof and the algorithm's parameter tuning use positive η. This file
certifies the obstruction to allowing negative η, without changing the source.
Take p=2, b=M=1, R=2, c=0, x=-1, Z=1, η=-1, ξ=0, V=0, s₀=a/2.
Both x and Z are strictly inside the radius-2 ball; s₀R=a.
Then U=1+aN and the plus-error exponential is the integrand below. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace HeavyTail

def negativeEtaIntegrand (a z : ℝ) : ℝ :=
  Real.exp (clip (-2 - a * z) + 2 + a * z)

theorem negativeEtaIntegrand_integrable (a : ℝ) :
    Integrable (negativeEtaIntegrand a) (gaussianReal 0 1) := by
  apply ((GaussianEstimates.standard_exp_integrable a).const_mul (Real.exp 3)).mono'
  · apply Continuous.aestronglyMeasurable
    unfold negativeEtaIntegrand clip
    fun_prop
  · apply Filter.Eventually.of_forall
    intro z
    unfold negativeEtaIntegrand
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := (clip_mem (-2 - a * z)).2
    linarith

theorem negative_eta_gaussian_lower (a : ℝ) :
    Real.exp (1 + a ^ 2 / 2) ≤ ∫ z, negativeEtaIntegrand a z ∂gaussianReal 0 1 := by
  have hpoint (z : ℝ) : Real.exp 1 * Real.exp (a * z) ≤ negativeEtaIntegrand a z := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := (clip_mem (-2 - a * z)).1
    linarith
  have hi := integral_mono
    ((GaussianEstimates.standard_exp_integrable a).const_mul (Real.exp 1))
    (negativeEtaIntegrand_integrable a) hpoint
  rw [integral_const_mul] at hi
  change Real.exp 1 * mgf id (gaussianReal 0 1) a ≤ _ at hi
  rw [GaussianEstimates.standard_mgf, ← Real.exp_add] at hi
  exact hi

/-- No positive constant repairs the written estimate for all negative η. -/
theorem mixed_exp_requires_nonnegative_eta (C : ℝ) (hC : 0 < C) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      Real.exp (C * ((-1 : ℝ) ^ 2 * a ^ 2 + (-1 : ℝ) ^ 2 * a ^ 2 * (0 + 1 ^ 2))) <
        ∫ z, negativeEtaIntegrand a z ∂gaussianReal 0 1 := by
  let a := 1 / (4 * (C + 1))
  have hd : 0 < 4 * (C + 1) := by positivity
  have ha : 0 < a := one_div_pos.mpr hd
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ hd).mpr
    linarith
  have hc : 2 * C * a ^ 2 < 1 := by
    dsimp [a]
    rw [div_pow, one_pow, ← mul_div_assoc, mul_one]
    apply (div_lt_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith only [sq_nonneg C, hC]
  refine ⟨a, ha, ha1, ?_⟩
  have hexp : Real.exp (2 * C * a ^ 2) < Real.exp (1 + a ^ 2 / 2) := by
    apply Real.exp_lt_exp.mpr
    nlinarith only [hc, sq_nonneg a]
  have h := hexp.trans_le (negative_eta_gaussian_lower a)
  convert h using 1 <;> congr 1 <;> ring

theorem no_uniform_negative_eta_constant :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
      (∫ z, negativeEtaIntegrand a z ∂gaussianReal 0 1) ≤ Real.exp (2 * C * a ^ 2) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨a, ha, ha1, hbad⟩ := mixed_exp_requires_nonnegative_eta C hC
  have heq : C * ((-1 : ℝ) ^ 2 * a ^ 2 + (-1 : ℝ) ^ 2 * a ^ 2 * (0 + 1 ^ 2)) =
      2 * C * a ^ 2 := by ring
  rw [heq] at hbad
  exact (not_lt_of_ge (hbound a ha ha1)) hbad

end HeavyTail
