import Nonsmooth.ConditionalMean
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Cauchy--Schwarz for the first two moments, proved by integrating a square. -/
theorem integral_square_mean_le {r : Ω → ℝ} (hi : Integrable r P)
    (hi2 : Integrable (fun ω => r ω ^ 2) P) :
    (∫ ω, r ω ∂P) ^ 2 ≤ ∫ ω, r ω ^ 2 ∂P := by
  let a := ∫ ω, r ω ∂P
  have hnon : 0 ≤ ∫ ω, r ω ^ 2 - 2 * a * r ω + a ^ 2 ∂P := by
    apply integral_nonneg
    intro ω
    change 0 ≤ r ω ^ 2 - 2 * a * r ω + a ^ 2
    nlinarith [sq_nonneg (r ω - a)]
  have hisub : Integrable (fun ω => r ω ^ 2 - 2 * a * r ω) P :=
    hi2.sub (hi.const_mul (2 * a))
  rw [integral_add hisub (integrable_const _),
    integral_sub hi2 (hi.const_mul (2 * a)), integral_const_mul,
    integral_const, measureReal_univ_eq_one, one_smul] at hnon
  change a ^ 2 ≤ _
  change 0 ≤ (∫ ω, r ω ^ 2 ∂P) - 2 * a * a + a ^ 2 at hnon
  nlinarith

theorem integral_le_sqrt_second_moment {r : Ω → ℝ} (hi : Integrable r P)
    (hi2 : Integrable (fun ω => r ω ^ 2) P) {q : ℝ}
    (hq : (∫ ω, r ω ^ 2 ∂P) ≤ q) : (∫ ω, r ω ∂P) ≤ Real.sqrt q := by
  have hs := integral_square_mean_le hi hi2
  have hq0 : 0 ≤ q := le_trans (integral_nonneg (fun ω => sq_nonneg (r ω))) hq
  have hroot := Real.sq_sqrt hq0
  have hp := Real.sqrt_nonneg q
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem posterior_norm_integrable {m : Ω → E} (hm : AEStronglyMeasurable m P)
    (hbound : ∀ᵐ ω ∂P, ‖m ω‖ ≤ 1) :
    Integrable (fun ω => ‖m ω‖) P ∧ Integrable (fun ω => ‖m ω‖ ^ 2) P := by
  constructor
  · apply (integrable_const (1 : ℝ)).mono' hm.norm
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hω
  · apply (integrable_const (1 : ℝ)).mono' (hm.norm.pow 2)
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖m ω‖ ^ 2 ≤ 1
    nlinarith [norm_nonneg (m ω)]

end
end Nonsmooth
