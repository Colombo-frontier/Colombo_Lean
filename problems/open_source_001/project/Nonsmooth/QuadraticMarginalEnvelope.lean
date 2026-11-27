import Nonsmooth.StrongPotentialVariance

open MeasureTheory Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E]

theorem quadratic_slice_exponential_integrable (V : E → ℝ → ℝ)
    (hV : ∀ t, Continuous (V t)) {a B : ℝ} (ha : 0 < a)
    (hl : ∀ t x, a * (‖t‖ ^ 2 + x ^ 2) - B ≤ V t x) (t : E) :
    Integrable (fun x => Real.exp (-V t x)) := by
  apply ((integrable_exp_neg_mul_sq ha).const_mul (Real.exp (B - a * ‖t‖ ^ 2))).mono'
    (Real.continuous_exp.comp (hV t).neg).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖Real.exp (-V t x)‖ ≤ Real.exp (B - a * ‖t‖ ^ 2) * Real.exp (-a * x ^ 2)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hl t x]

/-- Integrating one coordinate preserves two-sided quadratic potential bounds.
Both comparison constants are actual finite positive Gaussian integrals. -/
theorem quadratic_marginal_potential_bounds (V : E → ℝ → ℝ)
    (hV : ∀ t, Continuous (V t)) {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hl : ∀ t x, a * (‖t‖ ^ 2 + x ^ 2) - B ≤ V t x)
    (hu : ∀ t x, V t x ≤ B * (1 + ‖t‖ ^ 2 + x ^ 2)) (t : E) :
    a * ‖t‖ ^ 2 - B - Real.log (∫ x : ℝ, Real.exp (-a * x ^ 2)) ≤
      -Real.log (∫ x : ℝ, Real.exp (-V t x)) ∧
    -Real.log (∫ x : ℝ, Real.exp (-V t x)) ≤
      B * (1 + ‖t‖ ^ 2) - Real.log (∫ x : ℝ, Real.exp (-B * x ^ 2)) := by
  have hi := quadratic_slice_exponential_integrable V hV ha hl t
  have hia := integrable_exp_neg_mul_sq ha
  have hiB := integrable_exp_neg_mul_sq hB
  have hza := integral_exp_pos hia
  have hzB := integral_exp_pos hiB
  have hz := integral_exp_pos hi
  have hupper : (∫ x : ℝ, Real.exp (-V t x)) ≤
      Real.exp (B - a * ‖t‖ ^ 2) * ∫ x : ℝ, Real.exp (-a * x ^ 2) := by
    rw [← integral_const_mul]
    apply integral_mono hi (hia.const_mul _)
    intro x
    dsimp only
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hl t x]
  have hlower : Real.exp (-B * (1 + ‖t‖ ^ 2)) * (∫ x : ℝ, Real.exp (-B * x ^ 2)) ≤
      ∫ x : ℝ, Real.exp (-V t x) := by
    rw [← integral_const_mul]
    apply integral_mono (hiB.const_mul _) hi
    intro x
    dsimp only
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hu t x]
  have hlu := Real.log_le_log hz hupper
  have hll := Real.log_le_log (mul_pos (Real.exp_pos _) hzB) hlower
  rw [Real.log_mul (Real.exp_ne_zero _) hza.ne', Real.log_exp] at hlu
  rw [Real.log_mul (Real.exp_ne_zero _) hzB.ne', Real.log_exp] at hll
  constructor <;> linarith

theorem quadratic_marginal_potential_abs_bound (V : E → ℝ → ℝ)
    (hV : ∀ t, Continuous (V t)) {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hl : ∀ t x, a * (‖t‖ ^ 2 + x ^ 2) - B ≤ V t x)
    (hu : ∀ t x, V t x ≤ B * (1 + ‖t‖ ^ 2 + x ^ 2)) (t : E) :
    |-Real.log (∫ x : ℝ, Real.exp (-V t x))| ≤
      (B + |Real.log (∫ x : ℝ, Real.exp (-a * x ^ 2))| +
        |Real.log (∫ x : ℝ, Real.exp (-B * x ^ 2))|) * (1 + ‖t‖ ^ 2) := by
  have h := quadratic_marginal_potential_bounds V hV ha hB hl hu t
  apply abs_le.mpr
  have hs := sq_nonneg ‖t‖
  have ha0 := mul_nonneg ha.le hs
  have hB0 := mul_nonneg hB.le hs
  have hla := abs_nonneg (Real.log (∫ x : ℝ, Real.exp (-a * x ^ 2)))
  have hlB := abs_nonneg (Real.log (∫ x : ℝ, Real.exp (-B * x ^ 2)))
  constructor
  · nlinarith [le_abs_self (Real.log (∫ x : ℝ, Real.exp (-a * x ^ 2))),
      mul_nonneg hla hs, mul_nonneg hlB hs]
  · nlinarith [neg_abs_le (Real.log (∫ x : ℝ, Real.exp (-B * x ^ 2))),
      mul_nonneg hla hs, mul_nonneg hlB hs]

end
end Nonsmooth
