import Nonsmooth.KernelExponentialJensen
import Nonsmooth.GaussianExponential

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem scalar_unit_mgf_upper_tail {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ)
    (hi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * f x)) μ)
    (hb : ∀ r : ℝ, (∫ x, Real.exp (r * f x) ∂μ) ≤ Real.exp (r ^ 2 / 2))
    (t : ℝ) (ht : 0 ≤ t) : μ.real {x | t ≤ f x} ≤ Real.exp (-t ^ 2 / 2) := by
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    simpa only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero] using
      (measureReal_le_one (μ := μ) (s := {x | 0 ≤ f x}))
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Eventually.of_forall (fun x => (Real.exp_pos (t * f x)).le)) (hi t) (Real.exp (t ^ 2))
  have he : {x | Real.exp (t ^ 2) ≤ Real.exp (t * f x)} = {x | t ≤ f x} := by
    ext x
    simp only [mem_setOf_eq, Real.exp_le_exp, pow_two]
    exact mul_le_mul_iff_of_pos_left ht
  rw [he] at hm
  calc
    _ ≤ Real.exp (t ^ 2 / 2) / Real.exp (t ^ 2) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm (Real.exp (t ^ 2))] using hm.trans (hb t))
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

theorem scalar_unit_mgf_absolute_tail {α : Type} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ)
    (hi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * f x)) μ)
    (hb : ∀ r : ℝ, (∫ x, Real.exp (r * f x) ∂μ) ≤ Real.exp (r ^ 2 / 2))
    (t : ℝ) (ht : 0 ≤ t) : μ.real {x | t ≤ |f x|} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  have hp := scalar_unit_mgf_upper_tail μ f hi hb t ht
  have hn := scalar_unit_mgf_upper_tail μ (fun x => -f x)
    (fun r => by simpa only [mul_neg, neg_mul] using hi (-r))
    (fun r => by simpa only [mul_neg, neg_mul, neg_sq] using hb (-r)) t ht
  have he : {x | t ≤ |f x|} = {x | t ≤ f x} ∪ {x | t ≤ -f x} := by
    ext x
    change t ≤ |f x| ↔ t ≤ f x ∨ t ≤ -f x
    constructor
    · intro hx
      rcases le_total 0 (f x) with hf | hf
      · exact Or.inl (by simpa only [abs_of_nonneg hf] using hx)
      · exact Or.inr (by simpa only [abs_of_nonpos hf] using hx)
    · rintro (hx | hx)
      · exact hx.trans (le_abs_self _)
      · exact hx.trans (neg_le_abs _)
  rw [he]
  have hu := measureReal_union_le (μ := μ) {x | t ≤ f x} {x | t ≤ -f x}
  linarith

end
end Nonsmooth
