import SecondOrder.LikelihoodNormBound
import Mathlib.Tactic

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SecondOrder
noncomputable section

theorem mul_le_klFun_add_exp {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    r*t ≤ klFun r+Real.exp t-1 := by
  rcases eq_or_lt_of_le hr with he | hr
  · rw [← he,klFun_zero,zero_mul]
    linarith [Real.exp_pos t]
  · have hx := Real.add_one_le_exp (t-Real.log r)
    rw [Real.exp_sub,Real.exp_log hr] at hx
    have hy := (le_div_iff₀ hr).mp hx
    rw [klFun_apply]
    nlinarith only [hy]

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Entropy controls every integrable test with reference exponential
moment at most one. The statement concerns the actual two measures. -/
theorem integral_le_klDiv_of_exp_integral_le_one (hfin : klDiv μ ν ≠ ∞)
    {f : Ω → ℝ} (hf : Integrable f μ) (he : Integrable (fun x => Real.exp (f x)) ν)
    (hmgf : (∫ x, Real.exp (f x) ∂ν) ≤ 1) :
    (∫ x, f x ∂μ) ≤ (klDiv μ ν).toReal := by
  have hac := (klDiv_ne_top_iff.mp hfin).1
  have hkl := (integrable_klFun_rnDeriv_iff hac).mpr (klDiv_ne_top_iff.mp hfin).2
  have hi : Integrable (fun x => (μ.rnDeriv ν x).toReal*f x) ν :=
    (integrable_rnDeriv_smul_iff hac).mpr hf
  calc
    _ = ∫ x, (μ.rnDeriv ν x).toReal*f x ∂ν := (integral_rnDeriv_smul hac).symm
    _ ≤ ∫ x, klFun (μ.rnDeriv ν x).toReal+Real.exp (f x)-1 ∂ν :=
      integral_mono hi ((hkl.add he).sub (integrable_const _))
        (fun x => mul_le_klFun_add_exp ENNReal.toReal_nonneg (f x))
    _ = (klDiv μ ν).toReal+(∫ x, Real.exp (f x) ∂ν)-1 := by
      rw [integral_sub (f := fun x => klFun (μ.rnDeriv ν x).toReal+Real.exp (f x))
          (g := fun _ => (1:ℝ)) (hkl.add he) (integrable_const _),
        integral_add hkl he,← toReal_klDiv_eq_integral_klFun hac]
      simp
    _ ≤ (klDiv μ ν).toReal := by linarith

end
end SecondOrder
