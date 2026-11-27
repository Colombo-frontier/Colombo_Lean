import Nonsmooth.ConditioningExhaustion
import Nonsmooth.EventBarycenter

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α : Type} [MeasurableSpace α]

theorem integral_mul_centered_eq (μ : Measure α) (f g : α → ℝ)
    (hg : Integrable g μ) (hgf : Integrable (fun x => g x * f x) μ) :
    (∫ x, g x * (f x - ∫ y, f y ∂μ) ∂μ) =
      (∫ x, g x * f x ∂μ) - (∫ x, g x ∂μ) * (∫ x, f x ∂μ) := by
  simp_rw [mul_sub]
  rw [integral_sub hgf (hg.mul_const _), integral_mul_const]

theorem centered_product_conditioning_exhaustion_tendsto (μ : Measure α) [IsProbabilityMeasure μ]
    (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n))
    (hmono : Monotone A) (hcover : (⋃ n, A n) = univ) (hpos : ∀ n, μ (A n) ≠ 0) :
    Tendsto (fun n => ∫ x, g x * (f x - ∫ y, f y ∂μ[|A n]) ∂μ[|A n])
      atTop (𝓝 (∫ x, g x * (f x - ∫ y, f y ∂μ) ∂μ)) := by
  have hf1 : Integrable f μ := hf.integrable (by norm_num)
  have hg1 : Integrable g μ := hg.integrable (by norm_num)
  have hgf : Integrable (fun x => g x * f x) μ := hg.integrable_mul hf
  have hfL := integral_conditioning_exhaustion_tendsto μ hf1 A hA hmono hcover
  have hgL := integral_conditioning_exhaustion_tendsto μ hg1 A hA hmono hcover
  have hpL := integral_conditioning_exhaustion_tendsto μ hgf A hA hmono hcover
  rw [integral_mul_centered_eq μ f g hg1 hgf]
  have he (n : ℕ) :
      (∫ x, g x * (f x - ∫ y, f y ∂μ[|A n]) ∂μ[|A n]) =
        (∫ x, g x * f x ∂μ[|A n]) - (∫ x, g x ∂μ[|A n]) * (∫ x, f x ∂μ[|A n]) :=
    integral_mul_centered_eq _ f g (integrable_under_event hg1 (hpos n))
      (integrable_under_event hgf (hpos n))
  convert hpL.sub (hgL.mul hfL) using 1
  exact funext he

end
end Nonsmooth
