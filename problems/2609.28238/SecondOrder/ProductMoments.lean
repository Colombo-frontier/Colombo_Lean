import SecondOrder.IntegralMoments
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder

variable {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]

theorem integrable_product_fst {X : Ω → E} (hX : Integrable X μ) :
    Integrable (fun w : Ω × Ξ => X w.1) (μ.prod η) := by
  apply (integrable_prod_iff hX.aestronglyMeasurable.fst).mpr
  refine ⟨Eventually.of_forall (fun x => integrable_const (X x)), ?_⟩
  simpa using hX.norm

theorem integrable_product_snd {Y : Ξ → E} (hY : Integrable Y η) :
    Integrable (fun w : Ω × Ξ => Y w.2) (μ.prod η) := by
  simpa using (integrable_product_fst (η := μ) hY).swap

theorem integrable_product_inner {X : Ω → E} {Y : Ξ → E}
    (hX : Integrable X μ) (hY : Integrable Y η) :
    Integrable (fun w : Ω × Ξ => ⟪X w.1,Y w.2⟫_ℝ) (μ.prod η) :=
  hX.op_fst_snd (continuous_fst.inner continuous_snd)
    ⟨1, fun x y => by simpa using norm_inner_le_norm (𝕜 := ℝ) x y⟩ hY

theorem integrable_product_sum_sq {X : Ω → E} {Y : Ξ → E}
    (hX : Integrable X μ) (hY : Integrable Y η)
    (hX2 : Integrable (fun w => ‖X w‖^2) μ)
    (hY2 : Integrable (fun w => ‖Y w‖^2) η) :
    Integrable (fun w : Ω × Ξ => ‖X w.1+Y w.2‖^2) (μ.prod η) := by
  have hi := ((integrable_product_fst (η := η) hX2).add
    ((integrable_product_inner hX hY).const_mul 2)).add (integrable_product_snd (μ := μ) hY2)
  simpa only [norm_add_sq_real] using hi

theorem integral_product_sum {X : Ω → E} {Y : Ξ → E}
    (hX : Integrable X μ) (hY : Integrable Y η) :
    (∫ w : Ω × Ξ, X w.1+Y w.2 ∂μ.prod η) = (∫ x, X x ∂μ)+(∫ y, Y y ∂η) := by
  rw [integral_add (integrable_product_fst hX) (integrable_product_snd hY),
    integral_fun_fst, integral_fun_snd]
  simp

/-- Independent centered vectors have additive second moments. Both samples
are integrated over their actual product law. -/
theorem integral_product_sum_sq {X : Ω → E} {Y : Ξ → E}
    (hX : Integrable X μ) (hY : Integrable Y η)
    (hX2 : Integrable (fun w => ‖X w‖^2) μ)
    (hY2 : Integrable (fun w => ‖Y w‖^2) η)
    (hY0 : (∫ y, Y y ∂η) = 0) :
    (∫ w : Ω × Ξ, ‖X w.1+Y w.2‖^2 ∂μ.prod η) =
      (∫ x, ‖X x‖^2 ∂μ)+(∫ y, ‖Y y‖^2 ∂η) := by
  rw [integral_prod _ (integrable_product_sum_sq hX hY hX2 hY2)]
  have he (x : Ω) : (∫ y, ‖X x+Y y‖^2 ∂η) = (∫ y, ‖Y y‖^2 ∂η)+‖X x‖^2 := by
    simpa only [add_comm (X x)] using integral_norm_add_sq_of_mean_zero hY hY2 hY0 (X x)
  simp_rw [he]
  rw [integral_add (integrable_const _) hX2]
  simp [add_comm]

end SecondOrder
