import Nonsmooth.IndependentCovariance

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem independent_integral_inner (μ : Measure α) [IsProbabilityMeasure μ]
    (X Y : α → E) (hI : IndepFun X Y μ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    (∫ a, ⟪X a, Y a⟫_ℝ ∂μ) = ⟪∫ a, X a ∂μ, ∫ a, Y a ∂μ⟫_ℝ := by
  let b := stdOrthonormalBasis ℝ E
  have hsum (x y : E) : ⟪x, y⟫_ℝ = ∑ j, ⟪b j, x⟫_ℝ * ⟪b j, y⟫_ℝ := by
    rw [← b.sum_inner_mul_inner x y]
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm x (b j)]
  calc
    _ = ∫ a, ∑ j, ⟪b j, X a⟫_ℝ * ⟪b j, Y a⟫_ℝ ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun a => hsum (X a) (Y a)))
    _ = ∑ j, ∫ a, ⟪b j, X a⟫_ℝ * ⟪b j, Y a⟫_ℝ ∂μ :=
      integral_finsetSum _ (fun j _ => (hX.const_inner (b j)).integrable_mul (hY.const_inner (b j)))
    _ = ∑ j, ⟪b j, ∫ a, X a ∂μ⟫_ℝ * ⟪b j, ∫ a, Y a ∂μ⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      have hm : Measurable (fun z : E => ⟪b j, z⟫_ℝ) := (continuous_const.inner continuous_id).measurable
      have he := (hI.comp hm hm).integral_fun_mul_eq_mul_integral (hX.const_inner (b j)).aestronglyMeasurable
        (hY.const_inner (b j)).aestronglyMeasurable
      simp only [Function.comp_def] at he
      rw [he, integral_inner (hX.integrable (by norm_num)), integral_inner (hY.integrable (by norm_num))]
    _ = _ := (hsum _ _).symm

theorem independent_centered_inner_zero (μ : Measure α) [IsProbabilityMeasure μ]
    (X Y : α → E) (hI : IndepFun X Y μ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    (∫ a, ⟪X a - ∫ b, X b ∂μ, Y a - ∫ b, Y b ∂μ⟫_ℝ ∂μ) = 0 := by
  have hXm : Measurable (fun z : E => z - ∫ a, X a ∂μ) := measurable_id.sub measurable_const
  have hYm : Measurable (fun z : E => z - ∫ a, Y a ∂μ) := measurable_id.sub measurable_const
  have hcX : MemLp (fun a => X a - ∫ b, X b ∂μ) 2 μ := hX.sub (memLp_const _)
  have hcY : MemLp (fun a => Y a - ∫ b, Y b ∂μ) 2 μ := hY.sub (memLp_const _)
  have he := independent_integral_inner μ _ _ (hI.comp hXm hYm) hcX hcY
  simp only [Function.comp_def] at he
  rw [he, integral_sub (hX.integrable (by norm_num)) (integrable_const _),
    integral_sub (hY.integrable (by norm_num)) (integrable_const _)]
  simp

end
end Nonsmooth
