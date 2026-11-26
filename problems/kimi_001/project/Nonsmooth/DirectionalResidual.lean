import Nonsmooth.PosteriorEnergy

open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {m₀ : MeasurableSpace α} {Q : Measure α} [IsProbabilityMeasure Q]

theorem conditional_direction_residual_energy {m : MeasurableSpace α} (hm : m ≤ m₀)
    {V : α → E} (hV : MemLp V 2 Q) (u : E) :
    (∫ a, ⟪u, V a - (Q[V | m]) a⟫_ℝ ^ 2 ∂Q) =
      (∫ a, ⟪u, V a⟫_ℝ ^ 2 ∂Q) - ∫ a, ⟪u, (Q[V | m]) a⟫_ℝ ^ 2 ∂Q := by
  letI : MeasurableSpace α := m₀
  let M := Q[V | m]
  have hM : MemLp M 2 Q := hV.condExp (by norm_num)
  have hMm : AEStronglyMeasurable[m] M Q := stronglyMeasurable_condExp.aestronglyMeasurable
  let X : α → E := fun a => ⟪u, M a⟫_ℝ • u
  have hX : MemLp X 2 Q := (memLp_top_const u).smul (hM.const_inner u)
  have hscalar : AEStronglyMeasurable[m] (fun a => ⟪u, M a⟫_ℝ) Q := hMm.const_inner
  have hXm : AEStronglyMeasurable[m] X Q := hscalar.smul aestronglyMeasurable_const
  have he := integral_inner_condExp hm hV hX hXm
  change (∫ a, ⟪V a, ⟪u, M a⟫_ℝ • u⟫_ℝ ∂Q) =
    ∫ a, ⟪M a, ⟪u, M a⟫_ℝ • u⟫_ℝ ∂Q at he
  simp only [inner_smul_right, real_inner_comm u, ← pow_two] at he
  have hiV := (hV.const_inner u).integrable_sq
  have hiM := (hM.const_inner u).integrable_sq
  have hiP : Integrable (fun a => ⟪u, M a⟫_ℝ * ⟪u, V a⟫_ℝ) Q := by
    simpa only [X, inner_smul_right, real_inner_comm u] using integrable_inner_of_memLp hV hX
  have hpoly (a : α) : ⟪u, V a - M a⟫_ℝ ^ 2 =
      ⟪u, V a⟫_ℝ ^ 2 - 2 * (⟪u, M a⟫_ℝ * ⟪u, V a⟫_ℝ) + ⟪u, M a⟫_ℝ ^ 2 := by
    rw [inner_sub_right]
    ring
  change (∫ a, ⟪u, V a - M a⟫_ℝ ^ 2 ∂Q) = _
  simp_rw [hpoly]
  have hiSub : Integrable (fun a => ⟪u, V a⟫_ℝ ^ 2 - 2 * (⟪u, M a⟫_ℝ * ⟪u, V a⟫_ℝ)) Q :=
    hiV.sub (hiP.const_mul 2)
  rw [integral_add hiSub hiM, integral_sub hiV (hiP.const_mul 2), integral_const_mul, he]
  ring

/-- This controls each fixed direction after arbitrary conditioning; the direction is fixed before the data. -/
theorem conditional_direction_residual_le {m : MeasurableSpace α} (hm : m ≤ m₀)
    {V : α → E} (hV : MemLp V 2 Q) (u : E) :
    (∫ a, ⟪u, V a - (Q[V | m]) a⟫_ℝ ^ 2 ∂Q) ≤ ∫ a, ⟪u, V a⟫_ℝ ^ 2 ∂Q := by
  rw [conditional_direction_residual_energy hm hV u]
  exact sub_le_self _ (integral_nonneg (fun _ => sq_nonneg _))

end
end Nonsmooth
