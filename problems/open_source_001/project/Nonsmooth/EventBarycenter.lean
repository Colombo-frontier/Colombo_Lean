import Nonsmooth.ConditioningProbability
import Mathlib.Analysis.Convex.Integral

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem integrable_under_event {α F : Type} [MeasurableSpace α] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {μ : Measure α} [IsFiniteMeasure μ] {f : α → F}
    (hf : Integrable f μ) {A : Set α} (hA : μ A ≠ 0) : Integrable f μ[|A] := by
  exact hf.restrict.smul_measure (ENNReal.inv_ne_top.mpr hA)

theorem integral_event_le {α : Type} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (A : Set α) :
    (∫ x, f x ∂μ[|A]) ≤ (μ.real A)⁻¹ * ∫ x, f x ∂μ := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hf hf0) (by positivity)

/-- A dimension-free event barycenter estimate obtained directly from exponential moments. -/
theorem event_barycenter_of_exp_moments {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsProbabilityMeasure μ] {V : α → E} (hV : Integrable V μ)
    {v K : ℝ} (hv : 0 < v) (hK : 0 < K)
    (hInt : ∀ u : E, Integrable (fun x => Real.exp ⟪u, V x⟫_ℝ) μ)
    (hMGF : ∀ u : E, (∫ x, Real.exp ⟪u, V x⟫_ℝ ∂μ) ≤ K * Real.exp (v * ‖u‖ ^ 2 / 2))
    (A : Set α) (hA : μ A ≠ 0) :
    ‖∫ x, V x ∂μ[|A]‖ ^ 2 ≤ 2 * v * Real.log (K / μ.real A) := by
  letI : IsProbabilityMeasure μ[|A] := cond_isProbabilityMeasure hA
  let M : E := ∫ x, V x ∂μ[|A]
  let u : E := v⁻¹ • M
  have hVc : Integrable V μ[|A] := integrable_under_event hV hA
  have hJ := (convexOn_exp : ConvexOn ℝ Set.univ Real.exp).map_integral_le
    Real.continuous_exp.continuousOn isClosed_univ (Eventually.of_forall (fun _ => mem_univ _))
    (hVc.const_inner u) (integrable_under_event (hInt u) hA)
  rw [integral_inner hVc] at hJ
  have hupper := (integral_event_le (hInt u) (Eventually.of_forall (fun _ => (Real.exp_pos _).le)) A).trans
    (mul_le_mul_of_nonneg_left (hMGF u) (by positivity : 0 ≤ (μ.real A)⁻¹))
  have hm : 0 < μ.real A := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have hinner : ⟪u, M⟫_ℝ = ‖M‖ ^ 2 / v := by
    simp only [u, real_inner_smul_left, real_inner_self_eq_norm_sq, div_eq_inv_mul]
  have hnorm : v * ‖u‖ ^ 2 / 2 = ‖M‖ ^ 2 / (2 * v) := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv), mul_pow]
    field_simp
  change Real.exp ⟪u, M⟫_ℝ ≤ _ at hJ
  have h := hJ.trans hupper
  rw [hinner, hnorm] at h
  have he : (μ.real A)⁻¹ * (K * Real.exp (‖M‖ ^ 2 / (2 * v))) =
      Real.exp (Real.log (K / μ.real A) + ‖M‖ ^ 2 / (2 * v)) := by
    rw [Real.exp_add, Real.exp_log (div_pos hK hm)]
    ring
  rw [he, Real.exp_le_exp] at h
  change ‖M‖ ^ 2 ≤ _
  have hv2 : 0 < 2 * v := by positivity
  have he2 : ‖M‖ ^ 2 / v = 2 * (‖M‖ ^ 2 / (2 * v)) := by field_simp
  rw [he2] at h
  have hh : ‖M‖ ^ 2 / (2 * v) ≤ Real.log (K / μ.real A) := by linarith
  exact (div_le_iff₀ hv2).mp hh |>.trans_eq (mul_comm _ _)

end
end Nonsmooth
