import SecondOrder.RademacherProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint

open MeasureTheory
open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder
noncomputable section

theorem rademacherVector_projection_probability_all {d : ℕ} (g : Point d) :
    (1 : ℝ)/12 ≤ (signLaw d).real
      {w | ‖g‖^2/2 ≤ ⟪g, rademacherVector w⟫_ℝ ^ 2} := by
  by_cases hg : g = 0
  · subst g
    norm_num
  · exact rademacherVector_projection_probability g hg

theorem rademacherInit_projection_probability_all {d : ℕ} (hd : 0 < d) (g : Point d) :
    (1 : ℝ)/12 ≤ (signLaw d).real
      {w | ‖g‖^2/(2*d) ≤ ⟪g, rademacherInit w⟫_ℝ ^ 2} := by
  by_cases hg : g = 0
  · subst g
    norm_num
  · exact rademacherInit_projection_probability hd g hg

theorem inner_sq_le_norm_sq_of_unit {d : ℕ} {g : Point d} (hg : ‖g‖ = 1)
    (v : Point d) : ⟪g,v⟫_ℝ^2 ≤ ‖v‖^2 := by
  have hb := abs_real_inner_le_norm g v
  rw [hg, one_mul] at hb
  have hs := pow_le_pow_left₀ (abs_nonneg ⟪g,v⟫_ℝ) hb 2
  simpa only [sq_abs] using hs

/-- Transpose growth in one analysis direction implies norm growth for an
actual random initialization, with no knowledge of that direction required. -/
theorem rademacherVector_operator_probability {d : ℕ} (L : Point d →L[ℝ] Point d)
    {g : Point d} (hg : ‖g‖ = 1) :
    (1 : ℝ)/12 ≤ (signLaw d).real
      {w | ‖ContinuousLinearMap.adjoint L g‖^2/2 ≤ ‖L (rademacherVector w)‖^2} := by
  refine (rademacherVector_projection_probability_all (ContinuousLinearMap.adjoint L g)).trans ?_
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [ContinuousLinearMap.adjoint_inner_left] at hw
  exact hw.trans (inner_sq_le_norm_sq_of_unit hg _)

theorem rademacherInit_operator_probability {d : ℕ} (hd : 0 < d)
    (L : Point d →L[ℝ] Point d) {g : Point d} (hg : ‖g‖ = 1) :
    (1 : ℝ)/12 ≤ (signLaw d).real
      {w | ‖ContinuousLinearMap.adjoint L g‖^2/(2*d) ≤ ‖L (rademacherInit w)‖^2} := by
  refine (rademacherInit_projection_probability_all hd (ContinuousLinearMap.adjoint L g)).trans ?_
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [ContinuousLinearMap.adjoint_inner_left] at hw
  exact hw.trans (inner_sq_le_norm_sq_of_unit hg _)

/-- Integrate a conditional success probability on a measurable good event.
The two random sources are independent by the actual product measure. -/
theorem product_success_of_sections {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ρ : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    {G : Set Ω} (hG : MeasurableSet G) {S : Set (Ω × Ξ)} (hS : MeasurableSet S)
    {c : ℝ} (hs : ∀ z ∈ G, c ≤ ρ.real {w | (z,w) ∈ S}) :
    c * μ.real G ≤ (μ.prod ρ).real S := by
  let I : Ω × Ξ → ℝ := S.indicator (fun _ => 1)
  have hi : Integrable I (μ.prod ρ) := (integrable_const (1:ℝ)).indicator hS
  have hsections (z : Ω) : (∫ w, I (z,w) ∂ρ) = ρ.real {w | (z,w) ∈ S} := by
    have hm : MeasurableSet {w | (z,w) ∈ S} :=
      hS.preimage (measurable_const.prodMk measurable_id)
    exact integral_indicator_one hm
  have hb : (∫ z, G.indicator (fun _ => c) z ∂μ) ≤ ∫ z, ∫ w, I (z,w) ∂ρ ∂μ := by
    apply integral_mono ((integrable_const c).indicator hG) hi.integral_prod_left
    intro z
    change G.indicator (fun _ => c) z ≤ ∫ w, I (z,w) ∂ρ
    rw [hsections]
    by_cases hz : z ∈ G
    · simpa only [Set.indicator_of_mem hz] using hs z hz
    · simp only [Set.indicator_of_not_mem hz]
      exact ENNReal.toReal_nonneg
  rw [integral_indicator_const c hG, ← integral_prod _ hi] at hb
  have hiS : (∫ z, I z ∂μ.prod ρ) = (μ.prod ρ).real S := integral_indicator_one hS
  rw [hiS] at hb
  simpa only [smul_eq_mul, mul_comm] using hb

end
end SecondOrder
