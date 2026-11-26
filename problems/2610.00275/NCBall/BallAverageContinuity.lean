import NCBall.BallMeasure

/-! # Ball averaging makes every bounded measurable field continuous

After translating the integration domain, only a ball indicator varies.
Its discontinuity set is a sphere of Haar measure zero, so dominated
convergence applies even when the averaged field is merely measurable.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology
namespace NCBall

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem ball_indicator_continuousAt (g : E → F) (ρ : ℝ) (x₀ y : E) (hy : dist y x₀ ≠ ρ) :
    ContinuousAt (fun x => (ball x ρ).indicator g y) x₀ := by
  have hc : Continuous (fun x : E => dist y x) := continuous_const.dist continuous_id
  by_cases hlt : dist y x₀ < ρ
  · apply (continuousAt_const : ContinuousAt (fun _ : E => g y) x₀).congr_of_eventuallyEq
    filter_upwards [hc.continuousAt.eventually_lt_const hlt] with x hx
    exact indicator_of_mem (show y ∈ ball x ρ from hx) g
  · have hgt : ρ < dist y x₀ := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hy)
    apply (continuousAt_const : ContinuousAt (fun _ : E => (0 : F)) x₀).congr_of_eventuallyEq
    filter_upwards [hc.continuousAt.eventually_const_lt hgt] with x hx
    exact indicator_of_not_mem (show y ∉ ball x ρ from not_lt.mpr hx.le) g

theorem continuous_ball_setIntegral (τ : Measure E) [τ.IsAddHaarMeasure] {ρ : ℝ} (hρ : 0 < ρ)
    (g : E → F) (hg : Measurable g) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ y, ‖g y‖ ≤ B) :
    Continuous (fun x => ∫ y in ball x ρ, g y ∂τ) := by
  have he : (fun x => ∫ y in ball x ρ, g y ∂τ) =
      (fun x => ∫ y, (ball x ρ).indicator g y ∂τ) := by
    funext x
    exact (integral_indicator isOpen_ball.measurableSet).symm
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let b : E → ℝ := (closedBall x₀ (ρ + 1)).indicator (fun _ => B)
  have hb : Integrable b τ := by
    apply (integrable_indicator_iff isClosed_closedBall.measurableSet).2
    exact integrableOn_const.mpr (Or.inr measure_closedBall_lt_top)
  have hboundary : ∀ᵐ y ∂τ, dist y x₀ ≠ ρ := by
    apply ae_iff.mpr
    simpa only [not_not, ← mem_sphere] using Measure.addHaar_sphere_of_ne_zero τ x₀ hρ.ne'
  apply continuousAt_of_dominated
    (Eventually.of_forall (fun x => (hg.indicator isOpen_ball.measurableSet).aestronglyMeasurable)) _ hb
    (hboundary.mono (fun y hy => ball_indicator_continuousAt g ρ x₀ y hy))
  filter_upwards [ball_mem_nhds x₀ (show (0 : ℝ) < 1 by norm_num)] with x hx
  filter_upwards [] with y
  by_cases hy : y ∈ ball x ρ
  · have hybig : y ∈ closedBall x₀ (ρ + 1) := by
      rw [mem_closedBall]
      have ht := dist_triangle y x x₀
      have hy' : dist y x < ρ := hy
      have hx' : dist x x₀ < 1 := hx
      linarith
    simp only [b, indicator_of_mem hy g, indicator_of_mem hybig]
    exact hbound y
  · rw [indicator_of_not_mem hy g, norm_zero]
    exact indicator_nonneg (fun _ _ => hB) y

theorem ballAverage_continuous_of_bounded (τ : Measure E) [τ.IsAddHaarMeasure]
    (ρ : ℝ) (hρ : 0 < ρ) (g : E → F) (hg : Measurable g) {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ y, ‖g y‖ ≤ B) : Continuous (ballAverage τ ρ hρ g) := by
  have he : ballAverage τ ρ hρ g =
      fun x => (τ (ball (0 : E) ρ)).toReal⁻¹ • ∫ y in ball x ρ, g y ∂τ := by
    funext x
    exact ballAverage_eq_translatedIntegral τ ρ hρ g x
  rw [he]
  exact (continuous_ball_setIntegral τ hρ g hg hB hbound).const_smul _

end NCBall
