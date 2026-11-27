import HaarRebalancingUniform
set_option maxHeartbeats 1000000
open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal NNReal
namespace Task006.HaarRebalancing
noncomputable section
variable {d : ℕ}

/-- Haar averaging for any fixed radius, including radius zero/dimension zero. -/
theorem invariant_radius_lintegral_eq_haar
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (x₀ : EuclideanSpace ℝ (Fin d)) (hradius : ∀ᵐ x ∂μ, ‖x‖=‖x₀‖)
    (hrot : ∀ Q : OrthogonalGroup d, Measure.map (action (d := d) Q) μ=μ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ∫⁻ Q, f (action (d := d) Q x₀) ∂orthogonalHaarProbability d := by
  have hfixed (Q : OrthogonalGroup d) :
      (∫⁻ x, f (action (d := d) Q x) ∂μ) = ∫⁻ x, f x ∂μ := by
    rw [← lintegral_map hf (action (d := d) Q).continuous.measurable, hrot]
  calc
    (∫⁻ x, f x ∂μ) = ∫⁻ Q, ∫⁻ x, f (action (d := d) Q x) ∂μ ∂orthogonalHaarProbability d := by
      simp_rw [hfixed]
      simp
    _ = ∫⁻ x, ∫⁻ Q, f (action (d := d) Q x) ∂orthogonalHaarProbability d ∂μ := by
      apply lintegral_lintegral_swap
      exact (hf.comp action_joint_continuous.measurable).aemeasurable
    _ = ∫⁻ _x, ∫⁻ Q, f (action (d := d) Q x₀) ∂orthogonalHaarProbability d ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hradius] with x hx
      exact orbit_lintegral_eq f x x₀ hx
    _ = _ := by simp

/-- Actual invariant probability is the concrete Haar orbit law; no sphere
uniqueness premise is assumed, and zero radius and dimension are covered. -/
theorem invariant_radius_probability_eq_haar
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (x₀ : EuclideanSpace ℝ (Fin d)) (hradius : ∀ᵐ x ∂μ, ‖x‖=‖x₀‖)
    (hrot : ∀ Q : OrthogonalGroup d, Measure.map (action (d := d) Q) μ=μ) :
    μ = Measure.map (fun Q : OrthogonalGroup d => action (d := d) Q x₀) (orthogonalHaarProbability d) := by
  apply Measure.ext
  intro s hs
  have h := invariant_radius_lintegral_eq_haar μ x₀ hradius hrot
    (s.indicator (fun _ => (1:ℝ≥0∞))) (measurable_const.indicator hs)
  have hm : Measurable (fun Q : OrthogonalGroup d => action (d := d) Q x₀) :=
    (action_joint_continuous (d := d)).measurable.of_uncurry_right
  rw [Measure.map_apply hm hs]
  have hint : (∫⁻ Q : OrthogonalGroup d,
      s.indicator (fun _ => (1:ℝ≥0∞)) (action (d := d) Q x₀) ∂orthogonalHaarProbability d) =
      orthogonalHaarProbability d ((fun Q : OrthogonalGroup d => action (d := d) Q x₀) ⁻¹' s) := by
    change (∫⁻ Q : OrthogonalGroup d,
      ((fun Q : OrthogonalGroup d => action (d := d) Q x₀) ⁻¹' s).indicator (fun _ => (1:ℝ≥0∞)) Q
        ∂orthogonalHaarProbability d) = _
    simp only [lintegral_indicator_const (hs.preimage hm), one_mul]
  have hleft : μ s = ∫⁻ Q : OrthogonalGroup d,
      s.indicator (fun _ => (1:ℝ≥0∞)) (action (d := d) Q x₀) ∂orthogonalHaarProbability d := by
    simpa only [lintegral_indicator_const hs, one_mul] using h
  exact hleft.trans hint

end
end Task006.HaarRebalancing
