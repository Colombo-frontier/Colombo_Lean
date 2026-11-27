import SphereSmoothingRadialCutoff
open MeasureTheory MeasureTheory.Measure Set Metric Function Filter
open scoped NNReal Topology
namespace Task006.SphereSmoothing
noncomputable section

theorem radialCutoff_tendsto {E : Type*} [SeminormedAddCommGroup E] (ρ : ℝ) (z : E) :
    Tendsto (fun ε : ℝ => radialCutoff ρ ε z) (𝓝[>] 0)
      (𝓝 ((closedBall 0 ρ).indicator (fun _ : E => (1:ℝ)) z)) := by
  by_cases hz : z ∈ closedBall 0 ρ
  · rw [indicator_of_mem hz]
    have hn : ‖z‖ ≤ ρ := by simpa only [mem_closedBall,dist_zero_right] using hz
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (radialCutoff_eq_one hε hn).symm
  · rw [indicator_of_notMem hz]
    have hn : ρ < ‖z‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hz
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hn)] with ε hε
    exact (radialCutoff_eq_zero hε.1 (by linarith [hε.2])).symm

/-- Dominated convergence of the actual radial cutoff integral, using only
boundedness of g and finite-volume support of the cutoff. -/
theorem radialCutoff_smul_integral_tendsto {d : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {g : EuclideanSpace ℝ (Fin d) → V} {K ρ : ℝ}
    (hm : AEStronglyMeasurable g volume) (hb : ∀ z, ‖g z‖ ≤ K) :
    Tendsto (fun ε : ℝ => ∫ z, radialCutoff ρ ε z • g z) (𝓝[>] 0)
      (𝓝 (∫ z in closedBall 0 ρ, g z)) := by
  let C : Set (EuclideanSpace ℝ (Fin d)) := closedBall 0 (ρ+1)
  let bound : EuclideanSpace ℝ (Fin d) → ℝ := C.indicator (fun _ => K)
  have hK : 0 ≤ K := le_trans (norm_nonneg (g 0)) (hb 0)
  have hi : Integrable bound volume :=
    (integrableOn_const (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (s := C) (C := K) (hs := measure_closedBall_lt_top.ne)).integrable_indicator measurableSet_closedBall
  have ht : Tendsto (fun ε : ℝ => ∫ z, radialCutoff ρ ε z • g z) (𝓝[>] 0)
      (𝓝 (∫ z, (closedBall 0 ρ).indicator g z)) := by
    apply tendsto_integral_filter_of_dominated_convergence bound
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (radialCutoff_lipschitz (E := EuclideanSpace ℝ (Fin d)) hε).continuous.measurable.aestronglyMeasurable.smul hm
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ)<1)] with ε hε
      apply ae_of_all
      intro z
      by_cases hz : z ∈ C
      · change ‖radialCutoff ρ ε z • g z‖ ≤ C.indicator (fun _ => K) z
        rw [indicator_of_mem hz, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (radialCutoff_nonneg ρ ε z)]
        exact (mul_le_mul (radialCutoff_le_one ρ ε z) (hb z) (norm_nonneg _) (by norm_num)).trans_eq (one_mul K)
      · have hn : ρ+ε ≤ ‖z‖ := by
          have hh : ρ+1 < ‖z‖ := by simpa only [C,mem_closedBall,dist_zero_right,not_le] using hz
          linarith [hε.2]
        simp only [radialCutoff_eq_zero hε.1 hn, zero_smul, norm_zero]
        exact le_of_eq (by simp only [bound,indicator_of_notMem hz])
    · exact hi
    · apply ae_of_all
      intro z
      have hh := (radialCutoff_tendsto ρ z).smul (tendsto_const_nhds (x := g z))
      have heq : (closedBall 0 ρ).indicator (fun _ : EuclideanSpace ℝ (Fin d) => (1:ℝ)) z • g z =
          (closedBall 0 ρ).indicator g z := by
        by_cases hz : z ∈ closedBall 0 ρ
        · simp only [indicator_of_mem hz,one_smul]
        · simp only [indicator_of_notMem hz,zero_smul]
      rwa [heq] at hh
  simpa only [integral_indicator measurableSet_closedBall] using ht

/-- Bochner-valued right annulus averages converge to their boundary value. -/
theorem interval_average_tendsto {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {g : ℝ → V} (hg : Continuous g) (ρ : ℝ) :
    Tendsto (fun ε : ℝ => ε⁻¹ • ∫ r in ρ..ρ+ε, g r) (𝓝[>] 0) (𝓝 (g ρ)) := by
  have hd := intervalIntegral.integral_hasDerivAt_right (a := ρ) (b := ρ)
    (IntervalIntegrable.refl : IntervalIntegrable g volume ρ ρ)
    (hg.stronglyMeasurableAtFilter volume (𝓝 ρ)) hg.continuousAt
  simpa only [intervalIntegral.integral_same,sub_zero] using hd.tendsto_slope_zero_right

end
end Task006.SphereSmoothing
