import Nonsmooth.LogarithmicVolumeRounds

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem uniform_localization_stage_budget_bound (d : ℕ) (hd : 2 ≤ d) {A : ℝ} (hA : 0 ≤ A) :
    (⌈A * (d : ℝ) * Real.log ((d : ℝ) + 1)⌉₊ : ℝ) ≤
      (A + 1) * (d : ℝ) * Real.log ((d : ℝ) + 1) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : (1 / 2 : ℝ) ≤ Real.log ((d : ℝ) + 1) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  have hv : 1 ≤ (d : ℝ) * Real.log ((d : ℝ) + 1) := by nlinarith
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ A * (d : ℝ) * Real.log ((d : ℝ) + 1) by positivity)
  nlinarith only [hceil, hv]

theorem total_localization_query_bound (d : ℕ) (hd : 2 ≤ d) {A c η : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1) (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ((volumeLocalizationRounds d c η * ⌈A * (d : ℝ) * Real.log ((d : ℝ) + 1)⌉₊ : ℕ) : ℝ) ≤
      (3 * (A + 1) / c) * (d : ℝ) ^ 2 * Real.log ((d : ℝ) + 1) * Real.log (1 / η) := by
  have hN := volumeLocalizationRounds_bound d hd hc hc1 hη hηhalf
  have hB := uniform_localization_stage_budget_bound d hd hA
  have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((one_le_div hη).mpr (by linarith))
  have hm := mul_le_mul hN hB (show (0 : ℝ) ≤ ⌈A * (d : ℝ) * Real.log ((d : ℝ) + 1)⌉₊ from Nat.cast_nonneg _)
    (show 0 ≤ (3 / c) * (d : ℝ) * Real.log (1 / η) by positivity)
  rw [Nat.cast_mul]
  convert! hm using 1 <;> ring

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

omit [Nontrivial E] in
/-- A fixed volume loss per localization round gives the manuscript's relative-oscillation accuracy. -/
theorem ball_relative_error_of_fractional_localization (μ : Measure E) [IsAddHaarMeasure μ]
    {R c η : ℝ} (hR : 0 < R) (hc : 0 < c) (hc1 : c < 1) (hη : 0 < η) (hη1 : η ≤ 1)
    {f : E → ℝ} (hcont : ContinuousOn f (closedBall (0 : E) R))
    (hconv : ConvexOn ℝ (closedBall (0 : E) R) f) (y : Feasible E R)
    (K : ℕ → Set E) (hK0 : K 0 = closedBall (0 : E) R)
    (hstep : ∀ n < volumeLocalizationRounds (Module.finrank ℝ E) c η,
      μ (K (n + 1)) + ENNReal.ofReal c * μ (K n) ≤ μ (K n))
    (hkeep : ∀ z ∈ closedBall (0 : E) R, f z < f y.val →
      z ∈ K (volumeLocalizationRounds (Module.finrank ℝ E) c η)) :
    f y.val - minimumValue R f ≤ η * (maximumValue R f - minimumValue R f) := by
  have hv0 : 0 < μ (K 0) := by rw [hK0]; exact measure_closedBall_pos μ 0 hR
  have hvfinite : μ (K 0) < ∞ := by rw [hK0]; exact measure_closedBall_lt_top
  have hvol := volume_fraction_below_relative_threshold (fun n => μ (K n)) (Module.finrank ℝ E)
    hc hc1 hη hv0 hvfinite hstep
  rw [hK0] at hvol
  exact ball_relative_error_of_small_retained_volume μ hR.le hcont hconv y _ hη.le hη1 hkeep hvol

end
end Nonsmooth
