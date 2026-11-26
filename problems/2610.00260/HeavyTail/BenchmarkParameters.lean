import HeavyTail.BenchmarkThreeHalves

/-! The shared public parameter family for the manuscript p=3/2 benchmark. -/
noncomputable section
namespace HeavyTail

def benchmarkParameters (e μ : ℝ) (T : ℕ) (he : 256 ≤ e) (hμ : 0 ≤ μ) : OracleParameters where
  p := 3 / 2
  G := 1
  D := 1
  L := 1
  s := benchmarkNoise e
  μ := μ
  δ := benchmarkDelta e
  T := T
  p_gt_one := by norm_num
  p_le_two := by norm_num
  G_pos := by norm_num
  D_pos := by norm_num
  s_pos := Real.rpow_pos_of_pos (by linarith : 0 < e) _
  s_le_L := Real.rpow_le_one_of_one_le_of_nonpos (by linarith : 1 ≤ e) (by norm_num)
  μ_nonneg := hμ
  δ_pos := (benchmark_delta_valid (by linarith : 16 ≤ e)).1
  δ_lt_tenth := (benchmark_delta_valid (by linarith : 16 ≤ e)).2

@[simp] theorem benchmarkParameters_dimension (e μ : ℝ) (T : ℕ) (he : 256 ≤ e) (hμ : 0 ≤ μ) :
    (benchmarkParameters e μ T he hμ).L ^ 2 / (benchmarkParameters e μ T he hμ).s ^ 2 = e :=
  benchmark_dimension (by linarith : 0 < e)

end HeavyTail
