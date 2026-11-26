import Matvec.Model

/-! Explicit accuracy scales in the main sequence theorem. Constants are
conservative; no dimension-dependent factor is hidden in them. -/
namespace Matvec
noncomputable section

theorem rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

theorem log_twice_add_two {x : ℝ} (hx : 0 ≤ x) :
    Real.log (2 * x + 2) ≤ 2 * Real.log (x + 2) := by
  calc
    _ ≤ Real.log ((x + 2) ^ 2) := Real.log_le_log (by linarith) (by nlinarith [sq_nonneg x])
    _ = _ := by rw [Real.log_pow]; norm_num

theorem ball_accuracy_threshold {d N : ℕ} (hd : 0 < d) (hN : 0 < N) (hdN : d ≤ 2 * N)
    {κ K : ℝ} (hκ : 0 < κ) (hK : 0 < K) (hκN : κ ≤ K * N) :
    (1 / (1024 * K)) / (N : ℝ) ^ (3 / 2 : ℝ) ≤
      (1 / (4 * κ) / (8 * Real.sqrt d)) / 16 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsN : 0 < Real.sqrt (N : ℝ) := by positivity
  have hsd : 0 < Real.sqrt (d : ℝ) := by positivity
  have hds : Real.sqrt (d : ℝ) ≤ 2 * Real.sqrt N := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hdNR : (d : ℝ) ≤ 2 * N := by exact_mod_cast hdN
    nlinarith [Real.sq_sqrt hNR.le]
  have hprod : κ * Real.sqrt d ≤ (K * N) * (2 * Real.sqrt N) :=
    mul_le_mul hκN hds hsd.le (by positivity)
  rw [rpow_three_halves hNR]
  have hl : (1 / (1024 * K)) / ((N : ℝ) * Real.sqrt N) =
      1 / (1024 * K * N * Real.sqrt N) := by ring
  have hr : (1 / (4 * κ) / (8 * Real.sqrt d)) / 16 =
      1 / (512 * κ * Real.sqrt d) := by ring
  rw [hl, hr]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem simplex_accuracy_threshold {d N : ℕ} (hd : 0 < d) (hN : 0 < N) (hdN : d ≤ 2 * N)
    {κ K : ℝ} (hκ : 0 < κ) (hK : 0 < K) (hκN : κ ≤ K * N) :
    (1 / (32 * K)) / ((N : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (N + 2))) ≤
      1 / (2 * (8 * κ * Real.sqrt ((d : ℝ) * Real.log (d + 2)))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdNR : (d : ℝ) ≤ 2 * N := by exact_mod_cast hdN
  have hln : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by linarith)
  have hld : 0 < Real.log (d + 2 : ℝ) := Real.log_pos (by linarith)
  have hl : Real.log (d + 2 : ℝ) ≤ 2 * Real.log (N + 2 : ℝ) :=
    (Real.log_le_log (by positivity) (by linarith : (d : ℝ) + 2 ≤ 2 * N + 2)).trans
      (log_twice_add_two hNR.le)
  have hprod : (d : ℝ) * Real.log (d + 2) ≤
      (2 * N : ℝ) * (2 * Real.log (N + 2)) :=
    mul_le_mul hdNR hl hld.le (by positivity)
  have hs : Real.sqrt ((d : ℝ) * Real.log (d + 2)) ≤
      2 * Real.sqrt (N : ℝ) * Real.sqrt (Real.log (N + 2)) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow, mul_pow, Real.sq_sqrt hNR.le, Real.sq_sqrt hln.le]
    nlinarith
  have htotal := mul_le_mul hκN hs (Real.sqrt_nonneg _) (by positivity : 0 ≤ K * N)
  rw [rpow_three_halves hNR]
  have heq : (1 / (32 * K)) /
      ((N : ℝ) * Real.sqrt N * Real.sqrt (Real.log (N + 2))) =
      1 / (32 * K * N * Real.sqrt N * Real.sqrt (Real.log (N + 2))) := by ring
  rw [heq]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem ball_accuracy_antitone {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {c : ℝ} (hc : 0 ≤ c) :
    c / (n : ℝ) ^ (3 / 2 : ℝ) ≤ c / (m : ℝ) ^ (3 / 2 : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  exact div_le_div_of_nonneg_left hc (by positivity)
    (Real.rpow_le_rpow hmR.le hmnR (by norm_num))

theorem simplex_accuracy_antitone {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {c : ℝ} (hc : 0 ≤ c) :
    c / ((n : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (n + 2))) ≤
      c / ((m : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Real.log (m + 2))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hlm : 0 < Real.log (m + 2 : ℝ) := Real.log_pos (by linarith)
  apply div_le_div_of_nonneg_left hc (by positivity)
  exact mul_le_mul (Real.rpow_le_rpow hmR.le hmnR (by norm_num))
    (Real.sqrt_le_sqrt (Real.log_le_log (by positivity) (by linarith)))
    (Real.sqrt_nonneg _) (Real.rpow_nonneg (hmR.le.trans hmnR) _)

end
end Matvec
