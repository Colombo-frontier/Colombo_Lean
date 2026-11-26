import ScaleGrid254

noncomputable section
namespace Paper254

theorem logFactor_ge_one (T : ℕ) (hT : 0 < T) : 1 ≤ logFactor T := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hh := Real.log_nonneg (show (1 : ℝ) ≤ 2*T by linarith)
  unfold logFactor
  linarith

theorem log_horizon_le (T : ℕ) (hT : 0 < T) : Real.log T ≤ logFactor T := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hh := Real.log_le_log ht (show (T : ℝ) ≤ 2*T by linarith)
  unfold logFactor
  linarith

theorem scaleDepth_log_bound (T : ℕ) (hT : 0 < T) :
    (scaleCount T+1 : ℝ) ≤ 2*logFactor T := by
  have hp : (2 : ℝ)^(scaleCount T) ≤ T := by
    exact_mod_cast Nat.pow_log_le_self 2 (ne_of_gt hT)
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2^(scaleCount T)) hp
  rw [Real.log_pow] at hh
  have htwo : (1/2 : ℝ) ≤ Real.log 2 := by
    have hh := log_one_add_lower 1 (by norm_num)
    norm_num at hh
    exact hh
  have hk := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (scaleCount T) (α := ℝ))
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hlog := Real.log_le_log ht (show (T : ℝ) ≤ 2*T by linarith)
  unfold logFactor
  nlinarith

theorem masterOverhead_log_bound (T : ℕ) (hT : 0 < T) (lam : ℝ) (hlam : 0 < lam) :
    masterOverhead T (scaleCount T) lam ≤ 2*logFactor T/lam := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hk : (scaleCount T : ℝ) ≤ T := by exact_mod_cast Nat.log_le_self 2 T
  have hprod : (T+1 : ℝ)*(scaleCount T+1 : ℝ) ≤ (2*T)^2 := by
    have hh := mul_le_mul (show (T+1 : ℝ) ≤ 2*T by linarith)
      (show (scaleCount T+1 : ℝ) ≤ 2*T by linarith)
      (show (0 : ℝ) ≤ scaleCount T+1 by positivity) (show (0 : ℝ) ≤ 2*T by positivity)
    nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (T+1 : ℝ)*(scaleCount T+1 : ℝ)) hprod
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  unfold masterOverhead
  apply div_le_div_of_nonneg_right _ hlam.le
  unfold logFactor
  linarith

theorem birthBudget_log_bound (d T : ℕ) (hT : 0 < T) (D τ : ℝ) (hD : 0 < D)
    (hlo : D/T ≤ τ) (hhi : τ ≤ D) :
    birthBudget d D (τ^2) ≤ (d+1 : ℝ)*logFactor T := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hτ : 0 < τ := lt_of_lt_of_le (div_pos hD ht) hlo
  have hρ : τ^2/D^2 ≤ 1 := (div_le_one (sq_pos_of_pos hD)).mpr (by nlinarith)
  have hlogτ := Real.log_le_log (div_pos hD ht) hlo
  rw [Real.log_div (ne_of_gt hD) (ne_of_gt ht)] at hlogτ
  have hlogρ : -Real.log (τ^2/D^2) ≤ 2*Real.log T := by
    rw [Real.log_div (ne_of_gt (sq_pos_of_pos hτ)) (ne_of_gt (sq_pos_of_pos hD)),
      Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hterm : τ^2/D^2-1-Real.log (τ^2/D^2) ≤ 2*Real.log T := by linarith
  have hmul := mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg d (α := ℝ))
  have hlog := mul_le_mul_of_nonneg_left (log_horizon_le T hT) (Nat.cast_nonneg d (α := ℝ))
  have hL := logFactor_ge_one T hT
  unfold birthBudget
  nlinarith

end Paper254
#print axioms Paper254.scaleDepth_log_bound
#print axioms Paper254.masterOverhead_log_bound
#print axioms Paper254.birthBudget_log_bound
