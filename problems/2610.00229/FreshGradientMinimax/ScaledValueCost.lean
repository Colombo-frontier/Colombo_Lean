import FreshGradientMinimax.ValueLogBounds

/-! Scaling the explicit work coefficients into the condition-number and
statistical terms of F.3. -/

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section
namespace FreshGradientMinimax

theorem epochSteps_scaled {m H : ℝ} (hm : 0 < m) (hmH : m ≤ H) :
    (epochSteps m H : ℝ) * Real.sqrt (m / H) ≤ 10 ^ 9 := by
  have hH := hm.trans_le hmH
  have ha : 0 < Real.sqrt (m / H) := Real.sqrt_pos.mpr (div_pos hm hH)
  have ha1 := (acceleration_parameter hm hmH).2.1
  have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 10000000 * 17)
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10000000 * 17)
  have hc := Nat.ceil_lt_add_one (mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 3) ha.le) hlog)
  change (epochSteps m H : ℝ) < (3 / Real.sqrt (m / H)) * Real.log (10000000 * 17) + 1 at hc
  have hmul := mul_le_mul_of_nonneg_right hc.le ha.le
  have heq : ((3 / Real.sqrt (m / H)) * Real.log (10000000 * 17) + 1) * Real.sqrt (m / H) =
      3 * Real.log (10000000 * 17) + Real.sqrt (m / H) := by field_simp; ring
  rw [heq] at hmul
  norm_num at hl ⊢
  linarith only [hmul, hl, ha1]

theorem refreshSteps_constant {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (hfast : ℓ / 4 ≤ α) :
    (refreshSteps ℓ α : ℝ) ≤ 4000000 := by
  have hratio : ℓ / α ≤ 4 := (div_le_iff₀ hα).mpr (by linarith)
  have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 1000000)
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1000000)
  have hc := Nat.ceil_lt_add_one (mul_nonneg (div_nonneg hℓ.le hα.le) hlog)
  have ht := mul_le_mul_of_nonneg_right hratio hlog
  change (refreshSteps ℓ α : ℝ) < ℓ / α * Real.log 1000000 + 1 at hc
  norm_num at hl
  linarith only [hc, ht, hl]

theorem sqrt_ratio_inverse {m H : ℝ} (hm : 0 < m) (hH : 0 < H) :
    (Real.sqrt (m / H))⁻¹ = Real.sqrt (H / m) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [inv_pow, Real.sq_sqrt (div_nonneg hm.le hH.le), Real.sq_sqrt (div_nonneg hH.le hm.le)]
  simp only [inv_div]

theorem sqrt_ratio_product {m H : ℝ} (hm : 0 < m) (hH : 0 < H) :
    Real.sqrt (m / H) * Real.sqrt (m * H) = m := by
  apply (sq_eq_sq₀ (by positivity) hm.le).mp
  rw [mul_pow, Real.sq_sqrt (div_nonneg hm.le hH.le), Real.sq_sqrt (mul_nonneg hm.le hH.le)]
  field_simp
  ring

theorem epochSteps_condition_bound {m H : ℝ} (hm : 0 < m) (hmH : m ≤ H) :
    (epochSteps m H : ℝ) ≤ 10 ^ 9 * Real.sqrt (H / m) := by
  have ha : 0 < Real.sqrt (m / H) := Real.sqrt_pos.mpr (div_pos hm (hm.trans_le hmH))
  have h := (le_div_iff₀ ha).mpr (epochSteps_scaled hm hmH)
  change (epochSteps m H : ℝ) ≤ 10 ^ 9 * (Real.sqrt (m / H))⁻¹ at h
  rw [sqrt_ratio_inverse hm (hm.trans_le hmH)] at h
  exact h

theorem epochSteps_noise_bound {m H : ℝ} (hm : 0 < m) (hmH : m ≤ H) :
    (epochSteps m H : ℝ) / Real.sqrt (m * H) ≤ 10 ^ 9 / m := by
  have hH := hm.trans_le hmH
  have hs : 0 < Real.sqrt (m * H) := Real.sqrt_pos.mpr (mul_pos hm hH)
  apply (div_le_div_iff₀ hs hm).mpr
  calc
    _ = ((epochSteps m H : ℝ) * Real.sqrt (m / H)) * Real.sqrt (m * H) := by
      rw [mul_assoc, sqrt_ratio_product hm hH]
    _ ≤ _ := mul_le_mul_of_nonneg_right (epochSteps_scaled hm hmH) hs.le

theorem refresh_scale_bound {ℓ α m : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (hfast : ℓ / 4 ≤ α) (hm : 0 < m) (hmℓ : m ≤ 20 * ℓ) : m ^ 2 / (α * ℓ) ≤ 1600 := by
  apply (div_le_iff₀ (mul_pos hα hℓ)).mpr
  have hs := mul_self_le_mul_self hm.le hmℓ
  have hl := mul_le_mul_of_nonneg_right hfast hℓ.le
  nlinarith only [hs, hl]

theorem epochBaseWork_valueLog_bound {ℓ α σ m H e : ℝ}
    (hℓ : 0 < ℓ) (hα : 0 < α) (hfast : ℓ / 4 ≤ α) (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e) :
    epochBaseWork ℓ α σ m H e ≤ 10 ^ 42 * valueLogFactor ℓ σ m e ^ 2 * Real.sqrt (H / m) := by
  have hW := estimatorWork_valueLog_bound (σ := σ) hℓ hα hfast hm he
  have hW0 := estimatorWork_nonneg ℓ α epochRho m e σ
  have hN := epochSteps_condition_bound hm hmH
  have hF := refreshSteps_constant hℓ hα hfast
  have hL := (valueLogFactor_bounds (σ := σ) hℓ hm he).1
  have hroot : 1 ≤ Real.sqrt (H / m) := Real.one_le_sqrt.mpr ((le_div_iff₀ hm).mpr (by simpa using hmH))
  have hL2 : 1 ≤ valueLogFactor ℓ σ m e ^ 2 := by nlinarith only [hL]
  have hprod : 1 ≤ valueLogFactor ℓ σ m e ^ 2 * Real.sqrt (H / m) :=
    one_le_mul_of_one_le_of_one_le hL2 hroot
  have hb := mul_le_mul hN hW hW0 (by positivity : 0 ≤ 10 ^ 9 * Real.sqrt (H / m))
  dsimp [epochBaseWork]
  nlinarith only [hb, hF, hprod]

theorem epochNoiseWork_valueLog_bound {ℓ α σ m H e : ℝ}
    (hℓ : 0 < ℓ) (hα : 0 < α) (hfast : ℓ / 4 ≤ α) (hm : 0 < m) (hmH : m ≤ H)
    (hmℓ : m ≤ 20 * ℓ) (he : 0 < e) :
    epochNoiseWork ℓ α σ m H e ≤ 10 ^ 68 * valueLogFactor ℓ σ m e ^ 3 * σ ^ 2 / m := by
  let L := valueLogFactor ℓ σ m e
  let W := estimatorWork ℓ α epochRho m e σ
  let K := estimatorCutoff epochRho m e σ
  have hL := (valueLogFactor_bounds (σ := σ) hℓ hm he).1
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hW := estimatorWork_valueLog_bound (σ := σ) hℓ hα hfast hm he
  have hW0 := estimatorWork_nonneg ℓ α epochRho m e σ
  have hK := estimatorCutoff_valueLog_bound (σ := σ) hℓ hm he
  have hWK : W * (K + 1 : ℝ) ≤ 10 ^ 47 * L ^ 3 := by
    have h := mul_le_mul hW hK (by positivity : (0 : ℝ) ≤ K + 1) (by positivity : 0 ≤ 10 ^ 32 * L ^ 2)
    nlinarith only [h]
  have hN := epochSteps_noise_bound hm hmH
  have hA := mul_le_mul hN hWK (mul_nonneg hW0 (by positivity)) (by positivity : 0 ≤ 10 ^ 9 / m)
  have hA' := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ 238000000000 * σ ^ 2)
  have hF := refreshSteps_constant hℓ hα hfast
  have hS := refresh_scale_bound hℓ hα hfast hm hmℓ
  have hFS := mul_le_mul hF hS (by positivity : 0 ≤ m ^ 2 / (α * ℓ)) (by norm_num : (0 : ℝ) ≤ 4000000)
  have hF' := mul_le_mul_of_nonneg_right hFS (by positivity : 0 ≤ 1000000 * σ ^ 2 / m)
  have hstat : 0 ≤ σ ^ 2 / m := by positivity
  have hLstat := mul_le_mul_of_nonneg_right hL3 hstat
  have heq : epochNoiseWork ℓ α σ m H e =
      ((epochSteps m H : ℝ) / Real.sqrt (m * H) * (W * (K + 1 : ℝ))) * (238000000000 * σ ^ 2) +
      ((refreshSteps ℓ α : ℝ) * (m ^ 2 / (α * ℓ))) * (1000000 * σ ^ 2 / m) := by
    dsimp [epochNoiseWork, W, K]
    field_simp
    ring
  rw [heq]
  change _ ≤ 10 ^ 68 * L ^ 3 * σ ^ 2 / m
  have haform : ((10 ^ 9 / m) * (10 ^ 47 * L ^ 3)) * (238000000000 * σ ^ 2) =
      (238 * 10 ^ 65) * L ^ 3 * (σ ^ 2 / m) := by ring
  have hfform : (4000000 * 1600) * (1000000 * σ ^ 2 / m) = 6400000000000000 * (σ ^ 2 / m) := by ring
  rw [haform] at hA'
  rw [hfform] at hF'
  calc
    _ ≤ 10 ^ 68 * L ^ 3 * (σ ^ 2 / m) := by nlinarith only [hA', hF', hLstat, hstat]
    _ = _ := by ring

end FreshGradientMinimax
