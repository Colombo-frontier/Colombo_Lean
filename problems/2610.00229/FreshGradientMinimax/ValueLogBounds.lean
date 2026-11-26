import FreshGradientMinimax.ValueCostBounds

/-! Uniform logarithmic bounds for the F.3 cutoff and estimator work.
Constants are explicit and deliberately loose. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax

def valueLogFactor (ℓ σ m e : ℝ) : ℝ :=
  1 + Real.log (2 + ℓ / m) + Real.log (2 + σ ^ 2 / (m * e))

theorem log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h

theorem valueLogFactor_bounds {ℓ σ m e : ℝ} (hℓ : 0 < ℓ) (hm : 0 < m) (he : 0 < e) :
    1 ≤ valueLogFactor ℓ σ m e ∧ Real.log (2 + ℓ / m) ≤ valueLogFactor ℓ σ m e ∧
      Real.log (2 + σ ^ 2 / (m * e)) ≤ valueLogFactor ℓ σ m e := by
  have h1 := Real.log_nonneg (show 1 ≤ 2 + ℓ / m by have := div_pos hℓ hm; linarith)
  have h2 := Real.log_nonneg (show 1 ≤ 2 + σ ^ 2 / (m * e) by
    have ht : 0 ≤ σ ^ 2 / (m * e) := by positivity
    linarith only [ht])
  dsimp [valueLogFactor]
  constructor
  · linarith
  constructor <;> linarith

theorem estimatorCutoff_valueLog_bound {ℓ σ m e : ℝ} (hℓ : 0 < ℓ) (hm : 0 < m) (he : 0 < e) :
    (estimatorCutoff epochRho m e σ + 1 : ℝ) ≤ 1000000000000000 * valueLogFactor ℓ σ m e := by
  have hL := valueLogFactor_bounds (σ := σ) hℓ hm he
  have hρ := epochRho_pos
  have ht : 0 ≤ σ ^ 2 / (m * e) := by positivity
  have hA : 0 ≤ 10 / epochRho := by positivity
  have heq : 10 * σ ^ 2 / (epochRho * m * e) = (10 / epochRho) * (σ ^ 2 / (m * e)) := by ring
  have hx : 2 + 10 * σ ^ 2 / (epochRho * m * e) ≤ (1 + 10 / epochRho) * (2 + σ ^ 2 / (m * e)) := by
    rw [heq]
    nlinarith only [ht, hA]
  have hlog := Real.log_le_log (by positivity : 0 < 2 + 10 * σ ^ 2 / (epochRho * m * e)) hx
  rw [Real.log_mul (by positivity) (by positivity)] at hlog
  have hconst : Real.log (1 + 10 / epochRho) ≤ 100000000000000 := by
    exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by norm_num [epochRho])
  have hupper : Real.log (2 + 10 * σ ^ 2 / (epochRho * m * e)) ≤
      100000000000000 + valueLogFactor ℓ σ m e := by linarith only [hlog, hconst, hL.2.2]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : Real.log (2 + 10 * σ ^ 2 / (epochRho * m * e)) / Real.log 2 ≤
      2 * (100000000000000 + valueLogFactor ℓ σ m e) := by
    apply (div_le_iff₀ hl2).mpr
    have hmul := mul_le_mul_of_nonneg_right log_two_bounds.1
      (by linarith [hL.1] : 0 ≤ 2 * (100000000000000 + valueLogFactor ℓ σ m e))
    nlinarith only [hupper, hmul]
  have hK := estimatorCutoff_log_bound (σ := σ) epochRho_pos hm he
  linarith only [hK, hdiv, hL.1]

theorem estimatorWork_valueLog_bound {ℓ α σ m e : ℝ}
    (hℓ : 0 < ℓ) (hα : 0 < α) (hfast : ℓ / 4 ≤ α) (hm : 0 < m) (he : 0 < e) :
    estimatorWork ℓ α epochRho m e σ ≤ 10 ^ 32 * valueLogFactor ℓ σ m e ^ 2 := by
  let K := estimatorCutoff epochRho m e σ
  let L := valueLogFactor ℓ σ m e
  have hL := valueLogFactor_bounds (σ := σ) hℓ hm he
  have hK := estimatorCutoff_valueLog_bound (σ := σ) hℓ hm he
  change (K + 1 : ℝ) ≤ 1000000000000000 * L at hK
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have h4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h
    exact h
  have hρ : Real.log (1 + 14 / epochRho) ≤ 100000000000000 :=
    (Real.log_le_sub_one_of_pos (by have := epochRho_pos; positivity)).trans (by norm_num [epochRho])
  have hKL : Real.log (K + 1 : ℝ) ≤ K := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos (show (0 : ℝ) < K + 1 by positivity)
  have hKlog := mul_le_mul_of_nonneg_left log_two_bounds.2 (show (0 : ℝ) ≤ 4 * K by positivity)
  have hbr : 2 + 4 * Real.log 4 + 4 * K * Real.log 2 + 4 * Real.log (1 + 14 / epochRho) +
      4 * Real.log (K + 1 : ℝ) + 8 * Real.log (2 + ℓ / m) ≤ 10000000000000000 * L := by
    linarith only [h4, hρ, hKL, hKlog, hK, hL.1, hL.2.1]
  have hb := mul_le_mul_of_nonneg_left hbr (show (0 : ℝ) ≤ 4 * (K + 1) by positivity)
  have hkm := mul_le_mul_of_nonneg_right hK (show 0 ≤ 4 * (10000000000000000 * L) by
    dsimp [L]; have := hL.1; positivity)
  have hw := multilevelWork_log_bound hℓ hα hfast epochRho_pos hm K
  change estimatorWork ℓ α epochRho m e σ ≤ _ at hw
  change _ ≤ 10 ^ 32 * L ^ 2
  nlinarith only [hw, hb, hkm, sq_nonneg L]

end FreshGradientMinimax
