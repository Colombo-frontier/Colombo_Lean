import LowRank.PowerBoostedRitz

/-! A fixed boost degree only shrinks the Chebyshev gap by a constant.
The weighted error retains a valid cutoff both near and far above the tail. -/

namespace LowRank
noncomputable section

def powerBoostedGap (δ : ℝ) (u : ℕ) : ℝ := δ / (2 : ℝ) ^ (2 * u)

theorem powerBoostedGap_pos {δ : ℝ} (hδ : 0 < δ) (u : ℕ) : 0 < powerBoostedGap δ u := by
  unfold powerBoostedGap
  positivity

theorem powerBoostedGap_le_one {δ : ℝ} (hδ : δ ≤ 1) (u : ℕ) : powerBoostedGap δ u ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ (2 * u))).mpr
  exact hδ.trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

theorem powerBoostedGap_cutoff {δ L α : ℝ} (u : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L) (hα : L ≤ α) :
    min (α - (δ / 2) * L * (L / α) ^ (2 * u)) L * (1 + powerBoostedGap δ u / 2) ≤ α := by
  have hα0 : 0 < α := hL.trans_le hα
  have hγ := powerBoostedGap_pos hδ u
  have hγ1 := powerBoostedGap_le_one hδ1 u
  by_cases hnear : α ≤ 2 * L
  · have hratio : (1 : ℝ) / 2 ≤ L / α := (le_div_iff₀ hα0).mpr (by linarith)
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hratio (2 * u)
    have he : (powerBoostedGap δ u / 2) * L ≤ (δ / 2) * L * (L / α) ^ (2 * u) := by
      have h := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (δ / 2) * L)
      have hid : (powerBoostedGap δ u / 2) * L = (δ / 2) * L * ((1 : ℝ) / 2) ^ (2 * u) := by
        norm_num [powerBoostedGap, div_pow, div_eq_mul_inv, inv_pow] <;> ring
      rwa [← hid] at h
    have h := min_cutoff_gap (t := α - (δ / 2) * L * (L / α) ^ (2 * u)) (L := L) hγ.le
    linarith
  · calc
      _ ≤ L * (1 + powerBoostedGap δ u / 2) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
      _ ≤ L * (1 + (1 : ℝ) / 2) := mul_le_mul_of_nonneg_left (by linarith) hL.le
      _ ≤ α := by linarith

theorem powerBoostedTolerance_budget {η C L α δ : ℝ} {s m : ℕ} (u : ℕ)
    (hL : 0 ≤ L) (hα : 0 ≤ α) (hbudget : η ^ 2 * (C * (s : ℝ) * (m : ℝ)) ≤ δ / 2) :
    (η * (L / α) ^ u) ^ 2 * (C * (s : ℝ) * (m : ℝ)) * L ≤
      (δ / 2) * L * (L / α) ^ (2 * u) := by
  have hp : (L / α) ^ (2 * u) = ((L / α) ^ u) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hp]
  calc
    _ = (η ^ 2 * (C * (s : ℝ) * (m : ℝ))) * (L * ((L / α) ^ u) ^ 2) := by ring
    _ ≤ (δ / 2) * (L * ((L / α) ^ u) ^ 2) :=
      mul_le_mul_of_nonneg_right hbudget (mul_nonneg hL (sq_nonneg _))
    _ = _ := by ring

end
end LowRank
