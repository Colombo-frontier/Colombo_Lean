import FreshGradientMinimax.AcceleratedPhysicalParameters

/-! The actual integer choices in E.4, with uniform thresholds and
quantitative floor bounds needed by the dimension-free rate. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def acceleratedConditionThreshold : ℝ := 1600 * acceleratedSmoothnessConstant
def acceleratedGapThreshold : ℝ := 4000 * acceleratedValueCoefficient

theorem acceleratedConditionThreshold_pos : 0 < acceleratedConditionThreshold :=
  mul_pos (by norm_num) acceleratedSmoothnessConstant_pos

theorem acceleratedGapThreshold_pos : 0 < acceleratedGapThreshold :=
  mul_pos (by norm_num) acceleratedValueCoefficient_pos

theorem accelerated_chain_count_exists (p : Parameters) (hκ : acceleratedConditionThreshold ≤ p.κ) :
    ∃ n : ℕ, 10 ≤ n + 2 ∧ n + 2 = ⌊Real.sqrt (p.κ / (4 * acceleratedSmoothnessConstant))⌋₊ ∧
      (n + 2 : ℝ) ^ 2 ≤ p.L / (4 * acceleratedSmoothnessConstant * p.μ) ∧
      Real.sqrt p.κ / (4 * Real.sqrt acceleratedSmoothnessConstant) ≤ (n + 2 : ℝ) := by
  let t := Real.sqrt (p.κ / (4 * acceleratedSmoothnessConstant))
  have hA := acceleratedSmoothnessConstant_pos
  have hq : (400 : ℝ) ≤ p.κ / (4 * acceleratedSmoothnessConstant) := by
    apply (le_div_iff₀ (by positivity)).mpr
    change 1600 * acceleratedSmoothnessConstant ≤ p.κ at hκ
    nlinarith only [hκ]
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = p.κ / (4 * acceleratedSmoothnessConstant) :=
    Real.sq_sqrt (by linarith only [hq])
  have ht : 20 ≤ t := by nlinarith only [ht0, ht2, hq]
  have hN : 20 ≤ ⌊t⌋₊ := Nat.le_floor ht
  let n := ⌊t⌋₊ - 2
  have hn : n + 2 = ⌊t⌋₊ := by dsimp only [n]; omega
  refine ⟨n, by omega, hn, ?_, ?_⟩
  · have hfloor := Nat.floor_le ht0
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg ⌊t⌋₊) hfloor 2
    rw [ht2] at hsq
    have he : p.κ / (4 * acceleratedSmoothnessConstant) = p.L / (4 * acceleratedSmoothnessConstant * p.μ) := by
      unfold Parameters.κ
      ring
    rw [he] at hsq
    convert hsq using 1
    congr 1
    exact_mod_cast hn
  · have hfloor := Nat.lt_floor_add_one t
    have hl : t / 2 ≤ (⌊t⌋₊ : ℝ) := by linarith only [hfloor, ht]
    have he : Real.sqrt p.κ / (4 * Real.sqrt acceleratedSmoothnessConstant) = t / 2 := by
      dsimp only [t]
      rw [Real.sqrt_div (le_trans (by norm_num) p.condition_ge_one), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring
    rw [he]
    convert hl using 1
    exact_mod_cast hn

theorem accelerated_stage_count_exists {lam Δ : ℝ} (hlam : 0 < lam) (hΔ : 4000 * lam ≤ Δ) :
    ∃ k : ℕ, 0 < k ∧ k + 1 = ⌊Δ / (1000 * lam)⌋₊ ∧
      1000 * (k + 1 : ℕ) * lam ≤ Δ ∧ Δ / (2000 * lam) ≤ (k : ℝ) := by
  have hq : (4 : ℝ) ≤ Δ / (1000 * lam) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hΔ])
  have hT : 4 ≤ ⌊Δ / (1000 * lam)⌋₊ := Nat.le_floor hq
  let k := ⌊Δ / (1000 * lam)⌋₊ - 1
  have hk : k + 1 = ⌊Δ / (1000 * lam)⌋₊ := by dsimp only [k]; omega
  refine ⟨k, by dsimp only [k]; omega, hk, ?_, ?_⟩
  · have hf := Nat.floor_le (show 0 ≤ Δ / (1000 * lam) by linarith only [hq])
    rw [← hk] at hf
    have h := (le_div_iff₀ (by positivity : 0 < 1000 * lam)).mp hf
    nlinarith only [h]
  · have hf := Nat.lt_floor_add_one (Δ / (1000 * lam))
    rw [← hk] at hf
    push_cast at hf
    have he : Δ / (2000 * lam) = (Δ / (1000 * lam)) / 2 := by ring
    rw [he]
    linarith only [hf, hq]

theorem accelerated_gap_threshold_scale (p : Parameters)
    (hgap : acceleratedGapThreshold * p.ε ^ 2 ≤ p.L * p.gap) :
    4000 * acceleratedValueScale p.L p.ε ≤ p.gap := by
  rw [acceleratedValueScale_coefficient]
  have he : 4000 * (acceleratedValueCoefficient * p.ε ^ 2 / p.L) = acceleratedGapThreshold * p.ε ^ 2 / p.L := by
    unfold acceleratedGapThreshold
    ring
  rw [he]
  exact (div_le_iff₀ (p.μ_pos.trans_le p.μ_le_L)).mpr (by simpa only [mul_comm] using hgap)

end FreshGradientMinimax
