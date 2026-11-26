import FreshGradientMinimax.RelativeEstimator
import FreshGradientMinimax.CostedMultilevel

/-! Exact scheduled level work and a distance-independent bound for its
expectation. The tags count minibatch draws in the construction. The
standalone estimator's original-query implementation is now proved in
EstimatorImplementation; composition inside the full solver remains. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def levelWork (ℓ α γ m : ℝ) (j : ℕ) : ℕ :=
  (levelSteps ℓ α γ m (2 ^ j) + 1) * 2 ^ j

def multilevelWork (ℓ α γ m : ℝ) (K : ℕ) : ℝ :=
  (levelWork ℓ α γ m 0 : ℝ) + ∑ j ∈ Finset.range K, levelProbability K j *
    ((levelWork ℓ α γ m (j + 1) : ℝ) + levelWork ℓ α γ m j)

theorem levelSteps_dyadic_mono {ℓ α γ m : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (hγ : 0 < γ) (hm : 0 < m) {j K : ℕ} (hj : j ≤ K) :
    levelSteps ℓ α γ m (2 ^ j) ≤ levelSteps ℓ α γ m (2 ^ K) := by
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hℓ.le hα.le)
  apply Real.log_le_log (by positivity)
  have hpow : ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hj
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity)

theorem level_probability_times_batch {K : ℕ} (hK : 0 < K) (j : ℕ) :
    levelProbability K j * (2 : ℝ) ^ (j + 1) ≤ 2 := by
  have hh : (1 / 2 : ℝ) ^ K ≤ 1 / 2 := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hK
      _ = _ := pow_one _
  have he : levelProbability K j * (2 : ℝ) ^ (j + 1) = 1 / (1 - (1 / 2 : ℝ) ^ K) := by
    rw [levelProbability, div_mul_eq_mul_div]
    have hc : (1 / 2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (j + 1) = 1 := by
      rw [one_div, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))]
    rw [hc]
  rw [he]
  apply (div_le_iff₀ (level_normalizer_pos hK)).mpr
  linarith

theorem multilevelWork_bound {ℓ α γ m : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (hγ : 0 < γ) (hm : 0 < m) (K : ℕ) :
    multilevelWork ℓ α γ m K ≤
      4 * (K + 1 : ℝ) * ((levelSteps ℓ α γ m (2 ^ K) : ℝ) + 1) := by
  let N : ℝ := (levelSteps ℓ α γ m (2 ^ K) : ℝ) + 1
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hlevel (j : ℕ) (hj : j ≤ K) : (levelWork ℓ α γ m j : ℝ) ≤ N * (2 : ℝ) ^ j := by
    have hstep : (levelSteps ℓ α γ m (2 ^ j) : ℝ) ≤ levelSteps ℓ α γ m (2 ^ K) :=
      Nat.cast_le.mpr (levelSteps_dyadic_mono hℓ hα hγ hm hj)
    simp only [levelWork, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (by positivity)
  have h0 := hlevel 0 (Nat.zero_le K)
  simp only [pow_zero, mul_one] at h0
  by_cases hK : K = 0
  · simp only [multilevelWork, hK, Finset.range_zero, Finset.sum_empty, add_zero, Nat.cast_zero,
      zero_add, mul_one]
    dsimp [N] at h0 hN
    rw [hK] at h0 hN
    linarith
  · have hKpos := Nat.pos_of_ne_zero hK
    have hw (j : ℕ) (hj : j < K) :
        levelProbability K j * ((levelWork ℓ α γ m (j + 1) : ℝ) + levelWork ℓ α γ m j) ≤ 4 * N := by
      have h1 := hlevel (j + 1) (Nat.succ_le_of_lt hj)
      have h2 := hlevel j (Nat.le_of_lt hj)
      have hp := (level_probability_pos hKpos j).le
      have hbatch := level_probability_times_batch hKpos j
      have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (j + 1) := by
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j]
      have hbatch' : levelProbability K j * (2 : ℝ) ^ j ≤ 2 :=
        (mul_le_mul_of_nonneg_left hpow hp).trans hbatch
      have hcost := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hp
      have hc1 := mul_le_mul_of_nonneg_left hbatch hN
      have hc2 := mul_le_mul_of_nonneg_left hbatch' hN
      nlinarith only [hcost, hc1, hc2]
    calc
      multilevelWork ℓ α γ m K ≤ N + ∑ j ∈ Finset.range K, 4 * N :=
        add_le_add h0 (Finset.sum_le_sum (fun j hj => hw j (Finset.mem_range.mp hj)))
      _ = N + (K : ℝ) * (4 * N) := by simp
      _ ≤ 4 * (K + 1 : ℝ) * N := by nlinarith

theorem levelSteps_log_bound {ℓ α γ m : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (hfast : ℓ / 4 ≤ α) (hγ : 0 < γ) (hm : 0 < m) (K : ℕ) :
    (levelSteps ℓ α γ m (2 ^ K) : ℝ) + 1 ≤
      2 + 4 * Real.log 4 + 4 * K * Real.log 2 + 4 * Real.log (1 + ℓ ^ 2 / (γ * m ^ 2)) := by
  let R : ℝ := 4 * ((2 ^ K : ℕ) : ℝ) * (1 + ℓ ^ 2 / (γ * m ^ 2))
  have hb : (1 : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_pow K 2 (by decide))
  have hr : 0 ≤ ℓ ^ 2 / (γ * m ^ 2) := by positivity
  have hR : 1 ≤ R := by dsimp [R]; nlinarith
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (div_nonneg hℓ.le hα.le) hlog)).le
  have hratio : ℓ / α ≤ 4 := (div_le_iff₀ hα).mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hratio hlog
  have he : Real.log R = Real.log 4 + K * Real.log 2 + Real.log (1 + ℓ ^ 2 / (γ * m ^ 2)) := by
    dsimp [R]
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  change (levelSteps ℓ α γ m (2 ^ K) : ℝ) ≤ ℓ / α * Real.log R + 1 at hceil
  rw [he] at hceil hmul
  linarith

theorem estimatorGamma_log_bound {ℓ ρ m : ℝ} (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hm : 0 < m) (K : ℕ) :
    Real.log (1 + ℓ ^ 2 / (estimatorGamma ρ K * m ^ 2)) ≤
      Real.log (1 + 14 / ρ) + Real.log (K + 1 : ℝ) + 2 * Real.log (2 + ℓ / m) := by
  have ht : 0 ≤ 14 / ρ := by positivity
  have hr : 0 ≤ ℓ / m := (div_pos hℓ hm).le
  have hN : (1 : ℝ) ≤ K + 1 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  have hsq : 1 ≤ (2 + ℓ / m) ^ 2 := by nlinarith
  have h1 : 1 ≤ (K + 1 : ℝ) * (2 + ℓ / m) ^ 2 :=
    hsq.trans (le_mul_of_one_le_left (sq_nonneg _) hN)
  have h2 : (14 / ρ) * (K + 1 : ℝ) * (ℓ / m) ^ 2 ≤
      (14 / ρ) * (K + 1 : ℝ) * (2 + ℓ / m) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have heq : ℓ ^ 2 / (estimatorGamma ρ K * m ^ 2) = (14 / ρ) * (K + 1 : ℝ) * (ℓ / m) ^ 2 := by
    unfold estimatorGamma
    field_simp
    ring
  have hbound : 1 + ℓ ^ 2 / (estimatorGamma ρ K * m ^ 2) ≤
      (1 + 14 / ρ) * (K + 1 : ℝ) * (2 + ℓ / m) ^ 2 := by
    rw [heq]
    nlinarith only [h1, h2]
  have hlog := Real.log_le_log (by rw [heq]; positivity) hbound
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at hlog
  exact hlog

/-- An explicit version of (44); all coefficients are universal when ρ is fixed. -/
theorem multilevelWork_log_bound {ℓ α ρ m : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α)
    (hfast : ℓ / 4 ≤ α) (hρ : 0 < ρ) (hm : 0 < m) (K : ℕ) :
    multilevelWork ℓ α (estimatorGamma ρ K) m K ≤
      4 * (K + 1 : ℝ) * (2 + 4 * Real.log 4 + 4 * K * Real.log 2 +
        4 * Real.log (1 + 14 / ρ) + 4 * Real.log (K + 1 : ℝ) + 8 * Real.log (2 + ℓ / m)) := by
  have hw := multilevelWork_bound hℓ hα (estimatorGamma_pos hρ K) hm K
  have hn := levelSteps_log_bound hℓ hα hfast (estimatorGamma_pos hρ K) hm K
  have hg := estimatorGamma_log_bound hℓ hρ hm K
  exact hw.trans (mul_le_mul_of_nonneg_left (by linarith only [hn, hg]) (by positivity))

theorem estimatorCutoff_log_bound {ρ m e σ : ℝ} (hρ : 0 < ρ) (hm : 0 < m) (he : 0 < e) :
    (estimatorCutoff ρ m e σ : ℝ) ≤ 2 + Real.log (2 + 10 * σ ^ 2 / (ρ * m * e)) / Real.log 2 := by
  let R := 10 * σ ^ 2 / (ρ * m * e)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0 ≤ Real.log (2 + R) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hl2.le
  by_cases hσ : σ = 0
  · simp only [estimatorCutoff, if_pos hσ, Nat.cast_zero]
    change 0 ≤ 2 + Real.log (2 + R) / Real.log 2
    linarith
  · have hRpos : 0 < R := by dsimp [R]; positivity
    have hceil : ⌈Real.log R / Real.log 2⌉₊ ≤ ⌈Real.log (2 + R) / Real.log 2⌉₊ :=
      Nat.ceil_mono (div_le_div_of_nonneg_right (Real.log_le_log hRpos (by linarith)) hl2.le)
    have hK : estimatorCutoff ρ m e σ ≤ 1 + ⌈Real.log (2 + R) / Real.log 2⌉₊ := by
      rw [estimatorCutoff, if_neg hσ]
      change max 1 ⌈Real.log R / Real.log 2⌉₊ ≤ _
      omega
    have hKR := (Nat.cast_le (α := ℝ)).mpr hK
    have hb := Nat.ceil_lt_add_one hl
    simp only [Nat.cast_add, Nat.cast_one] at hKR
    change (estimatorCutoff ρ m e σ : ℝ) ≤ 2 + Real.log (2 + R) / Real.log 2
    linarith

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def costedRelativeEstimatorKernel (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (v a : Euclid dy) : Kernel (Euclid dx) (Euclid dy × ℕ) :=
  costedMultilevelKernel (fun j => S.levelKernel O (2 ^ j)
    (levelSteps ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m (2 ^ j)) v a)
    (levelWork ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m) (estimatorCutoff ρ m e σ)

instance costedRelativeEstimatorKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (v a : Euclid dy) : IsMarkovKernel (S.costedRelativeEstimatorKernel O ρ m e v a) := by
  unfold costedRelativeEstimatorKernel
  infer_instance

theorem costedRelativeEstimatorKernel_first (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (v a : Euclid dy) :
    (S.costedRelativeEstimatorKernel O ρ m e v a).map Prod.fst = S.relativeEstimatorKernel O ρ m e v a :=
  costedMultilevelKernel_first _ _ _

theorem costedRelativeEstimatorKernel_mean_cost (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (v a : Euclid dy) (u : Euclid dx) :
    (∫ z, (z.2 : ℝ) ∂S.costedRelativeEstimatorKernel O ρ m e v a u) =
      multilevelWork ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m (estimatorCutoff ρ m e σ) :=
  costedMultilevelKernel_mean_cost _ _ _ _

/-- The actual tagged estimator obeys the explicit distance-independent work bound. -/
theorem costedRelativeEstimatorKernel_work_bound (O : FreshOracle S.toNCObjective σ)
    (hfast : ℓ / 4 ≤ α) {ρ m e : ℝ} (hρ : 0 < ρ) (hm : 0 < m)
    (v a : Euclid dy) (u : Euclid dx) :
    (∫ z, (z.2 : ℝ) ∂S.costedRelativeEstimatorKernel O ρ m e v a u) ≤
      4 * (estimatorCutoff ρ m e σ + 1 : ℝ) *
        (2 + 4 * Real.log 4 + 4 * estimatorCutoff ρ m e σ * Real.log 2 +
          4 * Real.log (1 + 14 / ρ) + 4 * Real.log (estimatorCutoff ρ m e σ + 1 : ℝ) +
          8 * Real.log (2 + ℓ / m)) := by
  rw [S.costedRelativeEstimatorKernel_mean_cost]
  exact multilevelWork_log_bound S.toNCObjective.L_pos S.α_pos hfast hρ hm _

end SCObjective
end FreshGradientMinimax
