import FreshGradientMinimax.SCSCStageBounds

/-! Equation (51) for the actual SCSC program at a fixed base objective.
The universal constant is explicit; the eighth power is the paper's
deliberately loose logarithmic envelope. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem scsc_rate_envelope {L R T U a b r v : ℝ} (hL : 1 ≤ L)
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hU : 0 ≤ U) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hr0 : 0 ≤ r) (hv0 : 0 ≤ v)
    (ha : a ≤ 10000000 * L) (hb : b ≤ 100000000 * L * T)
    (hr : r ≤ 4 * R) (hv : v ≤ 400000000 * L ^ 2 * U) :
    10 ^ 70 * a ^ 3 * (r * b + v) ≤ 10 ^ 100 * L ^ 5 * (R * T + U) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hpow := pow_le_pow_left₀ ha0 ha 3
  have hprod := mul_le_mul hr hb hb0 (by positivity : 0 ≤ 4 * R)
  have hLsq : L ≤ L ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right hL hL0]
  have hdet := mul_le_mul_of_nonneg_right hLsq (by positivity : 0 ≤ 400000000 * R * T)
  have hinner : r * b + v ≤ 400000000 * L ^ 2 * (R * T + U) := by nlinarith only [hprod, hv, hdet]
  calc
    _ ≤ 10 ^ 70 * (10000000 * L) ^ 3 * (400000000 * L ^ 2 * (R * T + U)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hinner (by positivity) (by positivity)
    _ = (4 * 10 ^ 99) * (L ^ 5 * (R * T + U)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num : (4 * 10 ^ 99 : ℝ) ≤ 10 ^ 100) (by positivity)
    _ = _ := by ring

theorem scscStageWork_bound {ℓ α σ μ η E₀ : ℝ}
    (hμ : 0 < μ) (hμℓ : μ ≤ ℓ) (hα : 0 < α) (hfast : ℓ / 4 ≤ α) (hη : 0 < η) (hE : 0 ≤ E₀)
    {j : ℕ} (hj : j ≤ recursiveLastIndex (5 * ℓ) μ) :
    recursiveStageWork ℓ α σ μ (scscGradientTolerance μ η) (recursiveLastIndex (5 * ℓ) μ) (3 * (ℓ / μ) * E₀) j ≤
      10 ^ 100 * valueLogFactor ℓ σ μ η ^ 5 *
        (Real.sqrt (ℓ / μ) * Real.log (2 + (ℓ / μ) * E₀ / η) + σ ^ 2 / (μ * η)) := by
  have hℓ := hμ.trans_le hμℓ
  have hδ := scscGradientTolerance_pos hμ hη
  have hE' : 0 ≤ 3 * (ℓ / μ) * E₀ := by positivity
  have he := recursiveAccuracy_pos hμ hδ (recursiveLastIndex (5 * ℓ) μ) j
  have hm := recursiveMass_pos hμ j
  have henv := recursiveInputEnvelope_nonneg hμ hδ hE' (recursiveLastIndex (5 * ℓ) μ) j
  have h := recursiveStageWork_rate (σ := σ) hℓ hα hfast hμ hμℓ hδ hE' hj
  apply h.trans
  apply scsc_rate_envelope (valueLogFactor_bounds hℓ hμ hη).1 (Real.sqrt_nonneg _)
  · apply Real.log_nonneg
    have ht : 0 ≤ (ℓ / μ) * E₀ / η := by positivity
    linarith only [ht]
  · positivity
  · exact le_trans (by norm_num) (valueLogFactor_bounds hℓ (recursiveMass_pos hμ j) he).1
  · apply Real.log_nonneg
    have ht := div_nonneg henv he.le
    linarith only [ht]
  · exact Real.sqrt_nonneg _
  · positivity
  · exact scsc_stage_log_bound hμ hμℓ hη j
  · exact scsc_stage_initialization_bound hμ hμℓ hη hE j
  · exact scsc_stage_sqrt_bound hμ hμℓ hj
  · exact scsc_stage_noise_bound hμ hμℓ hη j

theorem scscSolverWork_rate {ℓ α σ μ η E₀ : ℝ}
    (hμ : 0 < μ) (hμℓ : μ ≤ ℓ) (hα : 0 < α) (hfast : ℓ / 4 ≤ α) (hη : 0 < η) (hE : 0 ≤ E₀) :
    scscSolverWork ℓ α σ μ η E₀ ≤ 10 ^ 110 * valueLogFactor ℓ σ μ η ^ 8 *
      (Real.sqrt (ℓ / μ) * Real.log (2 + (ℓ / μ) * E₀ / η) + σ ^ 2 / (μ * η)) := by
  let L := valueLogFactor ℓ σ μ η
  let B := Real.sqrt (ℓ / μ) * Real.log (2 + (ℓ / μ) * E₀ / η) + σ ^ 2 / (μ * η)
  have hℓ := hμ.trans_le hμℓ
  have hL : 1 ≤ L := (valueLogFactor_bounds (σ := σ) hℓ hμ hη).1
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hB : 0 ≤ B := by
    apply add_nonneg
    · apply mul_nonneg (Real.sqrt_nonneg _)
      apply Real.log_nonneg
      have ht : 0 ≤ (ℓ / μ) * E₀ / η := by positivity
      linarith only [ht]
    · positivity
  have hsum : scscSolverWork ℓ α σ μ η E₀ ≤ scscStageCount ℓ μ * (10 ^ 100 * L ^ 5 * B) := by
    unfold scscSolverWork
    calc
      _ ≤ ∑ j ∈ Finset.range (recursiveLastIndex (5 * ℓ) μ + 1), 10 ^ 100 * L ^ 5 * B := by
        apply Finset.sum_le_sum
        intro j hj
        exact scscStageWork_bound hμ hμℓ hα hfast hη hE (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, scscStageCount]
  have hcount : scscStageCount ℓ μ ≤ 20 * L := scscStageCount_log_bound hμ hμℓ hη
  have hpow : L ^ 6 ≤ L ^ 8 := pow_le_pow_right₀ hL (by decide)
  change _ ≤ 10 ^ 110 * L ^ 8 * B
  calc
    _ ≤ scscStageCount ℓ μ * (10 ^ 100 * L ^ 5 * B) := hsum
    _ ≤ (20 * L) * (10 ^ 100 * L ^ 5 * B) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (20 * 10 ^ 100) * L ^ 6 * B := by ring
    _ ≤ (20 * 10 ^ 100) * L ^ 8 * B := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hB
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (by norm_num : (20 * 10 ^ 100 : ℝ) ≤ 10 ^ 110)
        (show 0 ≤ L ^ 8 * B by positivity)
      simpa only [mul_assoc] using h

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem scscSolverProgram_calls_rate (O : FreshOracle S.toNCObjective σ)
    (hfast : ℓ / 4 ≤ α) {η E₀ : ℝ} (hη : 0 < η) (hE : 0 ≤ E₀)
    (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν] :
    (∫ t, costValue t ∂(scscSolverProgram dx dy ℓ α σ μ η E₀).originalKernel O.kernel ∘ₘ ν) ≤
      10 ^ 110 * valueLogFactor ℓ σ μ η ^ 8 *
        (Real.sqrt (ℓ / μ) * Real.log (2 + (ℓ / μ) * E₀ / η) + σ ^ 2 / (μ * η)) := by
  rw [(S.scscSolverProgram_mean_calls O η E₀ ν).2]
  exact scscSolverWork_rate S.μ_pos S.μ_le_L S.α_pos hfast hη hE

end SCObjective
end FreshGradientMinimax
