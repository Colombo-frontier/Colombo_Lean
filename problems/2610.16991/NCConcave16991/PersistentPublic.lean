import NCConcave16991.PersistentStationarity
import NCConcave16991.PersistentBudget
import NCConcave16991.TheoremStatements

/-! # Public loop lengths and the paper's averaging-rate expression -/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991

noncomputable section

def persistentPublicEpoch (p : ProblemParameters) : ℕ :=
  persistentEpochLength p.n (persistentConditionNumber p)

def persistentPublicBatch (p : ProblemParameters) : ℕ :=
  persistentBatchSize (persistentConditionNumber p) (persistentPublicEpoch p)

def persistentPublicInnerSteps (p : ProblemParameters) : ℕ :=
  persistentInnerSteps (persistentConditionNumber p)

def persistentPublicOuterSteps (p : ProblemParameters) : ℕ :=
  persistentOuterSteps (dimensionlessA p)

def persistentPublicBudget (p : ProblemParameters) : ℕ :=
  persistentQueryBudget p.n (persistentPublicEpoch p) (persistentPublicBatch p)
    (persistentPublicInnerSteps p) (persistentPublicOuterSteps p)

theorem persistent_public_parameters (p : ProblemParameters) :
    0 < persistentPublicEpoch p ∧ 0 < persistentPublicBatch p ∧
      0 < persistentPublicOuterSteps p ∧
      persistentConditionNumber p * persistentPublicEpoch p / persistentPublicBatch p ≤ 1 / 4096 ∧
      4294967296 * persistentConditionNumber p ^ 2 ≤ (persistentPublicInnerSteps p : ℝ) ∧
      4096 * (1 + dimensionlessA p) ≤ (persistentPublicOuterSteps p : ℝ) := by
  have hq := persistentEpochLength_pos p.n (persistentConditionNumber p)
  have hb := persistentBatchSize_bounds (persistentConditionNumber_ge_one p) hq
  have hS := persistentOuterSteps_bounds (dimensionlessA_pos p).le
  refine ⟨hq, hb.1, hS.1, ?_, ?_, hS.2.1⟩
  · exact batch_ceiling_ratio (by linarith [persistentConditionNumber_ge_one p])
      _ hq _ rfl hb.1
  · have hk := (persistentInnerSteps_bounds (persistentConditionNumber p)).1
    norm_num at hk
    exact hk

instance persistentPublicOuterSteps_neZero (p : ProblemParameters) :
    NeZero (persistentPublicOuterSteps p) :=
  ⟨Nat.ne_of_gt (persistent_public_parameters p).2.2.1⟩

theorem persistentConditionNumber_bound (p : ProblemParameters) :
    persistentConditionNumber p ≤ (2 : ℝ) ^ 20 * clippedDiameter (dimensionlessB p) ^ 2 := by
  have hclip := clippedDiameter_one_le (dimensionlessB p)
  have hclip0 := clippedDiameter_nonneg (dimensionlessB p)
  have hsmall : (1 : ℝ) ≤ (2 : ℝ) ^ 20 * clippedDiameter (dimensionlessB p) ^ 2 := by
    norm_num
    nlinarith
  by_cases hD : p.diameter = 0
  · simpa only [persistentConditionNumber, selectedDualRegularization, ite_eq_left hD,
      div_self p.L_pos.ne'] using hsmall
  · by_cases hL : p.L ≤ p.epsilon ^ 2 / (2 ^ 20 * p.L * p.diameter ^ 2)
    · simpa only [persistentConditionNumber, selectedDualRegularization, ite_eq_right hD,
        min_eq_left hL, div_self p.L_pos.ne'] using hsmall
    · have hmin : min p.L (p.epsilon ^ 2 / (2 ^ 20 * p.L * p.diameter ^ 2)) =
          p.epsilon ^ 2 / (2 ^ 20 * p.L * p.diameter ^ 2) := min_eq_right (le_of_not_ge hL)
      have hid : p.L / (p.epsilon ^ 2 / (2 ^ 20 * p.L * p.diameter ^ 2)) =
          (2 : ℝ) ^ 20 * dimensionlessB p ^ 2 := by
        dsimp [dimensionlessB]
        field_simp [p.epsilon_pos.ne']
        <;> ring
      rw [persistentConditionNumber, selectedDualRegularization, ite_eq_right hD, hmin, hid]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (dimensionlessB_nonneg p) (le_clippedDiameter _) 2) (by norm_num)

theorem persistent_public_rate_bound (p : ProblemParameters) :
    (persistentPublicBudget p : ℝ) ≤ (2 : ℝ) ^ 88 *
      ((p.n : ℝ) + (1 + dimensionlessA p) *
        ((p.n : ℝ) ^ (1 / 2 : ℝ) * clippedDiameter (dimensionlessB p) +
          clippedDiameter (dimensionlessB p) ^ 4)) := by
  let B := clippedDiameter (dimensionlessB p)
  let κ := persistentConditionNumber p
  have hB : 0 ≤ B := clippedDiameter_nonneg _
  have hκ : 0 ≤ κ := le_trans (by norm_num) (persistentConditionNumber_ge_one p)
  have hκbound : κ ≤ (2 : ℝ) ^ 20 * B ^ 2 := persistentConditionNumber_bound p
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hroot : Real.sqrt ((p.n : ℝ) * κ) ≤ 1024 * Real.sqrt (p.n : ℝ) * B := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (mul_nonneg hn hκ)]
    have hh := mul_le_mul_of_nonneg_left hκbound hn
    have hs := Real.sq_sqrt hn
    nlinarith only [hh, hs]
  have hpower : κ ^ 2 ≤ (2 : ℝ) ^ 40 * B ^ 4 := by
    have hh := pow_le_pow_left₀ hκ hκbound 2
    convert hh using 1 <;> ring
  have hW : Real.sqrt ((p.n : ℝ) * κ) + κ ^ 2 ≤
      (2 : ℝ) ^ 40 * (Real.sqrt (p.n : ℝ) * B + B ^ 4) := by
    have hh : 0 ≤ Real.sqrt (p.n : ℝ) * B := mul_nonneg (Real.sqrt_nonneg _) hB
    norm_num at hpower hroot ⊢
    nlinarith only [hroot, hpower, hh]
  have hbase := persistent_optimized_budget p.n_pos (persistentConditionNumber_ge_one p)
    (dimensionlessA_pos p).le
  have hmul := mul_le_mul_of_nonneg_left hW (show 0 ≤ 1 + dimensionlessA p by
    linarith [dimensionlessA_pos p])
  change (persistentPublicBudget p : ℝ) ≤ _ at hbase
  rw [← Real.sqrt_eq_rpow]
  change (persistentPublicBudget p : ℝ) ≤ (2 : ℝ) ^ 88 *
    ((p.n : ℝ) + (1 + dimensionlessA p) * (Real.sqrt (p.n : ℝ) * B + B ^ 4))
  norm_num at hbase hmul ⊢
  nlinarith only [hbase, hmul, hn]

abbrev PersistentPublicSeed (p : ProblemParameters) :=
  FiniteProcess.History
    (InnerAlgorithm.Seed p.n (persistentPublicInnerSteps p) ×
      (Fin (persistentPublicBatch p) → Fin p.n)) (persistentPublicOuterSteps p) ×
      Fin (persistentPublicOuterSteps p)

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

def persistentPublicLaw (p : ProblemParameters)
    [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)] :
    Measure (PersistentPublicSeed p) :=
  PersistentProcess.outputLaw (n := p.n) (b := persistentPublicBatch p)
    (InnerAlgorithm.seedLaw (persistentPublicInnerSteps p)) (persistentPublicOuterSteps p)

instance persistentPublicLaw_probability (p : ProblemParameters)
    [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)] :
    IsProbabilityMeasure (persistentPublicLaw p) := by
  unfold persistentPublicLaw
  infer_instance

def persistentPublicOutput (P : Problem p dx dy K) (y0 : DualSpace dy)
    (hy0 : y0 ∈ K.carrier) (ω : PersistentPublicSeed p) : PrimalSpace dx :=
  persistentSampleOutput P y0 hy0 (persistentPublicEpoch p) (persistentPublicInnerSteps p) ω

/-- Source B's expectation estimate with every loop length prescribed from
the public parameters and no convergence or moment hypotheses. -/
theorem persistent_public_original_gradient_mean (P : Problem p dx dy K)
    (hAS : P.averagedSmooth) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    (∫ ω, ‖gradient (problemMoreauEnvelope P) (persistentPublicOutput P y0 hy0 ω)‖ ^ 2
      ∂persistentPublicLaw p) < p.epsilon ^ 2 / 200 := by
  obtain ⟨hq, hb, hS, hbatch, hk, hSr⟩ := persistent_public_parameters p
  exact persistent_original_gradient_mean P hAS y0 hy0 hb hq hbatch hk hSr

theorem persistent_public_stationarity_probability (P : Problem p dx dy K)
    (hAS : P.averagedSmooth) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    (199 / 200 : ℝ) < (persistentPublicLaw p).real
      {ω | StationaryOutput P (persistentPublicOutput P y0 hy0 ω)} := by
  obtain ⟨hq, hb, hS, hbatch, hk, hSr⟩ := persistent_public_parameters p
  exact persistent_original_stationarity_probability P hAS y0 hy0 hb hq hbatch hk hSr

end

end NCConcave16991
