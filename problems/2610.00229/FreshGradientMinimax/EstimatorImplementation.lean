import FreshGradientMinimax.CorrectionMachine
import FreshGradientMinimax.SeedMachines
import FreshGradientMinimax.JointEstimator

/-! The complete relative estimator as original-query programs. A finite
label is sampled in the initial seed, then its three levels run sequentially.
The second output coordinate is the actual length of the stopped transcript.
This realizes the standalone estimator. EstimatorProgram, EpochProgram and
ValueProgram provide its adaptive composition inside the value solver;
the final fixed-budget algorithm is still separate. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy : ℕ}

def seededCorrectionMachine (dx dy : ℕ) (ℓ α γ m : ℝ) :
    OracleMachine dx dy (CorrectionMachineState dx dy × ℕ) :=
  OracleMachine.select (correctionMachine dx dy ℓ α γ m)

def seededCorrectionInitial (s : Joint dx dy × ℕ) : CorrectionMachineState dx dy × ℕ :=
  OracleMachine.selectInitial (fun _ => correctionInitial) s

theorem seededCorrectionInitial_measurable : Measurable (seededCorrectionInitial (dx := dx) (dy := dy)) :=
  OracleMachine.selectInitial_measurable _ (fun _ => correctionInitial_measurable)

def seededCorrectionAlgorithm (dx dy : ℕ) (ℓ α γ m : ℝ) : Algorithm dx dy (Joint dx dy × ℕ) :=
  (seededCorrectionMachine dx dy ℓ α γ m).compile seededCorrectionInitial seededCorrectionInitial_measurable

def seededCorrectionMethod (dx dy : ℕ) (ℓ α γ m : ℝ) {k : ℕ} (hk : 0 < k)
    (q : Joint dx dy) : RandomizedAlgorithm dx dy where
  Seed := Joint dx dy × ℕ
  seedLaw := finiteLabelKernel (levelProbability k) k q
  seedProbability := by
    letI := finiteLabelKernel_markov (X := Joint dx dy) (levelProbability k) k
      (fun j _ => (level_probability_pos hk j).le) (level_probabilities_sum hk)
    infer_instance
  policy := seededCorrectionAlgorithm dx dy ℓ α γ m

def seededCorrectionKernel (ℓ α γ m : ℝ) (k : ℕ) (a : Euclid dy → Euclid dy)
    (K : Kernel (Joint dx dy) (Joint dx dy)) : Kernel (Joint dx dy) (Euclid dy × ℕ) :=
  (seededCorrectionMachine dx dy ℓ α γ m).seedStoppedKernel
    seededCorrectionInitial seededCorrectionInitial_measurable K
    (fun s => correctionHorizon ℓ α γ m s.2)
    ((measurable_of_countable (correctionHorizon ℓ α γ m)).comp measurable_snd)
    (OracleMachine.selectRead (fun j => correctionRead j (levelProbability k j) a)) ∘ₖ
      finiteLabelKernel (levelProbability k) k

def originalMultilevelKernel (ℓ α γ m : ℝ) (k : ℕ) (a : Euclid dy → Euclid dy)
    (K : Kernel (Joint dx dy) (Joint dx dy)) : Kernel (Joint dx dy) (Euclid dy × ℕ) :=
  if k = 0 then
    ((levelAlgorithm dx dy ℓ (2 ^ 0) (levelSteps ℓ α γ m (2 ^ 0))).historyKernel K
      (levelWork ℓ α γ m 0)).map (fun h =>
        (levelTranscriptRead ℓ (2 ^ 0) (levelSteps ℓ α γ m (2 ^ 0)) a h, levelWork ℓ α γ m 0))
  else seededCorrectionKernel ℓ α γ m k a K

def originalRelativeEstimatorKernel (ℓ α σ ρ m e : ℝ) (a : Euclid dy → Euclid dy)
    (K : Kernel (Joint dx dy) (Joint dx dy)) : Kernel (Joint dx dy) (Euclid dy × ℕ) :=
  originalMultilevelKernel ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m
    (estimatorCutoff ρ m e σ) a K

namespace SCObjective
variable {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem seededCorrectionKernel_eq (O : FreshOracle S.toNCObjective σ) (γ m : ℝ) (k : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    seededCorrectionKernel ℓ α γ m k a O.kernel =
    finiteMixtureKernel (levelProbability k) (fun j => taggedKernel
      (independentCorrectionKernel
        (S.jointLevelKernel O (2 ^ 0) (levelSteps ℓ α γ m (2 ^ 0)) a ha)
        (S.jointLevelKernel O (2 ^ (j + 1)) (levelSteps ℓ α γ m (2 ^ (j + 1))) a ha)
        (S.jointLevelKernel O (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) a ha) (levelProbability k j))
      (correctionHorizon ℓ α γ m j)) k := by
  unfold seededCorrectionKernel seededCorrectionMachine seededCorrectionInitial
  rw [OracleMachine.select_stopped_seed_law _ _ (fun _ => correctionInitial_measurable) O.kernel
    (correctionHorizon ℓ α γ m) (fun j => correctionRead j (levelProbability k j) a)
    (fun j => correctionRead_measurable j _ a ha)]
  congr 1
  funext j
  rw [taggedKernel, ← S.correctionMachine_read O γ m j (levelProbability k j) a ha,
    ← Kernel.map_comp_right _ (f := correctionRead j (levelProbability k j) a)
      (g := fun r : Euclid dy => (r, correctionHorizon ℓ α γ m j))
      (correctionRead_measurable j _ a ha) (measurable_id.prodMk measurable_const)]
  rfl

theorem originalMultilevelKernel_eq (O : FreshOracle S.toNCObjective σ) (γ m : ℝ) (k : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    originalMultilevelKernel ℓ α γ m k a O.kernel =
      costedMultilevelKernel (fun j => S.jointLevelKernel O (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) a ha)
        (levelWork ℓ α γ m) k := by
  by_cases hk : k = 0
  · rw [originalMultilevelKernel, costedMultilevelKernel, if_pos hk, if_pos hk]
    exact S.dyadic_level_original_tagged_kernel O γ m 0 a ha
  · rw [originalMultilevelKernel, costedMultilevelKernel, if_neg hk, if_neg hk,
      S.seededCorrectionKernel_eq O γ m k a ha]
    simp only [correctionHorizon, Nat.add_assoc]

theorem originalRelativeEstimatorKernel_eq (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    originalRelativeEstimatorKernel ℓ α σ ρ m e a O.kernel = S.jointCostedEstimatorKernel O ρ m e a ha :=
  S.originalMultilevelKernel_eq O _ _ _ a ha

theorem originalRelativeEstimatorKernel_first (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    (originalRelativeEstimatorKernel ℓ α σ ρ m e a O.kernel).map Prod.fst =
      S.jointRelativeEstimatorKernel O ρ m e a ha := by
  rw [S.originalRelativeEstimatorKernel_eq O ρ m e a ha, S.jointCostedEstimatorKernel_first]

theorem originalRelativeEstimatorKernel_mean_calls (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (q : Joint dx dy) :
    (∫ z, (z.2 : ℝ) ∂originalRelativeEstimatorKernel ℓ α σ ρ m e a O.kernel q) =
      multilevelWork ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m (estimatorCutoff ρ m e σ) := by
  rw [S.originalRelativeEstimatorKernel_eq O ρ m e a ha, S.jointCostedEstimatorKernel_mean_cost]

theorem originalRelativeEstimatorKernel_calls_integrable (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (q : Joint dx dy) :
    Integrable (fun z => (z.2 : ℝ)) (originalRelativeEstimatorKernel ℓ α σ ρ m e a O.kernel q) := by
  rw [S.originalRelativeEstimatorKernel_eq O ρ m e a ha]
  exact costedMultilevelKernel_cost_integrable _ _ _ _

theorem originalRelativeEstimatorKernel_bias (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m e : ℝ} (hρ : 0 < ρ) (hm : 0 < m) (he : 0 < e)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (q : Joint dx dy) :
    ‖(∫ r, r ∂(originalRelativeEstimatorKernel ℓ α σ ρ m e a O.kernel).map Prod.fst q) -
      (gradient S.effectiveValue q.2 + a q.2)‖ ^ 2 ≤
        ρ * m * e + ρ * m ^ 2 * ‖q.1 - S.sliceMin q.2‖ ^ 2 := by
  rw [S.originalRelativeEstimatorKernel_first O ρ m e a ha]
  exact S.jointRelativeEstimatorKernel_bias O hαℓ hfast hρ hm he a ha q

theorem originalRelativeEstimatorKernel_variance (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m e : ℝ} (hρ : 0 < ρ) (hm : 0 < m)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (q : Joint dx dy) :
    (∫ r, ‖r - ∫ w, w ∂(originalRelativeEstimatorKernel ℓ α σ ρ m e a O.kernel).map Prod.fst q‖ ^ 2
      ∂(originalRelativeEstimatorKernel ℓ α σ ρ m e a O.kernel).map Prod.fst q) ≤
      140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2 + ρ * m ^ 2 * ‖q.1 - S.sliceMin q.2‖ ^ 2 := by
  rw [S.originalRelativeEstimatorKernel_first O ρ m e a ha]
  exact S.jointRelativeEstimatorKernel_variance O hαℓ hfast hρ hm a ha q

theorem originalRelativeEstimatorKernel_calls_bound (O : FreshOracle S.toNCObjective σ)
    (hfast : ℓ / 4 ≤ α) {ρ m e : ℝ} (hρ : 0 < ρ) (hm : 0 < m)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (q : Joint dx dy) :
    (∫ z, (z.2 : ℝ) ∂originalRelativeEstimatorKernel ℓ α σ ρ m e a O.kernel q) ≤
      4 * (estimatorCutoff ρ m e σ + 1 : ℝ) * (2 + 4 * Real.log 4 +
        4 * estimatorCutoff ρ m e σ * Real.log 2 + 4 * Real.log (1 + 14 / ρ) +
        4 * Real.log (estimatorCutoff ρ m e σ + 1 : ℝ) + 8 * Real.log (2 + ℓ / m)) := by
  rw [S.originalRelativeEstimatorKernel_mean_calls O ρ m e a ha]
  exact multilevelWork_log_bound S.toNCObjective.L_pos S.α_pos hfast hρ hm _

end SCObjective
end FreshGradientMinimax
