import FreshGradientMinimax.ProgramBatch
import FreshGradientMinimax.EstimatorImplementation
import FreshGradientMinimax.CostedEpoch

/-! The analysed relative estimator is an OracleProgram. Its independent
minibatch is now one compiled original-query policy, not just a product of
separately implemented kernels. Output and accumulated call count agree
with the joint costed estimator used by the accelerated solver. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def finiteSeedLaw (p : ℕ → ℝ) (k : ℕ) : Measure ℕ :=
  finiteMixtureKernel p (fun j => Kernel.deterministic (fun _ : Unit => j) measurable_const) k ()

theorem finiteSeedLaw_probability (p : ℕ → ℝ) (k : ℕ) (hp : ∀ j < k, 0 ≤ p j)
    (hs : ∑ j ∈ Finset.range k, p j = 1) : IsProbabilityMeasure (finiteSeedLaw p k) := by
  letI := finiteMixtureKernel_markov p (fun j => Kernel.deterministic (fun _ : Unit => j) measurable_const) k hp hs
  exact inferInstanceAs (IsProbabilityMeasure (finiteMixtureKernel p
    (fun j => Kernel.deterministic (fun _ : Unit => j) measurable_const) k ()))

theorem mixtureKernel_finiteSeedLaw {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (p : ℕ → ℝ) (k : ℕ) [SFinite (finiteSeedLaw p k)] (L : ℕ → Kernel X Y) :
    mixtureKernel (finiteSeedLaw p k) L = finiteMixtureKernel p L k := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  rw [mixtureKernel_apply _ _ _ hA]
  simp only [finiteSeedLaw, finiteMixtureKernel_apply, Kernel.deterministic_apply,
    lintegral_finset_sum_measure, lintegral_smul_measure, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
  congr 1
  funext j
  rw [lintegral_dirac' _ (measurable_of_countable _)]

def levelProgram (dx dy : ℕ) (ℓ : ℝ) (b n : ℕ) (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    OracleProgram dx dy (Joint dx dy) (Euclid dy) where
  Seed := Unit
  seedLaw := Measure.dirac ()
  State := LevelMachineState dx dy
  machine _ := levelMachine dx dy ℓ b n
  init _ := levelInitial
  init_measurable _ := levelInitial_measurable
  read _ := levelRead b a
  read_measurable _ := levelRead_measurable b a ha
  calls _ := (n + 1) * b

def correctionProgram (dx dy : ℕ) (ℓ α γ m : ℝ) {k : ℕ} (hk : 0 < k)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) : OracleProgram dx dy (Joint dx dy) (Euclid dy) where
  Seed := ℕ
  seedLaw := finiteSeedLaw (levelProbability k) k
  seedProbability := finiteSeedLaw_probability _ _ (fun j _ => (level_probability_pos hk j).le) (level_probabilities_sum hk)
  State := CorrectionMachineState dx dy
  machine := correctionMachine dx dy ℓ α γ m
  init _ := correctionInitial
  init_measurable _ := correctionInitial_measurable
  read j := correctionRead j (levelProbability k j) a
  read_measurable j := correctionRead_measurable j _ a ha
  calls := correctionHorizon ℓ α γ m

def multilevelProgram (dx dy : ℕ) (ℓ α γ m : ℝ) (k : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) : OracleProgram dx dy (Joint dx dy) (Euclid dy) :=
  if hk : k = 0 then levelProgram dx dy ℓ (2 ^ 0) (levelSteps ℓ α γ m (2 ^ 0)) a ha
  else correctionProgram dx dy ℓ α γ m (Nat.pos_of_ne_zero hk) a ha

def relativeEstimatorProgram (dx dy : ℕ) (ℓ α σ ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) : OracleProgram dx dy (Joint dx dy) (Euclid dy) :=
  multilevelProgram dx dy ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m (estimatorCutoff ρ m e σ) a ha

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem levelProgram_law (O : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b) (n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    (levelProgram dx dy ℓ b n a ha).lawKernel O.kernel = taggedKernel (S.jointLevelKernel O b n a ha) ((n + 1) * b) := by
  change mixtureKernel (Measure.dirac ()) ((levelProgram dx dy ℓ b n a ha).branchKernel O.kernel) = _
  rw [mixtureKernel_dirac]
  change taggedKernel _ _ = _
  dsimp only [levelProgram]
  rw [S.levelMachine_run O hb n a ha]

theorem correctionProgram_law (O : FreshOracle S.toNCObjective σ) (γ m : ℝ) {k : ℕ} (hk : 0 < k)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    (correctionProgram dx dy ℓ α γ m hk a ha).lawKernel O.kernel =
      finiteMixtureKernel (levelProbability k) (fun j => taggedKernel
        (independentCorrectionKernel
          (S.jointLevelKernel O (2 ^ 0) (levelSteps ℓ α γ m (2 ^ 0)) a ha)
          (S.jointLevelKernel O (2 ^ (j + 1)) (levelSteps ℓ α γ m (2 ^ (j + 1))) a ha)
          (S.jointLevelKernel O (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) a ha) (levelProbability k j))
        (correctionHorizon ℓ α γ m j)) k := by
  letI := finiteSeedLaw_probability (levelProbability k) k (fun j _ => (level_probability_pos hk j).le)
    (level_probabilities_sum hk)
  change mixtureKernel (finiteSeedLaw (levelProbability k) k)
    ((correctionProgram dx dy ℓ α γ m hk a ha).branchKernel O.kernel) = _
  rw [mixtureKernel_finiteSeedLaw]
  congr 1
  funext j
  change taggedKernel _ _ = _
  dsimp only [correctionProgram]
  rw [S.correctionMachine_read O γ m j (levelProbability k j) a ha]

theorem multilevelProgram_law (O : FreshOracle S.toNCObjective σ) (γ m : ℝ) (k : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    (multilevelProgram dx dy ℓ α γ m k a ha).lawKernel O.kernel =
      costedMultilevelKernel (fun j => S.jointLevelKernel O (2 ^ j) (levelSteps ℓ α γ m (2 ^ j)) a ha)
        (levelWork ℓ α γ m) k := by
  by_cases hk : k = 0
  · rw [multilevelProgram, dif_pos hk, costedMultilevelKernel, if_pos hk, S.levelProgram_law O (by norm_num)]
    rfl
  · rw [multilevelProgram, dif_neg hk, costedMultilevelKernel, if_neg hk,
      S.correctionProgram_law O γ m (Nat.pos_of_ne_zero hk) a ha]
    simp only [correctionHorizon, Nat.add_assoc]

theorem relativeEstimatorProgram_law (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    (relativeEstimatorProgram dx dy ℓ α σ ρ m e a ha).lawKernel O.kernel = S.jointCostedEstimatorKernel O ρ m e a ha :=
  S.multilevelProgram_law O _ _ _ a ha

theorem relativeEstimatorProgram_original (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    (relativeEstimatorProgram dx dy ℓ α σ ρ m e a ha).originalKernel O.kernel =
      S.jointCostedEstimatorKernel O ρ m e a ha := by
  rw [OracleProgram.originalKernel_eq_law, S.relativeEstimatorProgram_law]

theorem batchedEstimatorProgram_original (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (b : ℕ) :
    ((relativeEstimatorProgram dx dy ℓ α σ ρ m e a ha).batch b).originalKernel O.kernel =
      costedBatchKernel (S.jointCostedEstimatorKernel O ρ m e a ha) b := by
  rw [OracleProgram.batch_original, S.relativeEstimatorProgram_original]

end SCObjective
end FreshGradientMinimax
