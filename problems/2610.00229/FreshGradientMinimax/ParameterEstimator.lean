import FreshGradientMinimax.ParameterRead
import FreshGradientMinimax.CostedTransport
import FreshGradientMinimax.EstimatorProgram

/-! Jointly measurable known gradient corrections can depend on an
arbitrary measurable parameter. Every fiber agrees with the existing
costed estimator, including its true number of original oracle calls. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy : ℕ} {Θ : Type} [MeasurableSpace Θ]

def parameterLevelRead (b : ℕ) (a : Θ × Euclid dy → Euclid dy)
    (s : Θ × LevelMachineState dx dy) : Euclid dy :=
  -((b : ℝ)⁻¹ • s.2.2) + a (s.1, s.2.1.1.2)

theorem parameterLevelRead_measurable (b : ℕ) (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a) :
    Measurable (parameterLevelRead (dx := dx) b a) :=
  (measurable_const.smul measurable_snd.snd).neg.add
    (ha.comp (measurable_fst.prodMk measurable_snd.fst.fst.snd))

def parameterCorrectionRead (j : ℕ) (p : ℝ) (a : Θ × Euclid dy → Euclid dy)
    (s : Θ × CorrectionMachineState dx dy) : Euclid dy :=
  correctionValue p (parameterLevelRead (2 ^ 0) a (s.1, s.2.1),
    (parameterLevelRead (2 ^ (j + 1)) a (s.1, s.2.2.1),
      parameterLevelRead (2 ^ j) a (s.1, s.2.2.2)))

theorem parameterCorrectionRead_measurable (j : ℕ) (p : ℝ)
    (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a) :
    Measurable (parameterCorrectionRead (dx := dx) j p a) :=
  (correctionValue_continuous p).measurable.comp
    (((parameterLevelRead_measurable _ a ha).comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      (((parameterLevelRead_measurable _ a ha).comp (measurable_fst.prodMk measurable_snd.snd.fst)).prodMk
        ((parameterLevelRead_measurable _ a ha).comp (measurable_fst.prodMk measurable_snd.snd.snd))))

def parameterLevelProgram (dx dy : ℕ) (ℓ : ℝ) (b n : ℕ)
    (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a) :
    OracleProgram dx dy (Θ × Joint dx dy) (Euclid dy) :=
  (levelProgram dx dy ℓ b n (fun _ => 0) measurable_const).parameterRead
    (fun _ => parameterLevelRead b a) (fun _ => parameterLevelRead_measurable b a ha)

def parameterCorrectionProgram (dx dy : ℕ) (ℓ α γ m : ℝ) {k : ℕ} (hk : 0 < k)
    (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a) :
    OracleProgram dx dy (Θ × Joint dx dy) (Euclid dy) :=
  (correctionProgram dx dy ℓ α γ m hk (fun _ => 0) measurable_const).parameterRead
    (fun j => parameterCorrectionRead j (levelProbability k j) a)
    (fun j => parameterCorrectionRead_measurable j _ a ha)

def parameterMultilevelProgram (dx dy : ℕ) (ℓ α γ m : ℝ) (k : ℕ)
    (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a) :
    OracleProgram dx dy (Θ × Joint dx dy) (Euclid dy) :=
  if hk : k = 0 then parameterLevelProgram dx dy ℓ (2 ^ 0) (levelSteps ℓ α γ m (2 ^ 0)) a ha
  else parameterCorrectionProgram dx dy ℓ α γ m (Nat.pos_of_ne_zero hk) a ha

def parameterEstimatorProgram (dx dy : ℕ) (ℓ α σ ρ m e : ℝ)
    (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a) :
    OracleProgram dx dy (Θ × Joint dx dy) (Euclid dy) :=
  parameterMultilevelProgram dx dy ℓ α (estimatorGamma ρ (estimatorCutoff ρ m e σ)) m
    (estimatorCutoff ρ m e σ) a ha

theorem parameterLevelProgram_fiber (ℓ : ℝ) (b n : ℕ)
    (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) :
    ((parameterLevelProgram dx dy ℓ b n a ha).lawKernel K).comap (fun x => (θ, x)) measurable_prodMk_left =
      (levelProgram dx dy ℓ b n (fun v => a (θ, v)) (ha.comp measurable_prodMk_left)).lawKernel K := by
  rw [parameterLevelProgram, OracleProgram.parameterRead_law]
  rfl

theorem parameterCorrectionProgram_fiber (ℓ α γ m : ℝ) {k : ℕ} (hk : 0 < k)
    (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) :
    ((parameterCorrectionProgram dx dy ℓ α γ m hk a ha).lawKernel K).comap
        (fun x => (θ, x)) measurable_prodMk_left =
      (correctionProgram dx dy ℓ α γ m hk (fun v => a (θ, v)) (ha.comp measurable_prodMk_left)).lawKernel K := by
  rw [parameterCorrectionProgram, OracleProgram.parameterRead_law]
  rfl

theorem parameterMultilevelProgram_fiber (ℓ α γ m : ℝ) (k : ℕ)
    (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) :
    ((parameterMultilevelProgram dx dy ℓ α γ m k a ha).lawKernel K).comap
        (fun x => (θ, x)) measurable_prodMk_left =
      (multilevelProgram dx dy ℓ α γ m k (fun v => a (θ, v)) (ha.comp measurable_prodMk_left)).lawKernel K := by
  by_cases hk : k = 0
  · rw [parameterMultilevelProgram, dif_pos hk, multilevelProgram, dif_pos hk, parameterLevelProgram_fiber]
  · rw [parameterMultilevelProgram, dif_neg hk, multilevelProgram, dif_neg hk, parameterCorrectionProgram_fiber]

namespace SCObjective
variable {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem parameterEstimatorProgram_fiber (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a) (θ : Θ) :
    ((parameterEstimatorProgram dx dy ℓ α σ ρ m e a ha).lawKernel O.kernel).comap
        (fun x => (θ, x)) measurable_prodMk_left =
      S.jointCostedEstimatorKernel O ρ m e (fun v => a (θ, v)) (ha.comp measurable_prodMk_left) := by
  rw [parameterEstimatorProgram, parameterMultilevelProgram_fiber]
  exact S.relativeEstimatorProgram_law O ρ m e _ _

theorem parameterEstimatorProgram_batch_fiber (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (a : Θ × Euclid dy → Euclid dy) (ha : Measurable a) (θ : Θ) (b : ℕ) :
    (((parameterEstimatorProgram dx dy ℓ α σ ρ m e a ha).batch b).lawKernel O.kernel).comap
        (fun x => (θ, x)) measurable_prodMk_left =
      costedBatchKernel (S.jointCostedEstimatorKernel O ρ m e (fun v => a (θ, v))
        (ha.comp measurable_prodMk_left)) b := by
  rw [OracleProgram.batch_law, costedBatchKernel_comap, S.parameterEstimatorProgram_fiber]

end SCObjective
end FreshGradientMinimax
