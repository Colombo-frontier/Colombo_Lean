import MatchingBounds1005.SourceTensorEnergy
import MatchingBounds1005.SourceReferenceLaw
import MatchingBounds1005.ReferenceRotationInputs
import MatchingBounds1005.AlgorithmTraceIsometry

/-! The actual retained oracle history controls the full cumulative
innovation cost of the source protocol through its closed geometry event. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations
open scoped BigOperators NNReal
namespace MatchingBounds1005.SourceReferenceReplay
open ReferenceState TensorChannelRows TensorGeometry TensorAdaptiveRows SequentialPosterior
open SourceReferenceProgram CensoredGaussianProcess ShiftedSequential HistoryPath
open CensoredTensorEnergy
variable {Seed : Type} [MeasurableSpace Seed] {d H N : ℕ}

attribute [local irreducible] RandomizedFO2003.Rotations.isometry Model.queryTrace

def pairCostCap (P : Parameters d N) (θ : ℝ) : ℝ :=
  3 * (N : ℝ) ^ 2 * (-120 * P.τ * P.a ^ 3) ^ 2 * θ ^ 4 / (2 * P.σ₃ ^ 2) +
  4 * (N : ℝ) ^ 2 * (120 * P.τ * P.a ^ 4) ^ 2 * θ ^ 6 / (2 * P.σ₄ ^ 2)

theorem pairCostCap_nonneg (P : Parameters d N) (θ : ℝ) : 0 ≤ pairCostCap P θ := by
  unfold pairCostCap
  positivity

def sourceProtocol (P : Parameters d N) (A : Model.Algorithm d Seed) :=
  protocol (H := H) P A (rotationMap d)
    (fun i => rotationMap_column_measurable (P.b i))
    (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q)

def traceGood (P : Parameters d N) (A : Model.Algorithm d Seed) (θ : ℝ) :=
  trace (H := H) P A (rotationMap d) H ⁻¹'
    Model.geometryEvent P.R A H P.b (fun i => min (H + 1) (P.disclosure i - 1)) θ

theorem traceGood_measurable (P : Parameters d N) (A : Model.Algorithm d Seed) (θ : ℝ) :
    MeasurableSet (traceGood (H := H) P A θ) :=
  (Model.geometryEvent_measurable _ _ _ _ _ _).preimage
    (trace_measurable P A (rotationMap d) (fun i => rotationMap_column_measurable (P.b i))
      (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q) H)

theorem source_path_hidden (P : Parameters d N) (A : Model.Algorithm d Seed)
    (hτ : ∀ i, 0 < P.disclosure i) (ω : Rotation (Vec d) × Seed)
    (answers : ℕ → Fin (H * (d + d)) → ℝ) (j : ℕ) (hj : j < H) :
    hidden (sourceProtocol (H := H) P A) j (path ω answers j) = normalizedSignal P.σ₃ P.σ₄
      (stoppedCoordinates 3 Finset.univ (fun i => rotationMap d ω.1 (P.b i))
        (-120 * P.τ * P.a ^ 3) (fun i => min (P.disclosure i - 1) H) j)
      (stoppedCoordinates 4 Finset.univ (fun i => rotationMap d ω.1 (P.b i))
        (120 * P.τ * P.a ^ 4) (fun i => min (P.disclosure i - 1) H) j) := by
  rw [stoppedCoordinates_truncate _ _ _ _ _ hj, stoppedCoordinates_truncate _ _ _ _ _ hj]
  unfold sourceProtocol
  rw [protocol_hidden _ _ _ _ _ _ hτ, initialSeed_path]

theorem traceGood_cost (P : Parameters d N) (A : Model.Algorithm d Seed)
    (hτ : ∀ i, 0 < P.disclosure i) (hunit : ∀ i, ‖P.b i‖ = 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (h : History (Rotation (Vec d) × Seed) (H * (d + d)) H)
    (hg : h ∈ traceGood P A θ) :
    SeededKernelKL.cumulativeCost (energyCost (sourceProtocol P A) 1) H h ≤ pairCostCap P θ := by
  obtain ⟨ω, answers, rfl⟩ := exists_path H h
  rw [cumulativeCost_path]
  let xs := Model.queryTrace P.R A H
    (ω.2, fun i => (replay P A (rotationMap d) H (path ω answers H)).2.2.1 i.val)
  have hxs : xs ∈ ScheduledPrefix.readoutEvent (fun i => rotationMap d ω.1 (P.b i))
      (fun i => min (H + 1) (P.disclosure i - 1)) θ := by
    have hp := Model.geometryEvent_physical P.R A H P.b
      (fun i => min (H + 1) (P.disclosure i - 1)) θ
      (trace P A (rotationMap d) H (path ω answers H)) hg
    simpa only [trace, initialSeed_path] using hp
  have hu (i : Fin N) (_ : i ∈ Finset.univ) : ‖rotationMap d ω.1 (P.b i)‖ = 1 := by
    change ‖isometry _ ω.1 (P.b i)‖ = 1
    rw [LinearIsometryEquiv.norm_map, hunit i]
  have hq (j : ℕ) (hj : j < H) :
      actualQuery P A (rotationMap d) j (path ω answers j) = xs ⟨j, hj.trans_le (Nat.le_succ H)⟩ := by
    change radial P.R (queryPoint A j (before P A (rotationMap d) j (path ω answers j))) = _
    rw [queryPoint_path_final P A (rotationMap d) ω answers H j hj.le]
    exact (Model.queryTrace_query P.R A H
      (ω.2, fun i => (replay P A (rotationMap d) H (path ω answers H)).2.2.1 i.val)
      (⟨j, hj⟩ : Fin H)).symm
  have hc := path_cost_le_trace P.σ₃ P.σ₄ (actualQuery P A (rotationMap d))
    (actualQuery_measurable P A (rotationMap d) (fun i => rotationMap_column_measurable (P.b i))
      (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q))
    (sourceProtocol P A) (protocol_tensorRows P A _ _ _ _) ω answers Finset.univ
    (fun i => rotationMap d ω.1 (P.b i)) hu (-120 * P.τ * P.a ^ 3) (120 * P.τ * P.a ^ 4)
    (fun i => min (P.disclosure i - 1) H) H (fun i _ => min_le_right _ _)
    (source_path_hidden P A hτ ω answers) xs (Nat.le_succ H) hq
    (fun i => min (H + 1) (P.disclosure i - 1))
    (fun i _ => le_min ((min_le_right _ _).trans (Nat.le_succ H)) (min_le_left _ _)) θ hθ hxs
  simpa only [Finset.card_univ, Fintype.card_fin, pairCostCap] using hc

theorem global_cost (P : Parameters d N) (A : Model.Algorithm d Seed)
    (hτ : ∀ i, 0 < P.disclosure i) (hunit : ∀ i, ‖P.b i‖ = 1)
    (h : History (Rotation (Vec d) × Seed) (H * (d + d)) H) :
    SeededKernelKL.cumulativeCost (energyCost (sourceProtocol P A) 1) H h ≤ pairCostCap P 1 := by
  obtain ⟨ω, answers, rfl⟩ := exists_path H h
  rw [cumulativeCost_path]
  have hu (i : Fin N) (_ : i ∈ Finset.univ) : ‖rotationMap d ω.1 (P.b i)‖ = 1 := by
    change ‖isometry _ ω.1 (P.b i)‖ = 1
    rw [LinearIsometryEquiv.norm_map, hunit i]
  have hc := path_cost_le_global P.σ₃ P.σ₄ (actualQuery P A (rotationMap d))
    (actualQuery_measurable P A (rotationMap d) (fun i => rotationMap_column_measurable (P.b i))
      (rotationMap_column_measurable P.c) (rotationMap_quadratic_measurable P.Q))
    (sourceProtocol P A) (protocol_tensorRows P A _ _ _ _) ω answers Finset.univ
    (fun i => rotationMap d ω.1 (P.b i)) hu (-120 * P.τ * P.a ^ 3) (120 * P.τ * P.a ^ 4)
    (fun i => min (P.disclosure i - 1) H) H (fun i _ => min_le_right _ _)
    (source_path_hidden P A hτ ω answers)
  simpa only [Finset.card_univ, Fintype.card_fin, pairCostCap, one_pow, mul_one] using hc

end MatchingBounds1005.SourceReferenceReplay
