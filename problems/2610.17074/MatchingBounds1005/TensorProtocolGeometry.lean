import MatchingBounds1005.TensorAdaptiveRows
import MatchingBounds1005.TensorCoordinateEnergy
import MatchingBounds1005.GaussianPureRows
import MatchingBounds1005.ReferenceTransitionLink
import MatchingBounds1005.HistoryPath

/-! Actual accumulated tensor rows: channel block decomposition, monotonicity,
and containment in the whole-prefix tensor observation envelope. -/
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.TensorProtocolGeometry
open TensorChannelRows TensorGeometry GaussianBlockProjection
open GaussianPureRows AccumulatedRows SequentialPosterior HistoryPath

def leftMap (d : ℕ) : Vec (jointDim d) →ₗ[ℝ] Vec (cubicDim d) :=
  (LinearMap.fst ℝ (Vec (cubicDim d)) (Vec (quarticDim d))).comp
    (splitLinearEquiv (cubicDim d) (quarticDim d)).toLinearMap

def rightMap (d : ℕ) : Vec (jointDim d) →ₗ[ℝ] Vec (quarticDim d) :=
  (LinearMap.snd ℝ (Vec (cubicDim d)) (Vec (quarticDim d))).comp
    (splitLinearEquiv (cubicDim d) (quarticDim d)).toLinearMap

theorem leftMap_leftEmbedding (d : ℕ) (z : Vec (cubicDim d)) : leftMap d (leftEmbedding d z) = z := by
  change ((splitLinearEquiv (cubicDim d) (quarticDim d))
    ((splitLinearEquiv (cubicDim d) (quarticDim d)).symm (z, 0))).1 = z
  rw [LinearEquiv.apply_symm_apply]

theorem rightMap_leftEmbedding (d : ℕ) (z : Vec (cubicDim d)) : rightMap d (leftEmbedding d z) = 0 := by
  change ((splitLinearEquiv (cubicDim d) (quarticDim d))
    ((splitLinearEquiv (cubicDim d) (quarticDim d)).symm (z, 0))).2 = 0
  rw [LinearEquiv.apply_symm_apply]

theorem leftMap_rightEmbedding (d : ℕ) (z : Vec (quarticDim d)) : leftMap d (rightEmbedding d z) = 0 := by
  change ((splitLinearEquiv (cubicDim d) (quarticDim d))
    ((splitLinearEquiv (cubicDim d) (quarticDim d)).symm (0, z))).1 = 0
  rw [LinearEquiv.apply_symm_apply]

theorem rightMap_rightEmbedding (d : ℕ) (z : Vec (quarticDim d)) : rightMap d (rightEmbedding d z) = z := by
  change ((splitLinearEquiv (cubicDim d) (quarticDim d))
    ((splitLinearEquiv (cubicDim d) (quarticDim d)).symm (0, z))).2 = z
  rw [LinearEquiv.apply_symm_apply]

theorem jointRows_pure {d : ℕ} (σ₃ σ₄ : ℝ) (x : Vec d) (i : Fin (d + d)) :
    Pure (jointRows σ₃ σ₄ x i) := by
  cases hi : (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d + d)).symm i with
  | inl j =>
    simp only [jointRows, hi]
    apply pure_smul
    right
    rw [leftEmbedding, LinearEquiv.apply_symm_apply]
  | inr j =>
    simp only [jointRows, hi]
    apply pure_smul
    left
    rw [rightEmbedding, LinearEquiv.apply_symm_apply]

theorem jointRows_component_mem {d : ℕ} (σ₃ σ₄ : ℝ) (W : Submodule ℝ (Vec d))
    {x : Vec d} (hx : x ∈ W) (i : Fin (d + d)) :
    leftMap d (jointRows σ₃ σ₄ x i) ∈ coordinateObservation 3 W ∧
    rightMap d (jointRows σ₃ σ₄ x i) ∈ coordinateObservation 4 W := by
  cases hi : (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d + d)).symm i with
  | inl j =>
    simp only [jointRows, hi, map_smul, leftMap_leftEmbedding, rightMap_leftEmbedding]
    exact ⟨Submodule.smul_mem _ _ (channelCoordinates_mem (k := 3) W hx j), by simp⟩
  | inr j =>
    simp only [jointRows, hi, map_smul, leftMap_rightEmbedding, rightMap_rightEmbedding]
    exact ⟨by simp, Submodule.smul_mem _ _ (channelCoordinates_mem (k := 4) W hx j)⟩

theorem accumulated_path_property {Ω : Type*} [MeasurableSpace Ω] {D H r : ℕ}
    (current : (n : ℕ) → History Ω (H * r) n → Fin r → Vec D)
    (seed : Ω) (answers : ℕ → Fin (H * r) → ℝ) (n : ℕ) (P : Vec D → Prop)
    (hzero : P 0) (hcurrent : ∀ j, j ≤ n → ∀ i, P (current j (path seed answers j) i))
    (i : Fin (H * r)) : P (accumulated current n (path seed answers n) i) := by
  induction n with
  | zero =>
    rw [accumulated]
    split_ifs
    · exact hcurrent 0 le_rfl _
    · exact hzero
  | succ n ih =>
    rw [accumulated]
    split_ifs
    · exact hcurrent (n + 1) le_rfl _
    · exact ih (fun j hj => hcurrent j (hj.trans (Nat.le_succ n)))

variable {Ω : Type*} [MeasurableSpace Ω] {d H : ℕ}
  (σ₃ σ₄ : ℝ) (q : (n : ℕ) → History Ω (H * (d + d)) n → Vec d)
  (hq : ∀ n, Measurable (q n))

def leftExposure (seed : Ω) (answers : ℕ → Fin (H * (d + d)) → ℝ) (n : ℕ) :=
  (pathExposure (TensorAdaptiveRows.tensorProtocol σ₃ σ₄ q hq) seed answers n).map (leftMap d)

def rightExposure (seed : Ω) (answers : ℕ → Fin (H * (d + d)) → ℝ) (n : ℕ) :=
  (pathExposure (TensorAdaptiveRows.tensorProtocol σ₃ σ₄ q hq) seed answers n).map (rightMap d)

theorem leftExposure_monotone (seed : Ω) (answers : ℕ → Fin (H * (d + d)) → ℝ) :
    Monotone (leftExposure σ₃ σ₄ q hq seed answers) :=
  fun _ _ h => Submodule.map_mono ((pathExposure_monotone _ seed answers) h)

theorem rightExposure_monotone (seed : Ω) (answers : ℕ → Fin (H * (d + d)) → ℝ) :
    Monotone (rightExposure σ₃ σ₄ q hq seed answers) :=
  fun _ _ h => Submodule.map_mono ((pathExposure_monotone _ seed answers) h)

theorem pathExposure_block (seed : Ω) (answers : ℕ → Fin (H * (d + d)) → ℝ) (n : ℕ) :
    pathExposure (TensorAdaptiveRows.tensorProtocol σ₃ σ₄ q hq) seed answers n =
      blockSpace (leftExposure σ₃ σ₄ q hq seed answers n)
        (rightExposure σ₃ σ₄ q hq seed answers n) := by
  let A := TensorAdaptiveRows.tensorProtocol σ₃ σ₄ q hq
  let rows := ReferenceTransitionLink.oldRows A.rows n (path seed answers n)
  have hp : ∀ i, Pure (rows i) := by
    intro i
    cases n with
    | zero => exact pure_zero
    | succ n =>
      exact accumulated_path_property (TensorAdaptiveRows.currentRows σ₃ σ₄ q) seed answers n
        Pure pure_zero (fun j _ i => jointRows_pure σ₃ σ₄ (q j (path seed answers j)) i) i
  have hspan : Submodule.span ℝ (Set.range rows) = pathExposure A seed answers n :=
    ReferenceTransitionLink.oldRows_span A.rows n (path seed answers n)
  unfold leftExposure rightExposure
  change pathExposure A seed answers n =
    blockSpace ((pathExposure A seed answers n).map (leftMap d))
      ((pathExposure A seed answers n).map (rightMap d))
  rw [← hspan, Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
  exact span_pure_rows rows hp

theorem exposure_components_le (seed : Ω) (answers : ℕ → Fin (H * (d + d)) → ℝ)
    (n : ℕ) (W : Submodule ℝ (Vec d)) (hx : ∀ j, j < n → q j (path seed answers j) ∈ W) :
    leftExposure σ₃ σ₄ q hq seed answers n ≤ coordinateObservation 3 W ∧
    rightExposure σ₃ σ₄ q hq seed answers n ≤ coordinateObservation 4 W := by
  cases n with
  | zero => simp [leftExposure, rightExposure, pathExposure_zero]
  | succ n =>
    have hm (i : Fin (H * (d + d))) :
        leftMap d (accumulated (TensorAdaptiveRows.currentRows σ₃ σ₄ q) n (path seed answers n) i)
            ∈ coordinateObservation 3 W ∧
        rightMap d (accumulated (TensorAdaptiveRows.currentRows σ₃ σ₄ q) n (path seed answers n) i)
            ∈ coordinateObservation 4 W := by
      refine accumulated_path_property (TensorAdaptiveRows.currentRows σ₃ σ₄ q) seed answers n
        (fun z => leftMap d z ∈ coordinateObservation 3 W ∧ rightMap d z ∈ coordinateObservation 4 W)
        ?_ ?_ i
      · simp only [map_zero, Submodule.zero_mem, and_self]
      · intro j hj i
        exact jointRows_component_mem σ₃ σ₄ W (hx j (Nat.lt_succ_of_le hj)) i
    constructor
    · change (Submodule.span ℝ (Set.range _)).map (leftMap d) ≤ _
      rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (hm i).1
    · change (Submodule.span ℝ (Set.range _)).map (rightMap d) ≤ _
      rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (hm i).2

end MatchingBounds1005.TensorProtocolGeometry
