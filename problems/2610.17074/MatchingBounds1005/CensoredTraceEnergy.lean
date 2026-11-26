import MatchingBounds1005.CensoredTensorEnergy
import MatchingBounds1005.ReadoutPrefixEvent

/-! Applying the stopped tensor energy theorem to the closed finite-query
event. The global fallback has the same telescoping bound, with angle one. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace MatchingBounds1005.CensoredTensorEnergy
open TensorGeometry TensorChannelRows TensorAdaptiveRows CensoredGaussianProcess HistoryPath
open ScheduledPrefix ChronologicalProjection
variable {Ω : Type*} [MeasurableSpace Ω] {d H : ℕ}

theorem path_cost_le_trace {ι : Type*} {M : ℕ}
    (σ₃ σ₄ : ℝ) (q : (n : ℕ) → SequentialPosterior.History Ω (H * (d + d)) n → Vec d)
    (hq : ∀ n, Measurable (q n)) (A : CensoredProtocol Ω (jointDim d) (H * (d + d)))
    (hrow : A.original.rowProtocol = tensorProtocol σ₃ σ₄ q hq)
    (seed : Ω) (answers : ℕ → Fin (H * (d + d)) → ℝ)
    (signals : Finset ι) (b : ι → Vec d) (hb : ∀ s ∈ signals, ‖b s‖ = 1)
    (w₃ w₄ : ℝ) (ell : ι → ℕ) (T : ℕ) (hell : ∀ s ∈ signals, ell s ≤ T)
    (hhidden : ∀ j, j < T → hidden A j (path seed answers j) =
      normalizedSignal σ₃ σ₄ (stoppedCoordinates 3 signals b w₃ ell j)
        (stoppedCoordinates 4 signals b w₄ ell j))
    (xs : Fin M → Vec d) (hM : T ≤ M)
    (hqueries : ∀ j (hj : j < T), q j (path seed answers j) = xs ⟨j, hj.trans_le hM⟩)
    (wide : ι → ℕ) (hwide : ∀ s ∈ signals, ell s ≤ wide s)
    (θ : ℝ) (hθ : 0 ≤ θ) (hx : xs ∈ readoutEvent b wide θ) :
    (∑ j ∈ Finset.range T, energyCost A 1 j (path seed answers j)) ≤
      3 * (signals.card : ℝ) ^ 2 * w₃ ^ 2 * θ ^ 4 / (2 * σ₃ ^ 2) +
      4 * (signals.card : ℝ) ^ 2 * w₄ ^ 2 * θ ^ 6 / (2 * σ₄ ^ 2) := by
  apply path_cost_le σ₃ σ₄ q hq A hrow seed answers signals b hb w₃ w₄ ell T hell hhidden
    (fun s => prefixSpan (List.ofFn xs) (wide s)) ?_ θ hθ ?_
  · intro s hs j hj
    rw [hqueries j (hj.trans_le (hell s hs))]
    apply Submodule.subset_span
    apply List.mem_take_iff_getElem.mpr
    refine ⟨j, ?_, ?_⟩
    · simp only [List.length_ofFn]
      exact lt_min (hj.trans_le (hwide s hs)) (hj.trans_le ((hell s hs).trans hM))
    · simp only [List.getElem_ofFn]
  · intro s hs
    simpa only [hb s hs, mul_one] using readoutEvent_projection hθ hx s

theorem path_cost_le_global {ι : Type*}
    (σ₃ σ₄ : ℝ) (q : (n : ℕ) → SequentialPosterior.History Ω (H * (d + d)) n → Vec d)
    (hq : ∀ n, Measurable (q n)) (A : CensoredProtocol Ω (jointDim d) (H * (d + d)))
    (hrow : A.original.rowProtocol = tensorProtocol σ₃ σ₄ q hq)
    (seed : Ω) (answers : ℕ → Fin (H * (d + d)) → ℝ)
    (signals : Finset ι) (b : ι → Vec d) (hb : ∀ s ∈ signals, ‖b s‖ = 1)
    (w₃ w₄ : ℝ) (ell : ι → ℕ) (T : ℕ) (hell : ∀ s ∈ signals, ell s ≤ T)
    (hhidden : ∀ j, j < T → hidden A j (path seed answers j) =
      normalizedSignal σ₃ σ₄ (stoppedCoordinates 3 signals b w₃ ell j)
        (stoppedCoordinates 4 signals b w₄ ell j)) :
    (∑ j ∈ Finset.range T, energyCost A 1 j (path seed answers j)) ≤
      3 * (signals.card : ℝ) ^ 2 * w₃ ^ 2 / (2 * σ₃ ^ 2) +
      4 * (signals.card : ℝ) ^ 2 * w₄ ^ 2 / (2 * σ₄ ^ 2) := by
  have ha (s : ι) (hs : s ∈ signals) : ‖(⊤ : Submodule ℝ (Vec d)).orthogonalProjection (b s)‖ ≤ (1 : ℝ) := by
    calc
      _ ≤ ‖(⊤ : Submodule ℝ (Vec d)).orthogonalProjection‖ * ‖b s‖ :=
        (⊤ : Submodule ℝ (Vec d)).orthogonalProjection.le_opNorm _
      _ ≤ 1 * ‖b s‖ := mul_le_mul_of_nonneg_right
        (⊤ : Submodule ℝ (Vec d)).orthogonalProjection_norm_le (norm_nonneg _)
      _ = 1 := by rw [hb s hs, mul_one]
  simpa only [one_pow, mul_one] using path_cost_le σ₃ σ₄ q hq A hrow seed answers
    signals b hb w₃ w₄ ell T hell hhidden (fun _ => ⊤) (by intros; trivial) 1 (by norm_num) ha

end MatchingBounds1005.CensoredTensorEnergy
