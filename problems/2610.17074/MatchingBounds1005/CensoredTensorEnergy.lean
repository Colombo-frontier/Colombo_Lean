import MatchingBounds1005.PairTensorEnergy
import MatchingBounds1005.TensorProtocolGeometry
import MatchingBounds1005.CensoredGaussianBound

/-! The actual simultaneous adaptive tensor protocol satisfies the stopped
two-channel cumulative KL energy bound. All row-space hypotheses are derived
from its accumulated physical rows. Only the geometric angle bound remains. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MatchingBounds1005.CensoredTensorEnergy
open TensorGeometry TensorChannelRows TensorAdaptiveRows TensorProtocolGeometry
open CensoredGaussianProcess CensoredGaussianBound HistoryPath GaussianBlockProjection

variable {Ω : Type*} [MeasurableSpace Ω] {d H : ℕ}

theorem path_cost_le {ι : Type*}
    (σ₃ σ₄ : ℝ) (q : (n : ℕ) → SequentialPosterior.History Ω (H * (d + d)) n → Vec d)
    (hq : ∀ n, Measurable (q n)) (A : CensoredProtocol Ω (jointDim d) (H * (d + d)))
    (hrow : A.original.rowProtocol = tensorProtocol σ₃ σ₄ q hq)
    (seed : Ω) (answers : ℕ → Fin (H * (d + d)) → ℝ)
    (signals : Finset ι) (b : ι → Vec d) (hb : ∀ s ∈ signals, ‖b s‖ = 1)
    (w₃ w₄ : ℝ) (ell : ι → ℕ) (T : ℕ) (hell : ∀ s ∈ signals, ell s ≤ T)
    (hhidden : ∀ j, j < T → hidden A j (path seed answers j) =
      normalizedSignal σ₃ σ₄ (stoppedCoordinates 3 signals b w₃ ell j)
        (stoppedCoordinates 4 signals b w₄ ell j))
    (W : ι → Submodule ℝ (Vec d))
    (hqueries : ∀ s ∈ signals, ∀ j, j < ell s → q j (path seed answers j) ∈ W s)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hangle : ∀ s ∈ signals, ‖(W s).orthogonalProjection (b s)‖ ≤ θ) :
    (∑ j ∈ Finset.range T, energyCost A 1 j (path seed answers j)) ≤
      3 * (signals.card : ℝ) ^ 2 * w₃ ^ 2 * θ ^ 4 / (2 * σ₃ ^ 2) +
      4 * (signals.card : ℝ) ^ 2 * w₄ ^ 2 * θ ^ 6 / (2 * σ₄ ^ 2) := by
  have heq : (∑ j ∈ Finset.range T, energyCost A 1 j (path seed answers j)) =
      ∑ j ∈ Finset.range T,
        ‖AdaptiveGaussian.projection
          (blockSpace (leftExposure σ₃ σ₄ q hq seed answers (j + 1))
            (rightExposure σ₃ σ₄ q hq seed answers (j + 1)) ⊓
          (blockSpace (leftExposure σ₃ σ₄ q hq seed answers j)
            (rightExposure σ₃ σ₄ q hq seed answers j))ᗮ)
          (normalizedSignal σ₃ σ₄ (stoppedCoordinates 3 signals b w₃ ell j)
            (stoppedCoordinates 4 signals b w₄ ell j))‖ ^ 2 / 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [energyCost_eq, hhidden j (Finset.mem_range.mp hj), innovation_path, hrow,
      pathExposure_block, pathExposure_block]
    simp only [one_pow, mul_one, InnovationEnergy.proj, AdaptiveGaussian.projection]
    rfl
  rw [heq]
  exact cumulative_pair_coordinate_energy signals b hb
    (leftExposure σ₃ σ₄ q hq seed answers) (leftExposure_monotone σ₃ σ₄ q hq seed answers)
    (rightExposure σ₃ σ₄ q hq seed answers) (rightExposure_monotone σ₃ σ₄ q hq seed answers)
    W ell T hell
    (fun s hs => (exposure_components_le σ₃ σ₄ q hq seed answers (ell s) (W s) (hqueries s hs)).1)
    (fun s hs => (exposure_components_le σ₃ σ₄ q hq seed answers (ell s) (W s) (hqueries s hs)).2)
    w₃ w₄ σ₃ σ₄ θ hθ hangle

end MatchingBounds1005.CensoredTensorEnergy
