import MatchingBounds1005.TensorChannelRows
import MatchingBounds1005.AccumulatedRows
import MatchingBounds1005.ShiftedSequential

/-!
# Actual adaptive row protocol for the simultaneous tensor channels

One query chooses both normalized tensor row blocks. All preceding query
blocks are retained in a fixed finite array, and the generic static Gaussian
posterior theorem applies to the single joint normalized latent vector.
The separate disclosure interface must restrict which queries are allowed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace MatchingBounds1005.TensorAdaptiveRows
open GaussianVector TensorChannelRows SequentialPosterior AccumulatedRows GaussianFitter

variable {Ω : Type*} [MeasurableSpace Ω] {d H : ℕ}

def currentRows (σ₃ σ₄ : ℝ)
    (q : (n : ℕ) → History Ω (H * (d + d)) n → Vec d) (n : ℕ)
    (h : History Ω (H * (d + d)) n) : Fin (d + d) → Vec (jointDim d) :=
  jointRows σ₃ σ₄ (q n h)

theorem currentRows_measurable (σ₃ σ₄ : ℝ)
    (q : (n : ℕ) → History Ω (H * (d + d)) n → Vec d) (hq : ∀ n, Measurable (q n))
    (n : ℕ) (i : Fin (d + d)) : Measurable (fun h => currentRows σ₃ σ₄ q n h i) :=
  (jointRows_measurable σ₃ σ₄ i).comp (hq n)

def tensorProtocol (σ₃ σ₄ : ℝ)
    (q : (n : ℕ) → History Ω (H * (d + d)) n → Vec d) (hq : ∀ n, Measurable (q n)) :
    RowProtocol Ω (jointDim d) (H * (d + d)) :=
  protocol (currentRows σ₃ σ₄ q) (currentRows_measurable σ₃ σ₄ q hq)

theorem tensorProtocol_response_left (σ₃ σ₄ : ℝ)
    (q : (n : ℕ) → History Ω (H * (d + d)) n → Vec d) (hq : ∀ n, Measurable (q n))
    (n : Fin H) (h : History Ω (H * (d + d)) n.val) (z : Vec (jointDim d)) (i : Fin d) :
    rowResponse ((tensorProtocol σ₃ σ₄ q hq).rows n.val h) z
      (finProdFinEquiv (n, Fin.castAdd d i)) =
      σ₃ * TensorGeometry.channel 3 (TensorGeometry.gaussianTensor d 3
        (GaussianBlockProjection.splitLinearEquiv (cubicDim d) (quarticDim d) z).1) (q n.val h) i := by
  rw [show (tensorProtocol σ₃ σ₄ q hq).rows = accumulated (currentRows σ₃ σ₄ q) from rfl,
    current_response]
  exact jointResponse_left σ₃ σ₄ (q n.val h) z i

theorem tensorProtocol_response_right (σ₃ σ₄ : ℝ)
    (q : (n : ℕ) → History Ω (H * (d + d)) n → Vec d) (hq : ∀ n, Measurable (q n))
    (n : Fin H) (h : History Ω (H * (d + d)) n.val) (z : Vec (jointDim d)) (i : Fin d) :
    rowResponse ((tensorProtocol σ₃ σ₄ q hq).rows n.val h) z
      (finProdFinEquiv (n, Fin.natAdd d i)) =
      σ₄ * TensorGeometry.channel 4 (TensorGeometry.gaussianTensor d 4
        (GaussianBlockProjection.splitLinearEquiv (cubicDim d) (quarticDim d) z).2) (q n.val h) i := by
  rw [show (tensorProtocol σ₃ σ₄ q hq).rows = accumulated (currentRows σ₃ σ₄ q) from rfl,
    current_response]
  exact jointResponse_right σ₃ σ₄ (q n.val h) z i

theorem normalizedSignal_measurable (σ₃ σ₄ : ℝ)
    (S₃ : Ω → Vec (cubicDim d)) (S₄ : Ω → Vec (quarticDim d))
    (hS₃ : Measurable S₃) (hS₄ : Measurable S₄) :
    Measurable (fun ω => normalizedSignal σ₃ σ₄ (S₃ ω) (S₄ ω)) :=
  (GaussianBlockProjection.splitLinearEquiv (cubicDim d) (quarticDim d)).symm.toLinearMap.continuous_of_finiteDimensional.measurable.comp
    ((measurable_const.smul hS₃).prodMk (measurable_const.smul hS₄))

def staticProtocol (σ₃ σ₄ : ℝ)
    (q : (n : ℕ) → History Ω (H * (d + d)) n → Vec d) (hq : ∀ n, Measurable (q n))
    (S₃ : Ω → Vec (cubicDim d)) (S₄ : Ω → Vec (quarticDim d))
    (hS₃ : Measurable S₃) (hS₄ : Measurable S₄) :
    ShiftedSequential.ShiftedProtocol Ω (jointDim d) (H * (d + d)) where
  rowProtocol := tensorProtocol σ₃ σ₄ q hq
  signal ω := normalizedSignal σ₃ σ₄ (S₃ ω) (S₄ ω)
  measurable_signal := normalizedSignal_measurable σ₃ σ₄ S₃ S₄ hS₃ hS₄

/-- The tensor protocol's actual unchanged static latent parameter has the
derived fresh-residual posterior at every query. Its noise scale is one
because the physical channel scales occur in the normalized rows. -/
theorem static_tensor_posterior (σ₃ σ₄ : ℝ)
    (q : (n : ℕ) → History Ω (H * (d + d)) n → Vec d) (hq : ∀ n, Measurable (q n))
    (S₃ : Ω → Vec (cubicDim d)) (S₄ : Ω → Vec (quarticDim d))
    (hS₃ : Measurable S₃) (hS₄ : Measurable S₄)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    ShiftedSequential.staticJointLaw (staticProtocol σ₃ σ₄ q hq S₃ S₄ hS₃ hS₄) 1 ν₀ n =
      ShiftedSequential.representedLaw (staticProtocol σ₃ σ₄ q hq S₃ S₄ hS₃ hS₄) 1 ν₀ n :=
  ShiftedSequential.staticJointLaw_eq_represented _ _ _ _

end MatchingBounds1005.TensorAdaptiveRows
