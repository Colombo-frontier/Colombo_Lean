import MatchingBounds1005.TensorOracle
import MatchingBounds1005.GaussianBlockProjection

/-!
# The manuscript's simultaneous normalized tensor rows

Cubic and quartic physical channels are rows of one standard Gaussian
latent vector. Each row includes its own physical noise scale; its latent
signal is divided by that scale. The paired channels are determined from
the same query, before either response is sampled.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace MatchingBounds1005.TensorChannelRows
open GaussianVector GaussianProduct GaussianBlockProjection GaussianFitter

def cubicDim (d : ℕ) := Fintype.card (Fin 3 → Fin d)
def quarticDim (d : ℕ) := Fintype.card (Fin 4 → Fin d)
def jointDim (d : ℕ) := cubicDim d + quarticDim d

def leftEmbedding (d : ℕ) (x : Vec (cubicDim d)) : Vec (jointDim d) :=
  (splitLinearEquiv (cubicDim d) (quarticDim d)).symm (x, 0)

def rightEmbedding (d : ℕ) (x : Vec (quarticDim d)) : Vec (jointDim d) :=
  (splitLinearEquiv (cubicDim d) (quarticDim d)).symm (0, x)

theorem leftEmbedding_continuous (d : ℕ) : Continuous (leftEmbedding d) :=
  (splitLinearEquiv (cubicDim d) (quarticDim d)).symm.toLinearMap.continuous_of_finiteDimensional.comp
    (continuous_id.prodMk continuous_const)

theorem rightEmbedding_continuous (d : ℕ) : Continuous (rightEmbedding d) :=
  (splitLinearEquiv (cubicDim d) (quarticDim d)).symm.toLinearMap.continuous_of_finiteDimensional.comp
    (continuous_const.prodMk continuous_id)

theorem leftEmbedding_inner {d : ℕ} (x : Vec (cubicDim d)) (z : Vec (jointDim d)) :
    ⟪leftEmbedding d x, z⟫_ℝ = ⟪x, (splitLinearEquiv (cubicDim d) (quarticDim d) z).1⟫_ℝ := by
  rw [inner_split, leftEmbedding, LinearEquiv.apply_symm_apply]
  simp only [inner_zero_left, add_zero]

theorem rightEmbedding_inner {d : ℕ} (x : Vec (quarticDim d)) (z : Vec (jointDim d)) :
    ⟪rightEmbedding d x, z⟫_ℝ = ⟪x, (splitLinearEquiv (cubicDim d) (quarticDim d) z).2⟫_ℝ := by
  rw [inner_split, rightEmbedding, LinearEquiv.apply_symm_apply]
  simp only [inner_zero_left, zero_add]

def jointRows {d : ℕ} (σ₃ σ₄ : ℝ) (x : Vec d) (i : Fin (d + d)) : Vec (jointDim d) :=
  match (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d + d)).symm i with
  | Sum.inl j => σ₃ • leftEmbedding d (TensorGeometry.channelCoordinates 3 x j)
  | Sum.inr j => σ₄ • rightEmbedding d (TensorGeometry.channelCoordinates 4 x j)

theorem jointRows_left {d : ℕ} (σ₃ σ₄ : ℝ) (x : Vec d) (i : Fin d) :
    jointRows σ₃ σ₄ x (Fin.castAdd d i) = σ₃ • leftEmbedding d (TensorGeometry.channelCoordinates 3 x i) := by
  simp only [jointRows, finSumFinEquiv_symm_apply_castAdd]

theorem jointRows_right {d : ℕ} (σ₃ σ₄ : ℝ) (x : Vec d) (i : Fin d) :
    jointRows σ₃ σ₄ x (Fin.natAdd d i) = σ₄ • rightEmbedding d (TensorGeometry.channelCoordinates 4 x i) := by
  simp only [jointRows, finSumFinEquiv_symm_apply_natAdd]

theorem jointRows_measurable {d : ℕ} (σ₃ σ₄ : ℝ) (i : Fin (d + d)) :
    Measurable (fun x : Vec d => jointRows σ₃ σ₄ x i) := by
  cases hi : (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d + d)).symm i with
  | inl j =>
      simp only [jointRows, hi]
      exact measurable_const.smul ((leftEmbedding_continuous d).measurable.comp
        ((measurable_pi_apply j).comp (TensorGeometry.channelCoordinates_measurable 3)))
  | inr j =>
      simp only [jointRows, hi]
      exact measurable_const.smul ((rightEmbedding_continuous d).measurable.comp
        ((measurable_pi_apply j).comp (TensorGeometry.channelCoordinates_measurable 4)))

theorem jointResponse_left {d : ℕ} (σ₃ σ₄ : ℝ) (x : Vec d)
    (z : Vec (jointDim d)) (i : Fin d) :
    rowResponse (jointRows σ₃ σ₄ x) z (Fin.castAdd d i) =
      σ₃ * TensorGeometry.channel 3 (TensorGeometry.gaussianTensor d 3
        (splitLinearEquiv (cubicDim d) (quarticDim d) z).1) x i := by
  change ⟪jointRows σ₃ σ₄ x (Fin.castAdd d i), z⟫_ℝ = _
  rw [jointRows_left, real_inner_smul_left, leftEmbedding_inner]
  exact congrArg (fun a : ℝ => σ₃ * a)
    (congrFun (TensorGeometry.channelCoordinates_response 3 x _) i)

theorem jointResponse_right {d : ℕ} (σ₃ σ₄ : ℝ) (x : Vec d)
    (z : Vec (jointDim d)) (i : Fin d) :
    rowResponse (jointRows σ₃ σ₄ x) z (Fin.natAdd d i) =
      σ₄ * TensorGeometry.channel 4 (TensorGeometry.gaussianTensor d 4
        (splitLinearEquiv (cubicDim d) (quarticDim d) z).2) x i := by
  change ⟪jointRows σ₃ σ₄ x (Fin.natAdd d i), z⟫_ℝ = _
  rw [jointRows_right, real_inner_smul_left, rightEmbedding_inner]
  exact congrArg (fun a : ℝ => σ₄ * a)
    (congrFun (TensorGeometry.channelCoordinates_response 4 x _) i)

def normalizedSignal {d : ℕ} (σ₃ σ₄ : ℝ) (S₃ : Vec (cubicDim d)) (S₄ : Vec (quarticDim d)) :
    Vec (jointDim d) := (splitLinearEquiv (cubicDim d) (quarticDim d)).symm
      (σ₃⁻¹ • S₃, σ₄⁻¹ • S₄)

theorem normalizedSignal_left {d : ℕ} (σ₃ σ₄ : ℝ) (S₃ : Vec (cubicDim d))
    (S₄ : Vec (quarticDim d)) (z : Vec (jointDim d)) (hσ₃ : σ₃ ≠ 0) :
    σ₃ • (splitLinearEquiv (cubicDim d) (quarticDim d) (normalizedSignal σ₃ σ₄ S₃ S₄ + z)).1 =
      S₃ + σ₃ • (splitLinearEquiv (cubicDim d) (quarticDim d) z).1 := by
  rw [map_add, normalizedSignal, LinearEquiv.apply_symm_apply]
  change σ₃ • (σ₃⁻¹ • S₃ + _) = _
  rw [smul_add, smul_smul, mul_inv_cancel₀ hσ₃, one_smul]

theorem normalizedSignal_right {d : ℕ} (σ₃ σ₄ : ℝ) (S₃ : Vec (cubicDim d))
    (S₄ : Vec (quarticDim d)) (z : Vec (jointDim d)) (hσ₄ : σ₄ ≠ 0) :
    σ₄ • (splitLinearEquiv (cubicDim d) (quarticDim d) (normalizedSignal σ₃ σ₄ S₃ S₄ + z)).2 =
      S₄ + σ₄ • (splitLinearEquiv (cubicDim d) (quarticDim d) z).2 := by
  rw [map_add, normalizedSignal, LinearEquiv.apply_symm_apply]
  change σ₄ • (σ₄⁻¹ • S₄ + _) = _
  rw [smul_add, smul_smul, mul_inv_cancel₀ hσ₄, one_smul]

end MatchingBounds1005.TensorChannelRows
