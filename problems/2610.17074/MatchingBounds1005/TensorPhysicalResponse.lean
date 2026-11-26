import MatchingBounds1005.TensorChannelRows

/-! Exact simultaneous physical-channel responses of the single normalized
Gaussian latent vector. The cubic and quartic channels retain their distinct
physical noise scales and the source 1/3, 1/4 normalization. -/
noncomputable section
open scoped InnerProductSpace

namespace MatchingBounds1005.TensorGeometry

theorem channel_add {d : ℕ} (k : ℕ) (S T : Tensor d k) (x : Vec d) :
    channel k (S + T) x = channel k S x + channel k T x := by
  ext i
  simp only [PiLp.add_apply, channel_coordinate, inner_add_right]

theorem channel_smul {d : ℕ} (k : ℕ) (c : ℝ) (T : Tensor d k) (x : Vec d) :
    channel k (c • T) x = c • channel k T x := by
  ext i
  simp only [PiLp.smul_apply, smul_eq_mul, channel_coordinate, real_inner_smul_right]

end MatchingBounds1005.TensorGeometry

namespace MatchingBounds1005.TensorChannelRows
open GaussianBlockProjection GaussianFitter TensorGeometry

theorem jointResponse_signal_left {d : ℕ} (σ₃ σ₄ : ℝ) (hσ₃ : σ₃ ≠ 0)
    (S₃ : Tensor d 3) (S₄ : Tensor d 4) (z : Vec (jointDim d)) (x : Vec d) (i : Fin d) :
    rowResponse (jointRows σ₃ σ₄ x)
      (normalizedSignal σ₃ σ₄ (tensorCoordinates d 3 S₃) (tensorCoordinates d 4 S₄) + z)
        (Fin.castAdd d i) =
      channel 3 (S₃ + σ₃ • gaussianTensor d 3
        (splitLinearEquiv (cubicDim d) (quarticDim d) z).1) x i := by
  rw [jointResponse_left]
  have h := congrArg (gaussianTensor d 3)
    (normalizedSignal_left σ₃ σ₄ (tensorCoordinates d 3 S₃) (tensorCoordinates d 4 S₄) z hσ₃)
  simp only [gaussianTensor, map_smul, map_add, LinearIsometryEquiv.symm_apply_apply] at h
  have he : σ₃ • gaussianTensor d 3
      (splitLinearEquiv (cubicDim d) (quarticDim d)
        (normalizedSignal σ₃ σ₄ (tensorCoordinates d 3 S₃) (tensorCoordinates d 4 S₄) + z)).1 =
      S₃ + σ₃ • gaussianTensor d 3 (splitLinearEquiv (cubicDim d) (quarticDim d) z).1 := by
    simpa only [gaussianTensor, map_add] using h
  rw [← he, channel_smul]
  rfl

theorem jointResponse_signal_right {d : ℕ} (σ₃ σ₄ : ℝ) (hσ₄ : σ₄ ≠ 0)
    (S₃ : Tensor d 3) (S₄ : Tensor d 4) (z : Vec (jointDim d)) (x : Vec d) (i : Fin d) :
    rowResponse (jointRows σ₃ σ₄ x)
      (normalizedSignal σ₃ σ₄ (tensorCoordinates d 3 S₃) (tensorCoordinates d 4 S₄) + z)
        (Fin.natAdd d i) =
      channel 4 (S₄ + σ₄ • gaussianTensor d 4
        (splitLinearEquiv (cubicDim d) (quarticDim d) z).2) x i := by
  rw [jointResponse_right]
  have h := congrArg (gaussianTensor d 4)
    (normalizedSignal_right σ₃ σ₄ (tensorCoordinates d 3 S₃) (tensorCoordinates d 4 S₄) z hσ₄)
  simp only [gaussianTensor, map_smul, map_add, LinearIsometryEquiv.symm_apply_apply] at h
  have he : σ₄ • gaussianTensor d 4
      (splitLinearEquiv (cubicDim d) (quarticDim d)
        (normalizedSignal σ₃ σ₄ (tensorCoordinates d 3 S₃) (tensorCoordinates d 4 S₄) + z)).2 =
      S₄ + σ₄ • gaussianTensor d 4 (splitLinearEquiv (cubicDim d) (quarticDim d) z).2 := by
    simpa only [gaussianTensor, map_add] using h
  rw [← he, channel_smul]
  rfl

end MatchingBounds1005.TensorChannelRows
