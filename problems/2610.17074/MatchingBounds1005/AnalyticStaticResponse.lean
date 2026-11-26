import MatchingBounds1005.AnalyticReferenceRotation
import MatchingBounds1005.SourceStaticResponse

/-! The reference compiler's held static Gaussian response is exactly the
concrete sampled family reply, with the manuscript's physical mask scales. -/
noncomputable section
open RandomizedFO2003.Rotations
namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry SourceReferenceProgram SourceReferenceReplay
open TensorChannelRows GaussianBlockProjection BlockGeometry

theorem directResponse_eq_sourceReply (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ)
    (U : Rotation (Vec (dimension p t K))) (z : Vec (jointDim (dimension p t K)))
    (j : ℕ) (x : Vec (dimension p t K)) :
    directResponse (referenceParameters p t ht hs K) (rotationMap _ U) z j x =
      sourceReply p t ht hs K (rotationIso p t K U)
        (maskSigma (dimension p t K) 3 ((t ^ 3) ^ 3 / 8) •
          gaussianTensor _ 3 (splitLinearEquiv (cubicDim _) (quarticDim _) z).1)
        (maskSigma (dimension p t K) 4 ((t ^ 3) ^ 4 / 8) •
          gaussianTensor _ 4 (splitLinearEquiv (cubicDim _) (quarticDim _) z).2)
        (Finset.univ.filter (fun i => (referenceParameters p t ht hs K).disclosure i ≤ j + 1)) x := by
  simp only [directResponse, cubicTensor, quarticTensor, referenceParameters_rotated_b,
    referenceParameters_rotated_c, referenceParameters_rotated_Q,
    sourceReply, sourceResponse, decoyDataResponse, Fintype.card_fin]
  rfl

end MatchingBounds1005.AnalyticFamily
