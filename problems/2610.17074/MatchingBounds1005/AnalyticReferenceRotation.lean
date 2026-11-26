import MatchingBounds1005.AnalyticReferenceParameters
import MatchingBounds1005.ReferenceRotationInputs

/-! All source-program parameter conditions and physical rotation identities
are proved for the calibrated family. -/
noncomputable section
open RandomizedFO2003.Rotations
namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry BlockGeometry SourceReferenceProgram

theorem referenceParameters_disclosure_pos (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ)
    (i : Fin (phaseCount (amplitudeConstant p) t - 1 + 1)) :
    0 < (referenceParameters p t ht hs K).disclosure i := by
  apply Nat.mul_pos (by omega)
  omega

theorem referenceParameters_core (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ) : 1 ≤ (referenceParameters p t ht hs K).r :=
  amplitude_ge_one _ _ ht (parameter_requirements p ht hs).1

theorem referenceParameters_rotated_b (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ) (U : Rotation (Vec (dimension p t K)))
    (i : Fin (phaseCount (amplitudeConstant p) t - 1 + 1)) :
    rotationMap _ U ((referenceParameters p t ht hs K).b i) =
      sourceReadouts p t ht hs K (rotationIso p t K U) i := rfl

theorem referenceParameters_rotated_c (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ) (U : Rotation (Vec (dimension p t K))) :
    rotationMap _ U (referenceParameters p t ht hs K).c =
      (sourceGeometry p t ht hs).transportedLinearVector
        (phaseCount (amplitudeConstant p) t - 1) K (rotationIso p t K U) := rfl

theorem referenceParameters_rotated_Q (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ) (U : Rotation (Vec (dimension p t K)))
    (x : Vec (dimension p t K)) :
    rotationMap _ U ((referenceParameters p t ht hs K).Q ((rotationMap _ U).adjoint x)) =
      (sourceGeometry p t ht hs).transportedOperator
        (phaseCount (amplitudeConstant p) t - 1) K (rotationIso p t K U) x := by
  simp only [rotationMap, LinearIsometryEquiv.adjoint_eq_symm]
  rfl

end MatchingBounds1005.AnalyticFamily
