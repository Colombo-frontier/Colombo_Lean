import MatchingBounds1005.AnalyticFamily
import MatchingBounds1005.MaskSampling

/-! The actual fixed Haar rotation and two independent Gaussian tensors,
with joint oracle measurability and proved analytic support on the source
norm event. The seed law is specified explicitly, before any query. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration TensorGeometry

abbrev Sample (p : ℕ) (t : ℝ) (K : ℕ) :=
  Rotation (Vec (dimension p t K)) × MaskSeed (dimension p t K)

def sampleLaw (p : ℕ) (t : ℝ) (K : ℕ) : Measure (Sample p t K) :=
  (haarLaw (Vec (dimension p t K))).prod (maskLaw (dimension p t K))

instance sampleLaw_probability (p : ℕ) (t : ℝ) (K : ℕ) : IsProbabilityMeasure (sampleLaw p t K) := by
  unfold sampleLaw
  infer_instance

def rotationIso (p : ℕ) (t : ℝ) (K : ℕ) (U : Rotation (Vec (dimension p t K))) :
    Copy p t K ≃ₗᵢ[ℝ] Vec (dimension p t K) :=
  (coordinateIso p t K).trans (isometry _ U)

def rotatedBase (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p)
    (K : ℕ) (U : Rotation (Vec (dimension p t K))) : Vec (dimension p t K) → ℝ :=
  transportedDecoy (amplitudeConstant p) (scale p) t (amplitudeConstant_pos p) (scale_pos p)
    ht (path_small p ht hsmall) K (rotationIso p t K U)

theorem rotatedBase_joint_continuous (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) (K : ℕ) :
    Continuous (rotatedBase p t ht hsmall K).uncurry := by
  have h := IsometricTransfer.continuous_rotated
    (transportedDecoy_smooth (amplitudeConstant p) (scale p) t
      (amplitudeConstant_pos p) (scale_pos p) ht (path_small p ht hsmall) K
      (coordinateIso p t K)).continuous
  exact h

def sampledObjective (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p)
    (K : ℕ) : Sample p t K → Vec (dimension p t K) → ℝ :=
  sampledConfined (rotatedBase p t ht hsmall K) ((t ^ 3) ^ 3 / 8) ((t ^ 3) ^ 4 / 8)
    (t ^ 3)⁻¹ (4 * (t ^ 3) ^ 2)

theorem sampledObjective_eq (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p)
    (K : ℕ) (z : Sample p t K) :
    sampledObjective p t ht hsmall K z = objective p t ht hsmall K (rotationIso p t K z.1)
      (scaledGaussianTensor (dimension p t K) 3 ((t ^ 3) ^ 3 / 8) z.2.1)
      (scaledGaussianTensor (dimension p t K) 4 ((t ^ 3) ^ 4 / 8) z.2.2) := rfl

theorem sampledObjective_joint_continuous (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) (K : ℕ) :
    Continuous (fun z : Sample p t K × Vec (dimension p t K) =>
      sampledObjective p t ht hsmall K z.1 z.2) :=
  sampledConfined_continuous _ (rotatedBase_joint_continuous p t ht hsmall K) _ _ _ _

theorem sampledObjective_oracle_measurable (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) (K : ℕ) :
    Measurable (fun z : Sample p t K × Vec (dimension p t K) =>
      Model.oracle (sampledObjective p t ht hsmall K z.1) z.2) :=
  sampledConfined_oracle_measurable _ (rotatedBase_joint_continuous p t ht hsmall K) _ _ _ _

def Good (p : ℕ) (t : ℝ) (K : ℕ) : Set (Sample p t K) :=
  sampledGood (dimension p t K)

theorem good_measurable (p : ℕ) (t : ℝ) (K : ℕ) : MeasurableSet (Good p t K) :=
  sampledGood_measurable _

theorem good_probability (p : ℕ) (t : ℝ) (K : ℕ) :
    1 - 4 * Real.exp (-4 * dimension p t K) ≤ (sampleLaw p t K).real (Good p t K) :=
  sampledGood_probability (haarLaw (Vec (dimension p t K))) _

theorem good_positive (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p) (K : ℕ) :
    0 < (sampleLaw p t K).real (Good p t K) :=
  sampledGood_positive (haarLaw (Vec (dimension p t K))) (dimension_pos p t ht hsmall K)

/-- The same sample fixes both the Haar rotation and all tensor coefficients;
every sample in the measurable source norm event belongs to the desired class. -/
theorem sampledObjective_inFunctionClass (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) (K : ℕ) (z : Sample p t K) (hz : z ∈ Good p t K) :
    Model.InFunctionClass p (sampledObjective p t ht hsmall K z) := by
  rw [sampledObjective_eq]
  apply objective_inFunctionClass
  · exact scaledGaussianTensor_norm (dimension_pos p t ht hsmall K) (by norm_num)
      (by positivity) hz.1
  · exact scaledGaussianTensor_norm (dimension_pos p t ht hsmall K) (by norm_num)
      (by positivity) hz.2

theorem sampledObjective_stationarity (p : ℕ) (hp : 1 ≤ p) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) (K : ℕ) (z : Sample p t K) (hz : z ∈ Good p t K)
    (x : Vec (dimension p t K))
    (hread : |⟪tail p t ht hsmall K (rotationIso p t K z.1), radial (t ^ 3)⁻¹ x⟫_ℝ| ≤
      16 * t ^ 3 / RadialHigher.baseBudget p) :
    t ^ 3 < ‖gradient (sampledObjective p t ht hsmall K z) x‖ := by
  rw [sampledObjective_eq]
  apply objective_stationarity p hp t ht hsmall
  · exact scaledGaussianTensor_norm (dimension_pos p t ht hsmall K) (by norm_num)
      (by positivity) hz.1
  · exact scaledGaussianTensor_norm (dimension_pos p t ht hsmall K) (by norm_num)
      (by positivity) hz.2
  · exact hread

end MatchingBounds1005.AnalyticFamily
