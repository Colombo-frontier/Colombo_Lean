import MatchingBounds1005.SourceReferenceProgram
import MatchingBounds1005.AnalyticOracle
import MatchingBounds1005.SourcePowerGeometry
import MatchingBounds1005.SignalCalibration

/-! The accessible reference program instantiated with the actual calibrated
copied chain, its canonical coordinates, and the source Gaussian variances. -/
noncomputable section
open scoped InnerProductSpace

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration PathGreen BlockGeometry PathLayers TensorGeometry

def referenceParameters (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ) :
    SourceReferenceProgram.Parameters (dimension p t K) (phaseCount (amplitudeConstant p) t - 1 + 1) where
  Q := (sourceGeometry p t ht hs).transportedOperator (phaseCount (amplitudeConstant p) t - 1) K (coordinateIso p t K)
  c := (sourceGeometry p t ht hs).transportedLinearVector (phaseCount (amplitudeConstant p) t - 1) K (coordinateIso p t K)
  b := sourceReadouts p t ht hs K (coordinateIso p t K)
  disclosure i := (i.val + 1) * ((pathEdges (pathScale (amplitudeConstant p) (scale p) t) + 2) / 2)
  τ := (sourceGeometry p t ht hs).tau
  r := amplitude (amplitudeConstant p) t
  a := amplitude (amplitudeConstant p) t
  σ₃ := maskSigma (dimension p t K) 3 ((t ^ 3) ^ 3 / 8)
  σ₄ := maskSigma (dimension p t K) 4 ((t ^ 3) ^ 4 / 8)
  R := (t ^ 3)⁻¹
  η := 4 * (t ^ 3) ^ 2

def referenceLayer (p : ℕ) (t : ℝ) (K : ℕ) :=
  ambientLayerSpace (pathEdges (pathScale (amplitudeConstant p) (scale p) t))
    (phaseCount (amplitudeConstant p) t - 1) K
    ((pathEdges (pathScale (amplitudeConstant p) (scale p) t) + 2) / 2)

theorem referenceLayer_mono (p : ℕ) (t : ℝ) (K : ℕ) : Monotone (referenceLayer p t K) :=
  ambientLayerSpace_mono _ _ _ _

theorem referenceParameters_c_initial (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ) :
    (referenceParameters p t ht hs K).c ∈ referenceLayer p t K 1 :=
  actual_linearVector_initial_calendar (scale p) (pathScale (amplitudeConstant p) (scale p) t)
    (amplitude (amplitudeConstant p) t) (scale_pos p)
    (pathScale_pos _ _ _ (amplitudeConstant_pos p) (scale_pos p) ht) (path_small p ht hs)
    (amplitude_pos _ _ (amplitudeConstant_pos p) ht) _ K

theorem referenceParameters_b_disclosed (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ)
    (i : Fin (phaseCount (amplitudeConstant p) t - 1 + 1)) :
    (referenceParameters p t ht hs K).b i ∈
      referenceLayer p t K ((referenceParameters p t ht hs K).disclosure i) :=
  normalized_ambientReadout_disclosed _ _ _ _ _ i le_rfl

theorem referenceParameters_b_hidden (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K j : ℕ)
    (i : Fin (phaseCount (amplitudeConstant p) t - 1 + 1))
    (hj : j < (referenceParameters p t ht hs K).disclosure i) :
    (referenceParameters p t ht hs K).b i ∈ (referenceLayer p t K j)ᗮ :=
  normalized_ambientReadout_hidden _ _ _ _ _ i hj

theorem referenceParameters_Q_propagation (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K j : ℕ) :
    (referenceLayer p t K j).map (referenceParameters p t ht hs K).Q.toLinearMap ≤
      referenceLayer p t K (j + 1) :=
  actual_ambient_layer_propagation (scale p) (pathScale (amplitudeConstant p) (scale p) t)
    (amplitude (amplitudeConstant p) t) (scale_pos p)
    (pathScale_pos _ _ _ (amplitudeConstant_pos p) (scale_pos p) ht) (path_small p ht hs)
    (amplitude_pos _ _ (amplitudeConstant_pos p) ht) _ K j

theorem referenceParameters_sigmas_pos (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ) :
    0 < (referenceParameters p t ht hs K).σ₃ ∧ 0 < (referenceParameters p t ht hs K).σ₄ :=
  ⟨source_maskSigma_pos (dimension_pos p t ht hs K) (by norm_num) (by positivity),
    source_maskSigma_pos (dimension_pos p t ht hs K) (by norm_num) (by positivity)⟩

theorem referenceParameters_readouts_orthonormal (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hs : t ≤ parameterThreshold p) (K : ℕ) :
    Orthonormal ℝ (referenceParameters p t ht hs K).b :=
  transportedReadout_orthonormal _ _ (amplitude_pos _ _ (amplitudeConstant_pos p) ht)
    (suffixVector_norm _ (amplitude_pos _ _ (amplitudeConstant_pos p) ht).le _) _

end MatchingBounds1005.AnalyticFamily
