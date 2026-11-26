import MatchingBounds1005.AnalyticSampling
import MatchingBounds1005.DecoyOracle
import MatchingBounds1005.OracleFirstExit

/-! Exact first-exit coupling for the concrete calibrated Haar/Gaussian family.
The output is not required to be a previous query. -/
noncomputable section
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration PathGreen BlockGeometry TensorGeometry

def sourceGeometry (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) :=
  geometry (amplitudeConstant p) (scale p) t (amplitudeConstant_pos p) (scale_pos p) ht
    (path_small p ht hs)

def sourceReadouts (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d) :=
  transportedReadout (phaseCount (amplitudeConstant p) t - 1) K
    (sourceGeometry p t ht hs).a (amplitude (amplitudeConstant p) t) I

def sourceCubic (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d) : Tensor d 3 :=
  cubicSignal (sourceGeometry p t ht hs).tau (amplitude (amplitudeConstant p) t)
    (sourceReadouts p t ht hs K I)

def sourceQuartic (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d) : Tensor d 4 :=
  quarticSignal (sourceGeometry p t ht hs).tau (amplitude (amplitudeConstant p) t)
    (sourceReadouts p t ht hs K I)

def sourceResponse (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d)
    (S : Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1)))
    (x Y₃ Y₄ : Vec d) : Model.Response d :=
  (sourceGeometry p t ht hs).decoyDataResponse
    (amplitude (amplitudeConstant p) t) (amplitude (amplitudeConstant p) t)
    (t ^ 3)⁻¹ (4 * (t ^ 3) ^ 2) (phaseCount (amplitudeConstant p) t - 1) K I S x Y₃ Y₄

def sourceReply (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    (S : Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1))) (x : Vec d) : Model.Response d :=
  sourceResponse p t ht hs K I S x
    (channel 3 (sourceCubic p t ht hs K I + T₃) (radial (t ^ 3)⁻¹ x))
    (channel 4 (sourceQuartic p t ht hs K I + T₄) (radial (t ^ 3)⁻¹ x))

theorem sourceReply_exact (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    (S : Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1))) (x : Vec d)
    (hcore : ∀ i, i ∉ S → |⟪sourceReadouts p t ht hs K I i, radial (t ^ 3)⁻¹ x⟫_ℝ| ≤ 1) :
    Model.oracle (objective p t ht hs K I T₃ T₄) x = sourceReply p t ht hs K I T₃ T₄ S x := by
  apply (sourceGeometry p t ht hs).decoyDataResponse_exact
    (amplitude_ge_one _ _ ht (parameter_requirements p ht hs).1)
    (amplitude_pos _ _ (amplitudeConstant_pos p) ht)
  intro i hi
  rw [abs_mul, abs_of_pos (amplitude_pos _ _ (amplitudeConstant_pos p) ht)]
  exact (mul_le_mul_of_nonneg_left (hcore i hi)
    (amplitude_pos _ _ (amplitudeConstant_pos p) ht).le).trans_eq (mul_one _)

def sampledReply {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (z : Sample p t K) (A : Model.Algorithm (dimension p t K) Seed)
    (S : ℕ → Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1)))
    (j : ℕ) (seed : Seed) (h : Fin j → Model.Response (dimension p t K)) :=
  sourceReply p t ht hs K (rotationIso p t K z.1)
    (scaledGaussianTensor (dimension p t K) 3 ((t ^ 3) ^ 3 / 8) z.2.1)
    (scaledGaussianTensor (dimension p t K) 4 ((t ^ 3) ^ 4 / 8) z.2.2) (S j)
    (A.query j seed h)

def querySafe {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (z : Sample p t K) (A : Model.Algorithm (dimension p t K) Seed)
    (S : ℕ → Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1)))
    (j : ℕ) (seed : Seed) (h : Fin j → Model.Response (dimension p t K)) : Prop :=
  ∀ i, i ∉ S j → |⟪sourceReadouts p t ht hs K (rotationIso p t K z.1) i,
    radial (t ^ 3)⁻¹ (A.query j seed h)⟫_ℝ| ≤ 1

def outputSafe {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (z : Sample p t K) (A : Model.Algorithm (dimension p t K) Seed)
    (T : ℕ) (seed : Seed) (h : Fin T → Model.Response (dimension p t K)) : Prop :=
  |⟪tail p t ht hs K (rotationIso p t K z.1), radial (t ^ 3)⁻¹ (A.output T seed h)⟫_ℝ| ≤
    16 * t ^ 3 / RadialHigher.baseBudget p

theorem sampled_success_subset_firstExit {Seed : Type} [MeasurableSpace Seed]
    (p : ℕ) (hp : 1 ≤ p) (t : ℝ) (ht : 0 < t) (hs : t ≤ parameterThreshold p) (K : ℕ)
    (z : Sample p t K) (hz : z ∈ Good p t K) (A : Model.Algorithm (dimension p t K) Seed)
    (S : ℕ → Finset (Fin (phaseCount (amplitudeConstant p) t - 1 + 1))) (T : ℕ) :
    Model.Success A (sampledObjective p t ht hs K z) (t ^ 3) T ⊆
      Model.FirstExit (sampledReply p t ht hs K z A S) (querySafe p t ht hs K z A S)
        (outputSafe p t ht hs K z A T) := by
  apply Model.success_subset_firstExit
  · intro j seed h hsafe
    rw [sampledObjective_eq]
    exact (sourceReply_exact p t ht hs K _ _ _ _ _ hsafe).symm
  · intro seed h hsafe
    exact sampledObjective_stationarity p hp t ht hs K z hz _ hsafe

end MatchingBounds1005.AnalyticFamily
