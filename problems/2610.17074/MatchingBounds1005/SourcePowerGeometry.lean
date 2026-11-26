import MatchingBounds1005.PowerGeometry
import MatchingBounds1005.SourceGeometry

/-! One policy-independent geometric calibration for the actual p-dependent
family, including both exact-core and terminal stationarity thresholds. -/
noncomputable section
open scoped InnerProductSpace

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration PathGreen BlockGeometry GaussianMatrix GaussianBlockGeometry

def baseSize (p : ℕ) (t : ℝ) : ℕ :=
  phaseCount (amplitudeConstant p) t * pathSize (pathScale (amplitudeConstant p) (scale p) t)

def maximalStarts (p : ℕ) (t : ℝ) : ℕ := 12 * baseSize p t + 6

def sourceAngle (p : ℕ) (t : ℝ) : ℝ := geometricAngle (baseSize p t) (maximalStarts p t) t

def geometryThreshold (p : ℕ) : ℝ :=
  min (parameterThreshold p) (min (1 / 2)
    (min (1 / (4 * angleConstant (horizonUpper p)))
      (64 / (angleConstant (horizonUpper p) * RadialHigher.baseBudget p ^ 2))))

theorem geometryThreshold_pos (p : ℕ) : 0 < geometryThreshold p := by
  have hp := parameterThreshold_pos p
  have hC := angleConstant_pos (horizonUpper_pos p)
  have hb := RadialHigher.baseBudget_pos p
  unfold geometryThreshold
  positivity

theorem geometryThreshold_le_parameter (p : ℕ) : geometryThreshold p ≤ parameterThreshold p :=
  min_le_left _ _

theorem geometryThreshold_requirements (p : ℕ) {t : ℝ} (hsmall : t ≤ geometryThreshold p) :
    t ≤ parameterThreshold p ∧ t ≤ 1 / 2 ∧
      t ≤ 1 / (4 * angleConstant (horizonUpper p)) ∧
      t ≤ 64 / (angleConstant (horizonUpper p) * RadialHigher.baseBudget p ^ 2) := by
  have ha := hsmall.trans (min_le_left _ _)
  have hb := hsmall.trans (min_le_right _ _)
  have hc := hb.trans (min_le_right _ _)
  exact ⟨ha, hb.trans (min_le_left _ _), hc.trans (min_le_left _ _), hc.trans (min_le_right _ _)⟩

theorem baseSize_eq_baseDimension (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) :
    baseDimension (E := EuclideanSpace ℝ
      (Fin (pathEdges (pathScale (amplitudeConstant p) (scale p) t) + 1)))
      (phaseCount (amplitudeConstant p) t - 1) = baseSize p t := by
  rw [PathLayers.source_base_dimension, Nat.sub_add_cancel (phase_pos p ht hsmall),
    (ceiling_scale _ (pathScale_pos _ _ _ (amplitudeConstant_pos p) (scale_pos p) ht)
      (path_small p ht hsmall)).1]
  rfl

theorem baseSize_pos (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p) :
    0 < baseSize p t := by
  have h := dimension_pos p t ht hsmall 0
  rw [dimension_eq p t ht hsmall, zero_add, one_mul] at h
  exact h

theorem baseSize_upper (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p) :
    (baseSize p t : ℝ) ≤ horizonUpper p / t ^ 5 := by
  have h := (horizon_bounds p t ht hsmall).2
  rwa [cube_rate ht, mul_one_div] at h

theorem sourceAngle_bound (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ geometryThreshold p) : sourceAngle p t ^ 2 ≤ angleConstant (horizonUpper p) * t ^ 37 := by
  have hp := hsmall.trans (geometryThreshold_le_parameter p)
  exact geometricAngle_bound (baseSize_pos p t ht hp) (horizonUpper_pos p) ht
    (hp.trans (parameterThreshold_le_one p)) (baseSize_upper p t ht hp) le_rfl

theorem sourceAngle_half (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ geometryThreshold p) : sourceAngle p t ≤ 1 / 2 := by
  obtain ⟨hp, hhalf, hC, hb⟩ := geometryThreshold_requirements p hsmall
  exact geometricAngle_half (baseSize_pos p t ht hp) (horizonUpper_pos p) ht
    (hp.trans (parameterThreshold_le_one p)) (baseSize_upper p t ht hp) le_rfl hC

/-- Both source thresholds hold for every smaller t, uniformly in all queries. -/
theorem sourceAngle_readout_thresholds (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ geometryThreshold p) :
    2 * sourceAngle p t / t ^ 3 ≤ 1 ∧
      2 * sourceAngle p t / t ^ 3 ≤ 16 * t ^ 3 / RadialHigher.baseBudget p := by
  obtain ⟨hp, hhalf, hCsmall, hbsmall⟩ := geometryThreshold_requirements p hsmall
  have ht1 := hp.trans (parameterThreshold_le_one p)
  have hC := angleConstant_pos (horizonUpper_pos p)
  have hb := RadialHigher.baseBudget_pos p
  have hη := sourceAngle_bound p t ht hsmall
  have hη0 : 0 ≤ sourceAngle p t := geometricAngle_nonneg _ _ _
  have hcore := (le_div_iff₀ (by positivity : 0 < 4 * angleConstant (horizonUpper p))).mp hCsmall
  have ht30 : t ^ 30 ≤ 1 := pow_le_one₀ ht.le ht1
  have hcore31 : 4 * angleConstant (horizonUpper p) * t ^ 31 ≤ 1 := by
    have h := mul_le_mul hcore ht30 (by positivity : 0 ≤ t ^ 30) (by norm_num : (0 : ℝ) ≤ 1)
    convert h using 1 <;> ring
  have hcore37 : 4 * angleConstant (horizonUpper p) * t ^ 37 ≤ t ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hcore31 (by positivity : 0 ≤ t ^ 6)
    convert h using 1 <;> ring
  have hcore' : 2 * sourceAngle p t ≤ t ^ 3 := by
    nlinarith only [hη, hcore37, hη0, (by positivity : 0 < t ^ 3)]
  constructor
  · exact (div_le_iff₀ (pow_pos ht 3)).mpr (by simpa only [one_mul] using hcore')
  · have hcert := (le_div_iff₀ (by positivity :
        0 < angleConstant (horizonUpper p) * RadialHigher.baseBudget p ^ 2)).mp hbsmall
    have ht24 : t ^ 24 ≤ 1 := pow_le_one₀ ht.le ht1
    have hcert25 : angleConstant (horizonUpper p) * RadialHigher.baseBudget p ^ 2 * t ^ 25 ≤ 64 := by
      have h := mul_le_mul hcert ht24 (by positivity : 0 ≤ t ^ 24) (by norm_num : (0 : ℝ) ≤ 64)
      convert h using 1 <;> ring
    have hcert37 : angleConstant (horizonUpper p) * RadialHigher.baseBudget p ^ 2 * t ^ 37 ≤ 64 * t ^ 12 := by
      have h := mul_le_mul_of_nonneg_right hcert25 (by positivity : 0 ≤ t ^ 12)
      convert h using 1 <;> ring
    have hηb := mul_le_mul_of_nonneg_left hη (sq_nonneg (RadialHigher.baseBudget p))
    have hcert' : RadialHigher.baseBudget p * sourceAngle p t ≤ 8 * t ^ 6 := by
      nlinarith only [hηb, hcert37, mul_nonneg hb.le hη0, (by positivity : 0 < t ^ 6)]
    apply (le_div_iff₀ hb).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos ht 3)).mpr
    nlinarith only [hcert']

theorem source_dimension_room (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ geometryThreshold p) (k : ℕ) (hk : k ≤ maximalStarts p t) :
    k ≤ dimension p t (powerCopies t) := by
  obtain ⟨hp, hhalf, hC, hb⟩ := geometryThreshold_requirements p hsmall
  have hD := baseSize_pos p t ht hp
  rw [dimension_eq p t ht hp]
  change k ≤ (powerCopies t + 1) * baseSize p t
  have hK := powerCopies_large ht hhalf
  have hm : 19 * baseSize p t ≤ (powerCopies t + 1) * baseSize p t := Nat.mul_le_mul_right _ (by omega)
  change k ≤ 12 * baseSize p t + 6 at hk
  omega

def canonicalGeometry (p : ℕ) (t : ℝ) (ht : 0 < t) (hp : t ≤ parameterThreshold p) :=
  geometry (amplitudeConstant p) (scale p) t (amplitudeConstant_pos p) (scale_pos p) ht (path_small p ht hp)

def canonicalOperator (p : ℕ) (t : ℝ) (ht : 0 < t) (hp : t ≤ parameterThreshold p) :
    GaussianVector.Vec (dimension p t (powerCopies t)) →L[ℝ] GaussianVector.Vec (dimension p t (powerCopies t)) :=
  (canonicalGeometry p t ht hp).copyAmbientOperator (phaseCount (amplitudeConstant p) t - 1) (powerCopies t)

def canonicalActive (p : ℕ) (t : ℝ) : Submodule ℝ (GaussianVector.Vec (dimension p t (powerCopies t))) :=
  copyAmbientActiveSpace (E := EuclideanSpace ℝ
    (Fin (pathEdges (pathScale (amplitudeConstant p) (scale p) t) + 1)))
    (phaseCount (amplitudeConstant p) t - 1) (powerCopies t)

theorem source_cyclic_angle_failure (p : ℕ) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ geometryThreshold p) (k : ℕ) (hk : k ≤ maximalStarts p t) :
    let hp := hsmall.trans (geometryThreshold_le_parameter p)
    (gaussianMatrixLaw (dimension p t (powerCopies t)) k).real
      {g | ¬ CyclicAngleGood (canonicalActive p t) (canonicalOperator p t ht hp) g (sourceAngle p t)} ≤
        1 / (powerCopies t : ℝ) ^ 4 := by
  dsimp only
  let hp := hsmall.trans (geometryThreshold_le_parameter p)
  have hD := baseSize_pos p t ht hp
  have hmul := geometricAngle_multiplicity (k := maximalStarts p t) hD ht
  have hk' : (k : ℝ) ≤ maximalStarts p t := by exact_mod_cast hk
  have hmul' : 96 * ((k : ℝ) + 1) + 32 * confidenceExponent (baseSize p t) t ≤
      ((powerCopies t + 1 : ℕ) : ℝ) * sourceAngle p t ^ 2 := by
    change _ ≤ ((powerCopies t + 1 : ℕ) : ℝ) * geometricAngle (baseSize p t) (maximalStarts p t) t ^ 2
    nlinarith only [hmul, hk']
  have h := (canonicalGeometry p t ht hp).chain_copy_high_multiplicity
    (phaseCount (amplitudeConstant p) t - 1) (powerCopies t) k
    (geometricAngle_nonneg _ _ _) (sourceAngle_half p t ht hsmall)
    (confidenceExponent_nonneg hD ht) hmul'
  rw [baseSize_eq_baseDimension p t ht hp, confidence_failure_exact hD ht] at h
  exact h

end MatchingBounds1005.AnalyticFamily
