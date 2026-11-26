import MatchingBounds1005.DecoyConfinement
import MatchingBounds1005.CalibratedChain
import MatchingBounds1005.ChainSpectral

/-! A fixed analytic family for each finite derivative order. Every scalar
parameter is chosen here; the conclusions require only membership in the
actual tensor norm event. No regularity or gradient property is assumed. -/
noncomputable section
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.AnalyticFamily
open EpsilonCalibration PathGreen BlockGeometry TensorGeometry

def primitiveConstant (p : ℕ) : ℝ := (Primitive.finite_order_bounds p).choose

theorem primitiveConstant_nonneg (p : ℕ) : 0 ≤ primitiveConstant p :=
  (Primitive.finite_order_bounds p).choose_spec.1

theorem primitiveConstant_bounds (p q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p)
    (r : ℝ) (hr : 1 ≤ r) (u : ℝ) :
    |iteratedDeriv (q + 1) (Primitive.potential r) u| ≤ primitiveConstant p * r ^ 3 / r ^ q :=
  (Primitive.finite_order_bounds p).choose_spec.2 q hq hqp r hr u

def scale (p : ℕ) : ℝ := RadialHigher.baseBudget p / 16

theorem scale_pos (p : ℕ) : 0 < scale p := div_pos (RadialHigher.baseBudget_pos p) (by norm_num)

theorem scale_budget (p : ℕ) : 16 * scale p = RadialHigher.baseBudget p := by unfold scale; ring

def amplitudeConstant (p : ℕ) : ℝ := coreAmplitude (scale p) (primitiveConstant p)

theorem amplitudeConstant_pos (p : ℕ) : 0 < amplitudeConstant p :=
  coreAmplitude_pos (scale_pos p) _

theorem nonlinear_budget (p : ℕ) :
    18 * 8192 * primitiveConstant p * amplitudeConstant p ^ 3 ≤ 4 * scale p :=
  (coreAmplitude_budget (scale_pos p) (primitiveConstant_nonneg p)).trans (by linarith [scale_pos p])

def parameterThreshold (p : ℕ) : ℝ :=
  min (smallThreshold (amplitudeConstant p) (scale p)) (RadialHigher.accuracyThreshold p)

theorem parameterThreshold_pos (p : ℕ) : 0 < parameterThreshold p :=
  lt_min (smallThreshold_pos (amplitudeConstant_pos p) (scale_pos p))
    (RadialHigher.accuracyThreshold_pos p)

theorem parameter_requirements (p : ℕ) {t : ℝ} (ht : 0 < t) (hsmall : t ≤ parameterThreshold p) :
    t ≤ amplitudeConstant p ∧ pathScale (amplitudeConstant p) (scale p) t ≤ 1 / 37 ∧
      10368 * 8192 * t ^ 4 ≤ amplitudeConstant p ∧
      t ^ 3 ≤ RadialHigher.accuracyThreshold p := by
  obtain ⟨hr, hp, hg⟩ := smallThreshold_requirements (amplitudeConstant_pos p) (scale_pos p) ht
    (hsmall.trans (min_le_left _ _))
  have htδ : t ≤ RadialHigher.accuracyThreshold p := hsmall.trans (min_le_right _ _)
  have ht1 := htδ.trans (RadialHigher.accuracyThreshold_le_one p)
  have hs : t ^ 2 ≤ 1 := pow_le_one₀ ht.le ht1
  have ht3 : t ^ 3 ≤ t := by nlinarith only [mul_le_mul_of_nonneg_left hs ht.le]
  exact ⟨hr, hp, hg, ht3.trans htδ⟩

theorem path_small (p : ℕ) {t : ℝ} (ht : 0 < t) (hsmall : t ≤ parameterThreshold p) :
    pathScale (amplitudeConstant p) (scale p) t ≤ 1 / 4 :=
  (parameter_requirements p ht hsmall).2.1.trans (by norm_num)

theorem phase_pos (p : ℕ) {t : ℝ} (ht : 0 < t) (hsmall : t ≤ parameterThreshold p) :
    1 ≤ phaseCount (amplitudeConstant p) t := by
  apply phaseCount_pos _ _ ht
  have hg := (parameter_requirements p ht hsmall).2.2.1
  nlinarith only [hg, (by positivity : 0 ≤ t ^ 4)]

abbrev Copy (p : ℕ) (t : ℝ) (K : ℕ) := CalibratedCopySpace (amplitudeConstant p) (scale p) t K

def dimension (p : ℕ) (t : ℝ) (K : ℕ) : ℕ :=
  copyDimension (E := EuclideanSpace ℝ
    (Fin (pathEdges (pathScale (amplitudeConstant p) (scale p) t) + 1)))
    (phaseCount (amplitudeConstant p) t - 1) K

def coordinateIso (p : ℕ) (t : ℝ) (K : ℕ) : Copy p t K ≃ₗᵢ[ℝ] Vec (dimension p t K) :=
  (copyEuclideanIso _ _).symm

def objective (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) : Vec d → ℝ :=
  confinedDecoy (amplitudeConstant p) (scale p) t (amplitudeConstant_pos p) (scale_pos p)
    ht (path_small p ht hsmall) K I T₃ T₄

def tail (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d) : Vec d :=
  transportedTail (amplitudeConstant p) (scale p) t (amplitudeConstant_pos p) (scale_pos p)
    ht (path_small p ht hsmall) K I

theorem objective_inFunctionClass (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    (h3 : ‖tensorForm T₃‖ ≤ (t ^ 3) ^ 3 / 8)
    (h4 : ‖tensorForm T₄‖ ≤ (t ^ 3) ^ 4 / 8) :
    Model.InFunctionClass p (objective p t ht hsmall K I T₃ T₄) := by
  obtain ⟨hr, hp, hg, he⟩ := parameter_requirements p ht hsmall
  exact confinedDecoy_inFunctionClass (amplitudeConstant p) (scale p) t
    (amplitudeConstant_pos p) (scale_pos p) ht (path_small p ht hsmall)
    p (primitiveConstant p) (primitiveConstant_nonneg p) (primitiveConstant_bounds p)
    (nonlinear_budget p) hr hp (phase_pos p ht hsmall) hg (scale_budget p).le he K I T₃ T₄ h3 h4

theorem objective_stationarity (p : ℕ) (hp : 1 ≤ p) (t : ℝ) (ht : 0 < t)
    (hsmall : t ≤ parameterThreshold p) (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    (h3 : ‖tensorForm T₃‖ ≤ (t ^ 3) ^ 3 / 8)
    (h4 : ‖tensorForm T₄‖ ≤ (t ^ 3) ^ 4 / 8) (x : Vec d)
    (hread : |⟪tail p t ht hsmall K I, radial (t ^ 3)⁻¹ x⟫_ℝ| ≤
      16 * t ^ 3 / RadialHigher.baseBudget p) :
    t ^ 3 < ‖gradient (objective p t ht hsmall K I T₃ T₄) x‖ := by
  obtain ⟨hr, hpath, hg, he⟩ := parameter_requirements p ht hsmall
  apply confinedDecoy_stationarity (amplitudeConstant p) (scale p) t
    (amplitudeConstant_pos p) (scale_pos p) ht (path_small p ht hsmall)
    p (primitiveConstant p) (primitiveConstant_nonneg p) (primitiveConstant_bounds p)
    (nonlinear_budget p) hr hpath hp (phase_pos p ht hsmall) hg K I T₃ T₄ h3 h4 x
  simpa only [scale_budget] using hread

theorem objective_smooth (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p t K ≃ₗᵢ[ℝ] Vec d) (T₃ : Tensor d 3) (T₄ : Tensor d 4) :
    ContDiff ℝ ∞ (objective p t ht hsmall K I T₃ T₄) :=
  confined_mask_smooth (transportedDecoy_smooth _ _ _ _ _ _ _ K I) T₃ T₄ _ _

def horizonLower (p : ℕ) : ℝ :=
  amplitudeConstant p / (2880 * 8192 * Real.sqrt (8192 * amplitudeConstant p / scale p))

def horizonUpper (p : ℕ) : ℝ :=
  amplitudeConstant p / (720 * 8192 * Real.sqrt (8192 * amplitudeConstant p / scale p))

theorem horizonLower_pos (p : ℕ) : 0 < horizonLower p := by
  have ha := amplitudeConstant_pos p
  have hL := scale_pos p
  unfold horizonLower
  positivity

theorem horizonUpper_pos (p : ℕ) : 0 < horizonUpper p := by
  have ha := amplitudeConstant_pos p
  have hL := scale_pos p
  unfold horizonUpper
  positivity

theorem horizon_bounds (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p) :
    horizonLower p * Model.rate (t ^ 3) ≤
      ((phaseCount (amplitudeConstant p) t * pathSize (pathScale (amplitudeConstant p) (scale p) t) : ℕ) : ℝ) ∧
    ((phaseCount (amplitudeConstant p) t * pathSize (pathScale (amplitudeConstant p) (scale p) t) : ℕ) : ℝ) ≤
      horizonUpper p * Model.rate (t ^ 3) := by
  obtain ⟨hr, hp, hg, he⟩ := parameter_requirements p ht hsmall
  have hphase : 2880 * 8192 * t ^ 4 ≤ amplitudeConstant p := by
    nlinarith only [hg, (by positivity : 0 ≤ t ^ 4)]
  obtain ⟨hlo, hup⟩ := horizon_power_bounds (amplitudeConstant p) (scale p) t
    (amplitudeConstant_pos p) (scale_pos p) ht hphase (hp.trans (by norm_num))
  rw [cube_rate ht]
  constructor
  · rw [mul_one_div]
    exact (div_le_iff₀ (pow_pos ht 5)).mpr hlo
  · rw [mul_one_div]
    exact (le_div_iff₀ (pow_pos ht 5)).mpr hup

/-- A literal positive accuracy threshold, valid for every smaller ε. -/
def accuracyThreshold (p : ℕ) : ℝ := parameterThreshold p ^ 3

theorem accuracyThreshold_pos (p : ℕ) : 0 < accuracyThreshold p := pow_pos (parameterThreshold_pos p) 3

theorem accuracy_parameters (p : ℕ) {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold p) :
    0 < accuracyParameter ε ∧ accuracyParameter ε ≤ parameterThreshold p ∧
      accuracyParameter ε ^ 3 = ε :=
  ⟨accuracyParameter_pos hε,
    accuracyParameter_small hε.le (parameterThreshold_pos p).le hsmall,
    accuracyParameter_cube hε.le⟩

theorem dimension_eq (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p) (K : ℕ) :
    dimension p t K = (K + 1) * (phaseCount (amplitudeConstant p) t *
      pathSize (pathScale (amplitudeConstant p) (scale p) t)) := by
  unfold dimension
  rw [copyDimension_eq]
  congr 1
  unfold baseDimension
  rw [(WithLp.linearEquiv 2 ℝ (Fin (phaseCount (amplitudeConstant p) t - 1 + 1) →
    EuclideanSpace ℝ (Fin (pathEdges (pathScale (amplitudeConstant p) (scale p) t) + 1)))).finrank_eq]
  simp only [Module.finrank_pi_fintype]
  simp only [finrank_euclideanSpace_fin, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Nat.sub_add_cancel (phase_pos p ht hsmall)]
  rw [(ceiling_scale _ (pathScale_pos _ _ _ (amplitudeConstant_pos p) (scale_pos p) ht)
    (path_small p ht hsmall)).1]

theorem dimension_bounds (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p) (K : ℕ) :
    ((K + 1 : ℕ) : ℝ) * (horizonLower p * Model.rate (t ^ 3)) ≤ (dimension p t K : ℝ) ∧
      (dimension p t K : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * (horizonUpper p * Model.rate (t ^ 3)) := by
  rw [dimension_eq p t ht hsmall, Nat.cast_mul]
  obtain ⟨hl, hu⟩ := horizon_bounds p t ht hsmall
  exact ⟨mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _),
    mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _)⟩

theorem dimension_pos (p : ℕ) (t : ℝ) (ht : 0 < t) (hsmall : t ≤ parameterThreshold p) (K : ℕ) :
    0 < dimension p t K := by
  rw [dimension_eq p t ht hsmall]
  have hN := phase_pos p ht hsmall
  have hM := (ceiling_scale _ (pathScale_pos _ _ _ (amplitudeConstant_pos p) (scale_pos p) ht)
    (path_small p ht hsmall)).1
  exact Nat.mul_pos (Nat.succ_pos K) (Nat.mul_pos (by omega) (by omega))

def accuracyObjective (p : ℕ) (ε : ℝ) (hε : 0 < ε) (hsmall : ε ≤ accuracyThreshold p)
    (K : ℕ) {d : ℕ} (I : Copy p (accuracyParameter ε) K ≃ₗᵢ[ℝ] Vec d)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) : Vec d → ℝ :=
  objective p (accuracyParameter ε) (accuracy_parameters p hε hsmall).1
    (accuracy_parameters p hε hsmall).2.1 K I T₃ T₄

theorem accuracyObjective_inFunctionClass (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold p) (K : ℕ) {d : ℕ}
    (I : Copy p (accuracyParameter ε) K ≃ₗᵢ[ℝ] Vec d) (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    (h3 : ‖tensorForm T₃‖ ≤ ε ^ 3 / 8) (h4 : ‖tensorForm T₄‖ ≤ ε ^ 4 / 8) :
    Model.InFunctionClass p (accuracyObjective p ε hε hsmall K I T₃ T₄) := by
  apply objective_inFunctionClass
  · simpa only [accuracyParameter_cube hε.le] using h3
  · simpa only [accuracyParameter_cube hε.le] using h4

theorem accuracy_horizon_bounds (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyThreshold p) :
    horizonLower p * Model.rate ε ≤
      ((phaseCount (amplitudeConstant p) (accuracyParameter ε) *
        pathSize (pathScale (amplitudeConstant p) (scale p) (accuracyParameter ε)) : ℕ) : ℝ) ∧
    ((phaseCount (amplitudeConstant p) (accuracyParameter ε) *
      pathSize (pathScale (amplitudeConstant p) (scale p) (accuracyParameter ε)) : ℕ) : ℝ) ≤
        horizonUpper p * Model.rate ε := by
  simpa only [accuracyParameter_cube hε.le] using
    horizon_bounds p (accuracyParameter ε) (accuracy_parameters p hε hsmall).1
      (accuracy_parameters p hε hsmall).2.1

end MatchingBounds1005.AnalyticFamily
