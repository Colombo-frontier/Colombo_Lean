import Geode.GeodesicLine
import Geode.ContactRealization

/-! Tangent-vector exponential lines and total ambient-input exponential maps. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangentNorm_pos (x : Point E) {v : Ambient E}
    (hv : form E x.val v = 0) (hne : v ≠ 0) : 0 < tangentNorm v :=
  Real.sqrt_pos.mpr (tangent_pos x hv hne)

theorem normalized_tangent_unit (x : Point E) {v : Ambient E}
    (hv : form E x.val v = 0) (hne : v ≠ 0) :
    form E ((tangentNorm v)⁻¹ • v) ((tangentNorm v)⁻¹ • v) = 1 := by
  have hp := tangentNorm_pos x hv hne
  have hs : tangentNorm v ^ 2 = form E v v := Real.sq_sqrt (tangent_nonneg x hv)
  simp only [form_smul_left, form_smul_right]
  rw [← hs]
  field_simp only [ne_of_gt hp]
  ring

noncomputable def exponentialLine (x : Point E) (v : Ambient E)
    (hv : form E x.val v = 0) : GeodesicLine E := by
  classical
  exact if h : v = 0 then GeodesicLine.constant x else
    GeodesicLine.ofUnit x ((tangentNorm v)⁻¹ • v) (by simp [hv])
      (normalized_tangent_unit x hv h) (tangentNorm v)

@[simp] theorem exponentialLine_zero (x : Point E) (v : Ambient E)
    (hv : form E x.val v = 0) : (exponentialLine x v hv).point 0 = x := by
  classical
  unfold exponentialLine
  split_ifs <;> simp [GeodesicLine.constant, GeodesicLine.ofUnit]

@[simp] theorem exponentialLine_velocity_zero (x : Point E) (v : Ambient E)
    (hv : form E x.val v = 0) : (exponentialLine x v hv).velocity 0 = v := by
  classical
  unfold exponentialLine
  split_ifs with h
  · simp [GeodesicLine.constant, h]
  · have hp := tangentNorm_pos x hv h
    simp only [GeodesicLine.ofUnit, rayVelocity, mul_zero, Real.sinh_zero, zero_mul,
      Real.cosh_zero, one_mul, zero_smul, zero_add, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hp), one_smul]

@[simp] theorem exponentialLine_speedSq (x : Point E) (v : Ambient E)
    (hv : form E x.val v = 0) : (exponentialLine x v hv).speedSq = form E v v := by
  classical
  unfold exponentialLine
  split_ifs with h
  · simp [GeodesicLine.constant, h]
  · exact Real.sq_sqrt (tangent_nonneg x hv)

theorem exponentialLine_dist (x : Point E) (v : Ambient E)
    (hv : form E x.val v = 0) (s t : ℝ) :
    dist ((exponentialLine x v hv).point s) ((exponentialLine x v hv).point t) =
      |s - t| * tangentNorm v := by
  classical
  unfold exponentialLine
  split_ifs with h
  · simp [GeodesicLine.constant, h, tangentNorm]
  · dsimp only [GeodesicLine.ofUnit]
    rw [unitGeodesic_dist, ← mul_sub, abs_mul,
      abs_of_nonneg (show 0 ≤ tangentNorm v from Real.sqrt_nonneg _)]
    ring

noncomputable def expMap (x : Point E) (v : Ambient E) (hv : form E x.val v = 0) : Point E :=
  (exponentialLine x v hv).point 1

theorem dist_expMap (x : Point E) (v : Ambient E) (hv : form E x.val v = 0) :
    dist x (expMap x v hv) = tangentNorm v := by
  have h := exponentialLine_dist x v hv 0 1
  simpa only [exponentialLine_zero, zero_sub, abs_neg, abs_one, one_mul, expMap] using h

theorem logMap_expMap (x : Point E) (v : Ambient E) (hv : form E x.val v = 0) :
    logMap x (expMap x v hv) = v := by
  classical
  unfold expMap exponentialLine
  split_ifs with h
  · simp [GeodesicLine.constant, h]
  · have hp := tangentNorm_pos x hv h
    dsimp only [GeodesicLine.ofUnit]
    rw [mul_one, logMap, dist_unitGeodesic_pos _ _ _ _ hp,
      direction_unitGeodesic_pos _ _ _ _ hp, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

/-- Total map for arbitrary oracle replies: the ambient input is projected to
the actual tangent hyperplane. Legal tangent inputs are unchanged. -/
noncomputable def expAt (x : Point E) (v : Ambient E) : Point E :=
  expMap x (tangentPart x v) (tangentPart_orthogonal x v)

theorem tangentPart_eq_self (x : Point E) {v : Ambient E} (hv : form E x.val v = 0) :
    tangentPart x v = v := by simp [tangentPart, hv]

theorem expAt_eq_expMap (x : Point E) {v : Ambient E} (hv : form E x.val v = 0) :
    expAt x v = expMap x v hv := by
  unfold expAt
  congr 1
  exact tangentPart_eq_self x hv

end Geode.Lorentz
