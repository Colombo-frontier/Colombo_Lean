import Geode.Hyperbolic
import Mathlib.Topology.MetricSpace.Isometry

/-! Actual unit-speed geodesics in the hyperboloid model. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem future_of_normalized (x : Point E) {v : Ambient E}
    (hv : form E v v = -1) (hxv : form E x.val v < 0) : 0 < v.1 := by
  have hv1 : v.1 ≠ 0 := by
    intro hzero
    rw [form_self, hzero] at hv
    nlinarith [sq_nonneg ‖v.2‖]
  by_contra hfuture
  have hneg : v.1 < 0 := lt_of_le_of_ne (le_of_not_gt hfuture) hv1
  let q : Point E := ⟨-v, by simpa using hv, by simpa using neg_pos.mpr hneg⟩
  have h := reverse_cauchy x q
  change 1 ≤ -form E x.val (-v) at h
  simp only [form_neg_right, neg_neg] at h
  linarith

noncomputable def rayVector (x : Point E) (u : Ambient E) (t : ℝ) : Ambient E :=
  Real.cosh t • x.val + Real.sinh t • u

theorem rayVector_normalized (x : Point E) {u : Ambient E}
    (hu : form E x.val u = 0) (hn : form E u u = 1) (t : ℝ) :
    form E (rayVector x u t) (rayVector x u t) = -1 := by
  have hux : form E u x.val = 0 := by rw [form_comm]; exact hu
  simp only [rayVector, form_add_left, form_add_right, form_smul_left,
    form_smul_right, x.normalized, hu, hux, hn]
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

theorem rayVector_future (x : Point E) {u : Ambient E}
    (hu : form E x.val u = 0) (hn : form E u u = 1) (t : ℝ) :
    0 < (rayVector x u t).1 := by
  apply future_of_normalized x (rayVector_normalized x hu hn t)
  simp only [rayVector, form_add_right, form_smul_right, x.normalized, hu]
  nlinarith [Real.cosh_pos t]

noncomputable def unitGeodesic (x : Point E) (u : Ambient E)
    (hu : form E x.val u = 0) (hn : form E u u = 1) (t : ℝ) : Point E where
  val := rayVector x u t
  normalized := rayVector_normalized x hu hn t
  future := rayVector_future x hu hn t

@[simp] theorem unitGeodesic_zero (x : Point E) (u : Ambient E)
    (hu : form E x.val u = 0) (hn : form E u u = 1) :
    unitGeodesic x u hu hn 0 = x := by
  apply Point.ext
  simp [unitGeodesic, rayVector]

theorem unitGeodesic_form (x : Point E) (u : Ambient E)
    (hu : form E x.val u = 0) (hn : form E u u = 1) (s t : ℝ) :
    form E (unitGeodesic x u hu hn s).val (unitGeodesic x u hu hn t).val =
      -Real.cosh (s - t) := by
  have hux : form E u x.val = 0 := by rw [form_comm]; exact hu
  simp only [unitGeodesic, rayVector, form_add_left, form_add_right,
    form_smul_left, form_smul_right, x.normalized, hu, hux, hn, Real.cosh_sub]
  ring

theorem unitGeodesic_dist (x : Point E) (u : Ambient E)
    (hu : form E x.val u = 0) (hn : form E u u = 1) (s t : ℝ) :
    dist (unitGeodesic x u hu hn s) (unitGeodesic x u hu hn t) = |s - t| := by
  rw [dist_eq_arcosh, unitGeodesic_form, neg_neg, ← Real.cosh_abs]
  exact Geode.arcosh_cosh (abs_nonneg _)

theorem unitGeodesic_isometry (x : Point E) (u : Ambient E)
    (hu : form E x.val u = 0) (hn : form E u u = 1) :
    Isometry (unitGeodesic x u hu hn) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [unitGeodesic_dist, Real.dist_eq]

noncomputable def direction (x y : Point E) : Ambient E :=
  (Real.sinh (dist x y))⁻¹ • (y.val - Real.cosh (dist x y) • x.val)

theorem direction_tangent (x y : Point E) : form E x.val (direction x y) = 0 := by
  simp only [direction, form_smul_right, form_sub_right, x.normalized, cosh_dist]
  ring

theorem direction_unit (x y : Point E) (hne : x ≠ y) :
    form E (direction x y) (direction x y) = 1 := by
  have hd : 0 < dist x y := dist_pos.mpr hne
  have hs : Real.sinh (dist x y) ≠ 0 := (Real.sinh_pos_iff.mpr hd).ne'
  have hxy : form E x.val y.val = -Real.cosh (dist x y) := by rw [cosh_dist]; ring
  have hyx : form E y.val x.val = -Real.cosh (dist x y) := by rw [form_comm]; exact hxy
  have hnorm : form E (y.val - Real.cosh (dist x y) • x.val)
      (y.val - Real.cosh (dist x y) • x.val) = Real.sinh (dist x y) ^ 2 := by
    simp only [form_sub_left, form_sub_right, form_smul_left,
      form_smul_right, x.normalized, y.normalized, hxy, hyx]
    nlinarith [Real.cosh_sq_sub_sinh_sq (dist x y)]
  simp only [direction, form_smul_left, form_smul_right, hnorm]
  field_simp only [hs]
  ring

theorem unitGeodesic_direction (x y : Point E) (hne : x ≠ y) :
    unitGeodesic x (direction x y) (direction_tangent x y) (direction_unit x y hne)
      (dist x y) = y := by
  have hs : Real.sinh (dist x y) ≠ 0 := (Real.sinh_pos_iff.mpr (dist_pos.mpr hne)).ne'
  apply Point.ext
  change Real.cosh (dist x y) • x.val + Real.sinh (dist x y) • direction x y = y.val
  rw [direction, smul_smul, mul_inv_cancel₀ hs, one_smul]
  abel

/-- The constant-speed segment from x to y, parameterized on the whole real line. -/
noncomputable def segment (x y : Point E) (t : ℝ) : Point E := by
  classical
  exact if h : x = y then x else
    unitGeodesic x (direction x y) (direction_tangent x y) (direction_unit x y h) (t * dist x y)

@[simp] theorem segment_zero (x y : Point E) : segment x y 0 = x := by
  unfold segment
  split_ifs <;> simp

@[simp] theorem segment_one (x y : Point E) : segment x y 1 = y := by
  unfold segment
  split_ifs with h
  · exact h
  · simpa using unitGeodesic_direction x y h

theorem segment_dist (x y : Point E) (s t : ℝ) :
    dist (segment x y s) (segment x y t) = |s - t| * dist x y := by
  unfold segment
  split_ifs with h
  · subst y
    simp
  · rw [unitGeodesic_dist, ← sub_mul, abs_mul, abs_of_nonneg dist_nonneg]

end Geode.Lorentz
