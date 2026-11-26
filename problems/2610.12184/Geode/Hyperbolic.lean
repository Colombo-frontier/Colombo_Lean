import Geode.Lorentz
import Geode.Acosh
import Mathlib.Topology.MetricSpace.Basic

/-! The genuine hyperboloid metric, constructed from the Lorentz form. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def hyperbolicDistance (x y : Point E) : ℝ :=
  Geode.arcosh (-form E x.val y.val)

theorem hyperbolicDistance_nonneg (x y : Point E) : 0 ≤ hyperbolicDistance x y :=
  Geode.arcosh_nonneg _

@[simp] theorem hyperbolicDistance_self (x : Point E) : hyperbolicDistance x x = 0 := by
  simp [hyperbolicDistance, x.normalized]

theorem hyperbolicDistance_comm (x y : Point E) :
    hyperbolicDistance x y = hyperbolicDistance y x := by
  simp only [hyperbolicDistance, form_comm x.val y.val]

@[simp] theorem cosh_hyperbolicDistance (x y : Point E) :
    Real.cosh (hyperbolicDistance x y) = -form E x.val y.val :=
  Geode.cosh_arcosh (reverse_cauchy x y)

theorem hyperbolicDistance_eq_zero_iff (x y : Point E) :
    hyperbolicDistance x y = 0 ↔ x = y :=
  (Geode.arcosh_eq_zero_iff (reverse_cauchy x y)).trans (reverse_cauchy_eq_iff x y)

def tangentPart (x : Point E) (v : Ambient E) : Ambient E :=
  v + form E x.val v • x.val

@[simp] theorem tangentPart_orthogonal (x : Point E) (v : Ambient E) :
    form E x.val (tangentPart x v) = 0 := by
  simp [tangentPart, x.normalized]

theorem form_tangentPart (x : Point E) (v w : Ambient E) :
    form E (tangentPart x v) (tangentPart x w) =
      form E v w + form E x.val v * form E x.val w := by
  simp only [tangentPart, form_add_left, form_add_right,
    form_smul_left, form_smul_right, x.normalized, form_comm v x.val]
  ring

theorem lorentz_triangle_gram (x y z : Point E) :
    (form E x.val z.val + form E y.val x.val * form E y.val z.val) ^ 2 ≤
      (form E y.val x.val ^ 2 - 1) * (form E y.val z.val ^ 2 - 1) := by
  have h := tangent_cauchy_sq y (tangentPart_orthogonal y x.val)
    (tangentPart_orthogonal y z.val)
  simpa only [form_tangentPart, x.normalized, z.normalized, pow_two,
    sub_eq_add_neg, add_comm] using h

theorem hyperbolicDistance_triangle (x y z : Point E) :
    hyperbolicDistance x z ≤ hyperbolicDistance x y + hyperbolicDistance y z := by
  have ha := hyperbolicDistance_nonneg x y
  have hb := hyperbolicDistance_nonneg y z
  have hsa := Real.sinh_nonneg_iff.mpr ha
  have hsb := Real.sinh_nonneg_iff.mpr hb
  have hprod := mul_nonneg hsa hsb
  have hyx : form E y.val x.val = -Real.cosh (hyperbolicDistance x y) := by
    rw [cosh_hyperbolicDistance, form_comm y.val x.val]
    ring
  have hyz : form E y.val z.val = -Real.cosh (hyperbolicDistance y z) := by
    rw [cosh_hyperbolicDistance]
    ring
  have hgram := lorentz_triangle_gram x y z
  rw [hyx, hyz, neg_sq, neg_sq, neg_mul_neg] at hgram
  have hsq : (Real.sinh (hyperbolicDistance x y) * Real.sinh (hyperbolicDistance y z)) ^ 2 =
      (Real.cosh (hyperbolicDistance x y) ^ 2 - 1) *
      (Real.cosh (hyperbolicDistance y z) ^ 2 - 1) := by
    rw [mul_pow, Real.sinh_sq, Real.sinh_sq]
  have hbound : -form E x.val z.val ≤ Real.cosh (hyperbolicDistance x y) *
      Real.cosh (hyperbolicDistance y z) +
      Real.sinh (hyperbolicDistance x y) * Real.sinh (hyperbolicDistance y z) := by
    have habs := (sq_le_sq₀ (abs_nonneg (form E x.val z.val +
      Real.cosh (hyperbolicDistance x y) * Real.cosh (hyperbolicDistance y z))) hprod).mp
      (by simpa only [sq_abs, hsq] using hgram)
    have hlo := (abs_le.mp habs).1
    linarith
  apply (Geode.arcosh_le_iff_le_cosh (reverse_cauchy x z) (add_nonneg ha hb)).mpr
  simpa only [Real.cosh_add] using hbound

noncomputable instance : MetricSpace (Point E) where
  dist := hyperbolicDistance
  dist_self := hyperbolicDistance_self
  dist_comm := hyperbolicDistance_comm
  dist_triangle := hyperbolicDistance_triangle
  eq_of_dist_eq_zero := fun h => (hyperbolicDistance_eq_zero_iff _ _).mp h

@[simp] theorem dist_eq_arcosh (x y : Point E) :
    dist x y = Geode.arcosh (-form E x.val y.val) := rfl

@[simp] theorem cosh_dist (x y : Point E) :
    Real.cosh (dist x y) = -form E x.val y.val := cosh_hyperbolicDistance x y

theorem dist_le_iff {x y : Point E} {r : ℝ} (hr : 0 ≤ r) :
    dist x y ≤ r ↔ -form E x.val y.val ≤ Real.cosh r :=
  Geode.arcosh_le_iff_le_cosh (reverse_cauchy x y) hr

theorem le_dist_iff {x y : Point E} {r : ℝ} (hr : 0 ≤ r) :
    r ≤ dist x y ↔ Real.cosh r ≤ -form E x.val y.val :=
  Geode.le_arcosh_iff_cosh_le (reverse_cauchy x y) hr

end Geode.Lorentz
