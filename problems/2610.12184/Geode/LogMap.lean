import Geode.Geodesic
import Geode.DistanceComparison

/-! The actual logarithm vector and its global contraction inequality. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def logMap (x y : Point E) : Ambient E := dist x y • direction x y

@[simp] theorem logMap_self (x : Point E) : logMap x x = 0 := by simp [logMap]

@[simp] theorem logMap_tangent (x y : Point E) : form E x.val (logMap x y) = 0 := by
  simp [logMap, direction_tangent]

@[simp] theorem form_logMap_self (x y : Point E) :
    form E (logMap x y) (logMap x y) = dist x y ^ 2 := by
  by_cases h : x = y
  · subst y
    simp
  · simp only [logMap, form_smul_left, form_smul_right, direction_unit x y h]
    ring

theorem point_decomposition (x y : Point E) :
    y.val = Real.cosh (dist x y) • x.val + Real.sinh (dist x y) • direction x y := by
  by_cases h : x = y
  · subst y
    simp
  · have he := congrArg Point.val (unitGeodesic_direction x y h)
    exact he.symm

theorem hyperbolic_cosine_law (x y z : Point E) :
    -form E y.val z.val = Real.cosh (dist x y) * Real.cosh (dist x z) -
      Real.sinh (dist x y) * Real.sinh (dist x z) * form E (direction x y) (direction x z) := by
  have hyx : form E (direction x y) x.val = 0 := by rw [form_comm]; exact direction_tangent x y
  calc
    -form E y.val z.val = -form E
        (Real.cosh (dist x y) • x.val + Real.sinh (dist x y) • direction x y)
        (Real.cosh (dist x z) • x.val + Real.sinh (dist x z) • direction x z) := by
          rw [← point_decomposition x y, ← point_decomposition x z]
    _ = _ := by
      simp only [form_add_left, form_add_right, form_smul_left, form_smul_right,
        x.normalized, direction_tangent, hyx]
      ring

theorem direction_pair_bounds (x y z : Point E) (hy : x ≠ y) (hz : x ≠ z) :
    -1 ≤ form E (direction x y) (direction x z) ∧
      form E (direction x y) (direction x z) ≤ 1 := by
  have h := tangent_cauchy_sq x (direction_tangent x y) (direction_tangent x z)
  rw [direction_unit x y hy, direction_unit x z hz] at h
  constructor <;> nlinarith

theorem logMap_contraction_sq (x y z : Point E) :
    form E (logMap x y - logMap x z) (logMap x y - logMap x z) ≤ dist y z ^ 2 := by
  by_cases hy : x = y
  · subst y
    simp
  by_cases hz : x = z
  · subst z
    simp [dist_comm]
  obtain ⟨hlo, hhi⟩ := direction_pair_bounds x y z hy hz
  have h := Geode.cosine_law_squared_log_contraction
    (r := dist x y) (s := dist x z) hlo hhi
  rw [← hyperbolic_cosine_law x y z] at h
  change dist x y ^ 2 + dist x z ^ 2 -
      2 * dist x y * dist x z * form E (direction x y) (direction x z) ≤ dist y z ^ 2 at h
  have hform : form E (logMap x y - logMap x z) (logMap x y - logMap x z) =
      dist x y ^ 2 + dist x z ^ 2 -
        2 * dist x y * dist x z * form E (direction x y) (direction x z) := by
    simp only [form_sub_left, form_sub_right, form_logMap_self,
      form_comm (logMap x z) (logMap x y)]
    simp only [logMap, form_smul_left, form_smul_right]
    ring
  rw [hform]
  exact h

noncomputable def tangentNorm (v : Ambient E) : ℝ := Real.sqrt (form E v v)

@[simp] theorem tangentNorm_logMap (x y : Point E) : tangentNorm (logMap x y) = dist x y := by
  rw [tangentNorm, form_logMap_self, Real.sqrt_sq dist_nonneg]

/-- Global log-map contraction in the actual Riemannian tangent norm. -/
theorem logMap_contraction (x y z : Point E) :
    tangentNorm (logMap x y - logMap x z) ≤ dist y z := by
  apply (Real.sqrt_le_left dist_nonneg).mpr
  exact logMap_contraction_sq x y z

end Geode.Lorentz
