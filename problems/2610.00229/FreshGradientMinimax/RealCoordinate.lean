import FreshGradientMinimax.Objective

/-! Exact one-dimensional coordinates for admissible finite-dimensional instances. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def realVector (t : ℝ) : Euclid 1 := EuclideanSpace.single 0 t
def realCoord (x : Euclid 1) : ℝ := x 0
def realCoordCLM : Euclid 1 →L[ℝ] ℝ := innerSL ℝ (realVector 1)

@[simp]
theorem realCoord_vector (t : ℝ) : realCoord (realVector t) = t := by
  simp [realCoord, realVector, EuclideanSpace.single_apply]

@[simp]
theorem realVector_coord (x : Euclid 1) : realVector (realCoord x) = x := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [realCoord, realVector, EuclideanSpace.single_apply]

@[simp]
theorem realVector_norm (t : ℝ) : ‖realVector t‖ = |t| := by
  simp [realVector, EuclideanSpace.norm_single, Real.norm_eq_abs]

theorem realCoord_norm (x : Euclid 1) : |realCoord x| = ‖x‖ := by
  rw [← realVector_norm, realVector_coord]

@[simp]
theorem realVector_inner (t : ℝ) (x : Euclid 1) :
    ⟪realVector t, x⟫_ℝ = t * realCoord x := by
  simp [realVector, realCoord, EuclideanSpace.inner_single_left, mul_comm]

@[simp]
theorem realCoordCLM_apply (x : Euclid 1) : realCoordCLM x = realCoord x := by
  simp [realCoordCLM, innerSL_apply, realVector, realCoord]

@[simp]
theorem realCoord_sub (x y : Euclid 1) : realCoord (x - y) = realCoord x - realCoord y := by
  rfl

@[simp]
theorem realCoord_zero : realCoord (0 : Euclid 1) = 0 := rfl

theorem realVector_sub (a b : ℝ) : realVector a - realVector b = realVector (a - b) := by
  apply_fun realCoord using (fun x y h => by rw [← realVector_coord x, ← realVector_coord y, h])
  simp

theorem realCoord_hasFDerivAt (x : Euclid 1) : HasFDerivAt realCoord realCoordCLM x := by
  have he : (realCoordCLM : Euclid 1 → ℝ) = realCoord := funext realCoordCLM_apply
  exact he ▸ realCoordCLM.hasFDerivAt (x := x)

theorem scalar_hasFDerivAt {f : ℝ → ℝ} {d x : ℝ} (hd : HasDerivAt f d x) :
    HasFDerivAt f (innerSL ℝ d) x := by
  apply hd.hasFDerivAt.congr_fderiv
  apply ContinuousLinearMap.ext
  intro t
  simp [innerSL_apply, real_inner_comm]

end FreshGradientMinimax

