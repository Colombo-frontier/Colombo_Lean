import FreshGradientMinimax.CompressedSmoothness

/-! Actual compression transfers arbitrary uniform derivative bounds.
These estimates do not use the special constants of the C construction. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
variable {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
  {f : Euclid (n + 1) → Euclid dy → ℝ} {r R β A M : ℝ}

theorem compressedGradX_sub_x_general (hr : 0 < r) (hR : 0 < R) (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (hxx : ∀ u v y, ‖gradient (fun w => f w y) u - gradient (fun w => f w y) v‖ ≤ A * ‖u - v‖)
    (hbound : ∀ u y, ‖gradient (fun w => f w y) u‖ ≤ M)
    (x z : Euclid dx) (y : Euclid dy) :
    ‖compressedGradX U f r R β x y - compressedGradX U f r R β z y‖ ≤
      (A / r ^ 2 + 3 * M / (r * R) + β) * ‖x - z‖ := by
  let gx := gradient (fun u => f u y) (compressedCoordinates U r R x)
  let gz := gradient (fun u => f u y) (compressedCoordinates U r R z)
  have h1 := compressedPullback_sub_gradient U hr R x gx gz
  have h2 := compressedPullback_sub_point U hr hR x z gz
  have h3 := hxx (compressedCoordinates U r R x) (compressedCoordinates U r R z) y
  have h4 := mul_le_mul_of_nonneg_left (compressedCoordinates_sub_norm U hr hR x z) hA
  have h5 := mul_le_mul_of_nonneg_left (h3.trans h4) (inv_nonneg.mpr hr.le)
  have h6 := mul_le_mul_of_nonneg_left (hbound (compressedCoordinates U r R z) y)
    (by positivity : 0 ≤ (3 / (r * R)) * ‖x - z‖)
  have h7 := norm_sub_triangle (compressedPullback U r R x gx)
    (compressedPullback U r R x gz) (compressedPullback U r R z gz)
  have h8 := norm_add_le (compressedPullback U r R x gx - compressedPullback U r R z gz) (β • (x - z))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ] at h8
  change ‖(compressedPullback U r R x gx + β • x) - (compressedPullback U r R z gz + β • z)‖ ≤ _
  rw [add_sub_add_comm, ← smul_sub]
  have he : A / r ^ 2 = r⁻¹ * (A * r⁻¹) := by
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have he' : 3 * M / (r * R) = (3 / (r * R)) * M := by ring
  rw [he, he']
  change r⁻¹ * ‖gx - gz‖ ≤ _ at h5
  change _ * ‖gz‖ ≤ _ at h6
  nlinarith only [h1, h2, h5, h6, h7, h8]

theorem compressedGradX_sub_y_general (hr : 0 < r)
    (hxy : ∀ u y z, ‖gradient (fun w => f w y) u - gradient (fun w => f w z) u‖ ≤ A * ‖y - z‖)
    (x : Euclid dx) (y z : Euclid dy) :
    ‖compressedGradX U f r R β x y - compressedGradX U f r R β x z‖ ≤
      (A / r) * ‖y - z‖ := by
  have h1 := compressedPullback_sub_gradient U hr R x
    (gradient (fun u => f u y) (compressedCoordinates U r R x))
    (gradient (fun u => f u z) (compressedCoordinates U r R x))
  have h2 := mul_le_mul_of_nonneg_left (hxy (compressedCoordinates U r R x) y z)
    (inv_nonneg.mpr hr.le)
  simp only [compressedGradX, add_sub_add_right_eq_sub]
  convert h1.trans h2 using 1
  ring

theorem compressedGradY_sub_x_general (hr : 0 < r) (hR : 0 < R) (hA : 0 ≤ A)
    (hyx : ∀ u v y, ‖gradient (f u) y - gradient (f v) y‖ ≤ A * ‖u - v‖)
    (x z : Euclid dx) (y : Euclid dy) :
    ‖compressedGradY U f r R x y - compressedGradY U f r R z y‖ ≤
      (A / r) * ‖x - z‖ := by
  have h1 := hyx (compressedCoordinates U r R x) (compressedCoordinates U r R z) y
  have h2 := mul_le_mul_of_nonneg_left (compressedCoordinates_sub_norm U hr hR x z) hA
  convert h1.trans h2 using 1
  ring

theorem compressedGradY_sub_y_general
    (hyy : ∀ u y z, ‖gradient (f u) y - gradient (f u) z‖ ≤ A * ‖y - z‖)
    (x : Euclid dx) (y z : Euclid dy) :
    ‖compressedGradY U f r R x y - compressedGradY U f r R x z‖ ≤ A * ‖y - z‖ :=
  hyy (compressedCoordinates U r R x) y z

end FreshGradientMinimax
