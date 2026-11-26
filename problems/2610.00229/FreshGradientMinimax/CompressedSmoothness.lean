import FreshGradientMinimax.CompressedObjective

/-! Transfer C.2's global gradient bounds through the actual compression.
The estimates use differences, so they include all cap interfaces. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
theorem norm_sub_triangle {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  simpa only [dist_eq_norm] using dist_triangle x y z

variable {n dx dy : ℕ} (U : Euclid (n + 1) →ₗᵢ[ℝ] Euclid dx)
  {f : Euclid (n + 1) → Euclid dy → ℝ} {lam μ r R β : ℝ}

theorem compressedGradX_sub_x (hr : 0 < r) (hR : 0 < R) (hβ : 0 ≤ β) (hlam : 0 ≤ lam)
    (hf : CoreDerivativeBounds f lam μ) (x z : Euclid dx) (y : Euclid dy) :
    ‖compressedGradX U f r R β x y - compressedGradX U f r R β z y‖ ≤
      (10 ^ 6 * lam / r ^ 2 + 24000 * lam * Real.sqrt (n + 1 : ℝ) / (r * R) + β) * ‖x - z‖ := by
  let gx := gradient (fun u => f u y) (compressedCoordinates U r R x)
  let gz := gradient (fun u => f u y) (compressedCoordinates U r R z)
  have h1 := compressedPullback_sub_gradient U hr R x gx gz
  have h2 := compressedPullback_sub_point U hr hR x z gz
  have h3 := hf.uu_lipschitz (compressedCoordinates U r R x) (compressedCoordinates U r R z) y
  have h4 := mul_le_mul_of_nonneg_left (compressedCoordinates_sub_norm U hr hR x z)
    (by positivity : 0 ≤ 10 ^ 6 * lam)
  have h5 := mul_le_mul_of_nonneg_left (h3.trans h4) (inv_nonneg.mpr hr.le)
  have h6 := mul_le_mul_of_nonneg_left (hf.u_norm (compressedCoordinates U r R z) y)
    (by positivity : 0 ≤ (3 / (r * R)) * ‖x - z‖)
  have h7 := norm_sub_triangle (compressedPullback U r R x gx)
    (compressedPullback U r R x gz) (compressedPullback U r R z gz)
  have h8 := norm_add_le (compressedPullback U r R x gx - compressedPullback U r R z gz) (β • (x - z))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ] at h8
  change ‖(compressedPullback U r R x gx + β • x) - (compressedPullback U r R z gz + β • z)‖ ≤ _
  rw [add_sub_add_comm, ← smul_sub]
  have he : 10 ^ 6 * lam / r ^ 2 = r⁻¹ * (10 ^ 6 * lam * r⁻¹) := by
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have he' : 24000 * lam * Real.sqrt (n + 1 : ℝ) / (r * R) =
      (3 / (r * R)) * (8000 * lam * Real.sqrt (n + 1 : ℝ)) := by ring
  rw [he, he']
  change ‖gx - gz‖ ≤ _ at h3
  change r⁻¹ * ‖gx - gz‖ ≤ _ at h5
  change _ * ‖gz‖ ≤ _ at h6
  nlinarith only [h1, h2, h5, h6, h7, h8]

theorem compressedGradX_sub_y (hr : 0 < r) (hf : CoreDerivativeBounds f lam μ)
    (x : Euclid dx) (y z : Euclid dy) :
    ‖compressedGradX U f r R β x y - compressedGradX U f r R β x z‖ ≤
      (2000 * Real.sqrt (μ * lam) / r) * ‖y - z‖ := by
  have h1 := compressedPullback_sub_gradient U hr R x
    (gradient (fun u => f u y) (compressedCoordinates U r R x))
    (gradient (fun u => f u z) (compressedCoordinates U r R x))
  have h2 := mul_le_mul_of_nonneg_left (hf.uy_lipschitz (compressedCoordinates U r R x) y z)
    (inv_nonneg.mpr hr.le)
  simp only [compressedGradX, add_sub_add_right_eq_sub]
  convert h1.trans h2 using 1
  ring

theorem compressedGradY_sub_x (hr : 0 < r) (hR : 0 < R) (hf : CoreDerivativeBounds f lam μ)
    (x z : Euclid dx) (y : Euclid dy) :
    ‖compressedGradY U f r R x y - compressedGradY U f r R z y‖ ≤
      (2000 * Real.sqrt (μ * lam) / r) * ‖x - z‖ := by
  have h1 := hf.yu_lipschitz (compressedCoordinates U r R x) (compressedCoordinates U r R z) y
  have h2 := mul_le_mul_of_nonneg_left (compressedCoordinates_sub_norm U hr hR x z)
    (by positivity : 0 ≤ 2000 * Real.sqrt (μ * lam))
  convert h1.trans h2 using 1
  ring

theorem compressedGradY_sub_y (hf : CoreDerivativeBounds f lam μ)
    (x : Euclid dx) (y z : Euclid dy) :
    ‖compressedGradY U f r R x y - compressedGradY U f r R x z‖ ≤ 50 * μ * ‖y - z‖ :=
  hf.yy_lipschitz (compressedCoordinates U r R x) y z

theorem joint_smooth_of_four_blocks {L : ℝ} (hL : 0 ≤ L)
    {Gx : Euclid dx → Euclid dy → Euclid dx} {Gy : Euclid dx → Euclid dy → Euclid dy}
    (hxx : ∀ x z y, ‖Gx x y - Gx z y‖ ≤ L / 2 * ‖x - z‖)
    (hxy : ∀ x y z, ‖Gx x y - Gx x z‖ ≤ L / 2 * ‖y - z‖)
    (hyx : ∀ x z y, ‖Gy x y - Gy z y‖ ≤ L / 2 * ‖x - z‖)
    (hyy : ∀ x y z, ‖Gy x y - Gy x z‖ ≤ L / 2 * ‖y - z‖)
    (x z : Euclid dx) (y w : Euclid dy) :
    ‖Gx x y - Gx z w‖ ^ 2 + ‖Gy x y - Gy z w‖ ^ 2 ≤ L ^ 2 * (‖x - z‖ ^ 2 + ‖y - w‖ ^ 2) := by
  have hx : ‖Gx x y - Gx z w‖ ≤ L / 2 * (‖x - z‖ + ‖y - w‖) := by
    have h := (norm_sub_triangle (Gx x y) (Gx z y) (Gx z w)).trans (add_le_add (hxx x z y) (hxy z y w))
    nlinarith only [h]
  have hy : ‖Gy x y - Gy z w‖ ≤ L / 2 * (‖x - z‖ + ‖y - w‖) := by
    have h := (norm_sub_triangle (Gy x y) (Gy z y) (Gy z w)).trans (add_le_add (hyx x z y) (hyy z y w))
    nlinarith only [h]
  have hx2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ L / 2 * (‖x - z‖ + ‖y - w‖))).mpr hx
  have hy2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ L / 2 * (‖x - z‖ + ‖y - w‖))).mpr hy
  nlinarith only [hx2, hy2, sq_nonneg (L * (‖x - z‖ - ‖y - w‖))]

end FreshGradientMinimax

