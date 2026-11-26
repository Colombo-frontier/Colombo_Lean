import FreshGradientMinimax.CoreInteraction

/-! Uniform bounds on all four variations of the actual interaction gradients. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

theorem maskedClip_coordinate_bound {m : ℕ} {R : ℝ} (hR : 0 < R)
    (mask : Fin m → ℝ) (hm : ∀ i, |mask i| ≤ 1) (x : Euclid m) (i : Fin m) :
    |coordinateMultiplier mask (clipVector R x) i| ≤ 3 * R / 2 := by
  rw [coordinateMultiplier_apply, abs_mul]
  have h := mul_le_mul (hm i) (smoothClip_bound hR (x i)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using h

theorem maskedCoreLinks_coordinate_bound {n : ℕ} (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (i : Fin (n + n)) :
    |coordinateMultiplier mask (coreLinks u) i| ≤ 4 := by
  rw [coordinateMultiplier_apply, abs_mul]
  have h := mul_le_mul (hm i) (coreLinks_coordinate_bound u i) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using h

theorem framedMaskedClip_sub_norm {n dy : ℕ} (V : Euclid n →ₗᵢ[ℝ] Euclid dy)
    {R : ℝ} (hR : 0 < R) (mask : Fin n → ℝ) (hm : ∀ i, |mask i| ≤ 1) (y z : Euclid dy) :
    ‖coordinateMultiplier mask (clipVector R (frameCoordinates V y)) -
      coordinateMultiplier mask (clipVector R (frameCoordinates V z))‖ ≤ ‖y - z‖ := by
  rw [← map_sub]
  refine (coordinateMultiplier_norm_le hm _).trans ((clipVector_sub_norm hR _ _).trans ?_)
  rw [← map_sub]
  exact frameCoordinates_norm_bound V _

theorem coreInteractionGradU_norm {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreInteractionGradU V a R mask u y‖ ≤ 57 * a * (3 * R / 2) * Real.sqrt (n + n : ℝ) := by
  have hw := (coordinateMultiplier_norm_le hm (clipVector R (frameCoordinates V y))).trans
    (clipVector_norm_bound hR _)
  have hp := (coreLinksPullback_norm
    (coordinateMultiplier mask (clipVector R (frameCoordinates V y))) u).trans
    (mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 57))
  rw [coreInteractionGradU, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have h := mul_le_mul_of_nonneg_left hp ha
  push_cast at h
  nlinarith only [h]

theorem coreInteractionGradY_norm {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {a : ℝ} (ha : 0 ≤ a) (R : ℝ) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreInteractionGradY V a R mask u y‖ ≤ a * ‖coreLinks u‖ := by
  rw [coreInteractionGradY, norm_smul, V.norm_map, Real.norm_eq_abs, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left
    ((weightedClipGradient_norm _ _ _).trans (coordinateMultiplier_norm_le hm _)) ha

theorem coreInteractionGradU_sub_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u v : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreInteractionGradU V a R mask u y - coreInteractionGradU V a R mask v y‖ ≤
      12000 * a * R * ‖u - v‖ := by
  have h := coreLinksPullback_sub_norm (by positivity : 0 ≤ 3 * R / 2)
    (coordinateMultiplier mask (clipVector R (frameCoordinates V y)))
    (maskedClip_coordinate_bound hR mask hm _) u v
  rw [coreInteractionGradU, coreInteractionGradU, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ha]
  have hh := mul_le_mul_of_nonneg_left h ha
  nlinarith only [hh]

theorem coreInteractionGradU_sub_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy) :
    ‖coreInteractionGradU V a R mask u y - coreInteractionGradU V a R mask u z‖ ≤
      (57 * a) * ‖y - z‖ := by
  have h := (coreLinksPullback_sub_weight_norm
    (coordinateMultiplier mask (clipVector R (frameCoordinates V y)))
    (coordinateMultiplier mask (clipVector R (frameCoordinates V z))) u).trans
    (mul_le_mul_of_nonneg_left (framedMaskedClip_sub_norm V hR mask hm y z)
      (by norm_num : (0 : ℝ) ≤ 57))
  rw [coreInteractionGradU, coreInteractionGradU, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ha]
  have hh := mul_le_mul_of_nonneg_left h ha
  nlinarith only [hh]

theorem coreInteractionGradY_sub_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {a : ℝ} (ha : 0 ≤ a) (R : ℝ) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u v : Euclid (n + 1)) (y : Euclid dy) :
    ‖coreInteractionGradY V a R mask u y - coreInteractionGradY V a R mask v y‖ ≤
      (57 * a) * ‖u - v‖ := by
  have h := weightedClipGradient_sub_weights R (coordinateMultiplier mask (coreLinks u))
    (coordinateMultiplier mask (coreLinks v)) (frameCoordinates V y)
  rw [← map_sub] at h
  have hh := h.trans ((coordinateMultiplier_norm_le hm _).trans (coreLinks_sub_norm u v))
  rw [coreInteractionGradY, coreInteractionGradY, ← smul_sub, ← map_sub, norm_smul,
    V.norm_map, Real.norm_eq_abs, abs_of_nonneg ha]
  have hmul := mul_le_mul_of_nonneg_left hh ha
  nlinarith only [hmul]

theorem coreInteractionGradY_sub_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y z : Euclid dy) :
    ‖coreInteractionGradY V a R mask u y - coreInteractionGradY V a R mask u z‖ ≤
      (6 * a / R) * ‖y - z‖ := by
  have h := weightedClipGradient_sub_norm hR (by norm_num : (0 : ℝ) ≤ 4)
    (coordinateMultiplier mask (coreLinks u)) (maskedCoreLinks_coordinate_bound mask hm u)
    (frameCoordinates V y) (frameCoordinates V z)
  rw [← map_sub] at h
  have hh := h.trans (mul_le_mul_of_nonneg_left (frameCoordinates_norm_bound V (y - z))
    (by positivity : 0 ≤ 4 * (3 / (2 * R))))
  rw [coreInteractionGradY, coreInteractionGradY, ← smul_sub, ← map_sub, norm_smul,
    V.norm_map, Real.norm_eq_abs, abs_of_nonneg ha]
  have hmul := mul_le_mul_of_nonneg_left hh ha
  convert hmul using 1
  ring

end FreshGradientMinimax
