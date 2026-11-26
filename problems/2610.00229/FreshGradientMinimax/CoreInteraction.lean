import FreshGradientMinimax.ClipVector
import FreshGradientMinimax.FrameSolve

/-! The actual clipped square-link interaction in the full ambient dual space.
A coordinate mask allows all truncations to share the same construction. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

theorem coordinateMultiplier_inner_comm {m : ℕ} (mask : Fin m → ℝ) (x y : Euclid m) :
    ⟪coordinateMultiplier mask x, y⟫_ℝ = ⟪coordinateMultiplier mask y, x⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply, star_trivial,
    coordinateMultiplier_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem coordinateMultiplier_one {m : ℕ} (x : Euclid m) : coordinateMultiplier (fun _ => 1) x = x := by
  ext i
  simp

theorem frameCoordinates_norm_bound {m dy : ℕ} (V : Euclid m →ₗᵢ[ℝ] Euclid dy) (y : Euclid dy) :
    ‖frameCoordinates V y‖ ≤ ‖y‖ := by
  have h := (frameCoordinates V).le_opNorm y
  have hh := mul_le_mul_of_nonneg_right (frameCoordinates_opNorm V) (norm_nonneg y)
  simpa only [one_mul] using h.trans hh

def coreInteraction {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (a R : ℝ) (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : ℝ :=
  a * weightedCoreLinks (coordinateMultiplier mask (clipVector R (frameCoordinates V y))) u

def coreInteractionGradU {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (a R : ℝ) (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : Euclid (n + 1) :=
  a • coreLinksPullback (coordinateMultiplier mask (clipVector R (frameCoordinates V y))) u

def coreInteractionGradY {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (a R : ℝ) (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) : Euclid dy :=
  a • V (weightedClipGradient R (coordinateMultiplier mask (coreLinks u)) (frameCoordinates V y))

theorem coreInteraction_y_form {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (a R : ℝ) (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) :
    coreInteraction V a R mask u y = a * weightedClip R (coordinateMultiplier mask (coreLinks u))
      (frameCoordinates V y) := by
  unfold coreInteraction weightedCoreLinks weightedClip
  rw [coordinateMultiplier_inner_comm]

theorem coreInteraction_hasFDerivAt_u {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (a R : ℝ) (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) :
    HasFDerivAt (fun v => coreInteraction V a R mask v y)
      (innerSL ℝ (coreInteractionGradU V a R mask u y)) u := by
  convert (weightedCoreLinks_hasFDerivAt
    (coordinateMultiplier mask (clipVector R (frameCoordinates V y))) u).const_mul a using 1
  simp only [coreInteractionGradU, map_smul]

theorem coreInteraction_hasFDerivAt_y {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    (a : ℝ) {R : ℝ} (hR : 0 < R) (mask : Fin (n + n) → ℝ) (u : Euclid (n + 1)) (y : Euclid dy) :
    HasFDerivAt (coreInteraction V a R mask u)
      (innerSL ℝ (coreInteractionGradY V a R mask u y)) y := by
  have hd := ((weightedClip_hasFDerivAt hR (coordinateMultiplier mask (coreLinks u))
    (frameCoordinates V y)).comp y (frameCoordinates V).hasFDerivAt).const_mul a
  have hf : (fun z => a * weightedClip R (coordinateMultiplier mask (coreLinks u)) (frameCoordinates V z)) =
      coreInteraction V a R mask u := funext (fun z => (coreInteraction_y_form V a R mask u z).symm)
  simp only [Function.comp_def] at hd
  rw [hf] at hd
  apply hd.congr_fderiv
  ext v
  simp only [coreInteractionGradY, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply, real_inner_smul_left, smul_eq_mul, frameCoordinates]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem inner_abs_coordinate_bound {m : ℕ} (x y : Euclid m) {A B : ℝ}
    (hA : 0 ≤ A) (hx : ∀ i, |x i| ≤ A) (hy : ∀ i, |y i| ≤ B) :
    |⟪x, y⟫_ℝ| ≤ A * B * (m : ℝ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply, star_trivial]
  calc
    _ ≤ ∑ i : Fin m, |x i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, A * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hx i) (hy i) (abs_nonneg _) hA
    _ = _ := by simp; ring

theorem coreInteraction_bound {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (mask : Fin (n + n) → ℝ)
    (hm : ∀ i, |mask i| ≤ 1) (u : Euclid (n + 1)) (y : Euclid dy) :
    |coreInteraction V a R mask u y| ≤ 12 * a * R * (n : ℝ) := by
  have hw (i : Fin (n + n)) :
      |coordinateMultiplier mask (clipVector R (frameCoordinates V y)) i| ≤ 3 * R / 2 := by
    rw [coordinateMultiplier_apply, abs_mul]
    have h := mul_le_mul (hm i) (smoothClip_bound hR (frameCoordinates V y i)) (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using h
  have h := inner_abs_coordinate_bound
    (coordinateMultiplier mask (clipVector R (frameCoordinates V y))) (coreLinks u)
    (by positivity : 0 ≤ 3 * R / 2) hw (coreLinks_coordinate_bound u)
  unfold coreInteraction weightedCoreLinks
  rw [abs_mul, abs_of_nonneg ha]
  have hh := mul_le_mul_of_nonneg_left h ha
  push_cast at hh
  nlinarith only [hh]

end FreshGradientMinimax
