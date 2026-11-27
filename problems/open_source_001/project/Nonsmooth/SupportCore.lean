import Nonsmooth.Minimax
import Nonsmooth.SphericalLaw
import Nonsmooth.Radial

open MeasureTheory
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The deterministic geometric properties supplied by the external support-function input.
No probability or hardness conclusion is part of this definition. -/
structure SupportModel (h : E → ℝ) : Prop where
  convex : ConvexOn ℝ Set.univ h
  homogeneous : ∀ (a : ℝ), 0 ≤ a → ∀ x, h (a • x) = a * h x
  lipschitz_unit : ∀ x, ‖x‖ ≤ 1 → ∀ y, ‖y‖ ≤ 1 → |h x - h y| ≤ 2 * ‖x - y‖

def strongSupport (μ ℓ : ℝ) (h : E → ℝ) (x : E) : ℝ := μ / 2 * ‖x‖ ^ 2 + ℓ * h x

theorem support_zero {h : E → ℝ} (hh : SupportModel h) : h 0 = 0 := by
  simpa only [zero_smul, zero_mul] using hh.homogeneous 0 le_rfl (0 : E)

theorem support_lipschitz {h : E → ℝ} (hh : SupportModel h) (x y : E) :
    |h x - h y| ≤ 2 * ‖x - y‖ := by
  let s := 1 + ‖x‖ + ‖y‖
  have hs : 0 < s := by dsimp [s]; positivity
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hx : ‖s⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsi]
    apply (mul_le_mul_iff_of_pos_left hs).mp
    simp only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, mul_one]
    dsimp [s]
    linarith [norm_nonneg y]
  have hy : ‖s⁻¹ • y‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsi]
    apply (mul_le_mul_iff_of_pos_left hs).mp
    simp only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, mul_one]
    dsimp [s]
    linarith [norm_nonneg x]
  have hl := hh.lipschitz_unit _ hx _ hy
  rw [hh.homogeneous _ hsi.le, hh.homogeneous _ hsi.le, ← mul_sub, abs_mul,
    abs_of_pos hsi, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hsi] at hl
  have he : 2 * (s⁻¹ * ‖x - y‖) = s⁻¹ * (2 * ‖x - y‖) := by ring
  rw [he] at hl
  exact (mul_le_mul_iff_of_pos_left hsi).mp hl

theorem support_lipschitzWith {h : E → ℝ} (hh : SupportModel h) : LipschitzWith 2 h := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat] using support_lipschitz hh x y

theorem strongSupport_strong {h : E → ℝ} (hh : SupportModel h) (μ R : ℝ)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : StrongConvexOn (Metric.closedBall (0 : E) R) μ (strongSupport μ ℓ h) := by
  apply strongConvexOn_iff_convex.mpr
  refine ⟨convex_closedBall (0 : E) R, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := mul_le_mul_of_nonneg_left (hh.convex.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab) hℓ
  simp only [strongSupport, smul_eq_mul] at *
  nlinarith

theorem quadratic_ball_lipschitz {μ R : ℝ} (hμ : 0 ≤ μ) {x y : E}
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |μ / 2 * ‖x‖ ^ 2 - μ / 2 * ‖y‖ ^ 2| ≤ μ * R * ‖x - y‖ := by
  have hid : μ / 2 * ‖x‖ ^ 2 - μ / 2 * ‖y‖ ^ 2 = ⟪(μ / 2) • (x + y), x - y⟫_ℝ := by
    simp only [real_inner_smul_left, inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm y x]
    ring
  have hn : ‖(μ / 2) • (x + y)‖ ≤ μ * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ μ / 2)]
    calc
      _ ≤ μ / 2 * (‖x‖ + ‖y‖) := mul_le_mul_of_nonneg_left (norm_add_le x y) (by positivity)
      _ ≤ _ := by nlinarith
  rw [hid]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

theorem strongSupport_mem_class {h : E → ℝ} (hh : SupportModel h) {μ ℓ R : ℝ}
    (hμ : 0 ≤ μ) (hℓ : 0 ≤ ℓ) : BallObjective (μ * R + 2 * ℓ) μ R (strongSupport μ ℓ h) := by
  refine ⟨?_, strongSupport_strong hh μ R hℓ⟩
  intro x hx y hy
  have hq := quadratic_ball_lipschitz hμ hx hy
  have hl := mul_le_mul_of_nonneg_left (support_lipschitz hh x y) hℓ
  have hab := abs_add_le (μ / 2 * ‖x‖ ^ 2 - μ / 2 * ‖y‖ ^ 2) (ℓ * (h x - h y))
  rw [abs_mul, abs_of_nonneg hℓ] at hab
  have he : strongSupport μ ℓ h x - strongSupport μ ℓ h y =
      (μ / 2 * ‖x‖ ^ 2 - μ / 2 * ‖y‖ ^ 2) + ℓ * (h x - h y) := by
    unfold strongSupport
    ring
  rw [he]
  nlinarith

theorem support_minimum_attained [ProperSpace E] {h : E → ℝ} (hh : SupportModel h) :
    ∃ z : E, ‖z‖ ≤ 1 ∧ h z = minimumValue 1 h ∧ ∀ y, ‖y‖ ≤ 1 → h z ≤ h y := by
  obtain ⟨z, hz, hm⟩ := (isCompact_closedBall (0 : E) (1 : ℝ)).exists_isMinOn
    (show (Metric.closedBall (0 : E) (1 : ℝ)).Nonempty from ⟨0, by simp⟩)
    (support_lipschitzWith hh).continuous.continuousOn
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  have hm' : ∀ y, ‖y‖ ≤ 1 → h z ≤ h y := fun y hy => hm (by simpa using hy)
  exact ⟨z, hz', (minimumValue_eq hz' hm').symm, hm'⟩

theorem support_minimum_le [ProperSpace E] {h : E → ℝ} (hh : SupportModel h) {y : E}
    (hy : ‖y‖ ≤ 1) : minimumValue 1 h ≤ h y := by
  obtain ⟨z, hz, he, hm⟩ := support_minimum_attained hh
  rw [← he]
  exact hm y hy

theorem support_depth_nonneg [ProperSpace E] {h : E → ℝ} (hh : SupportModel h) :
    0 ≤ -minimumValue 1 h := by
  have h := support_minimum_le hh (y := 0) (by simp)
  rw [support_zero hh] at h
  linarith

theorem support_radial_lower [ProperSpace E] {h : E → ℝ} (hh : SupportModel h) (x : E) :
    minimumValue 1 h * ‖x‖ ≤ h x := by
  by_cases hx : x = 0
  · simp only [hx, norm_zero, mul_zero, support_zero hh, le_refl]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hunit : ‖normalizedDirection x‖ ≤ 1 := by
      simp [normalizedDirection, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), hn]
    have hmin := support_minimum_le hh hunit
    have he : ‖x‖ • normalizedDirection x = x := by
      simp only [normalizedDirection, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have hhom := hh.homogeneous ‖x‖ (norm_nonneg x) (normalizedDirection x)
    rw [he] at hhom
    have hm := mul_le_mul_of_nonneg_right hmin (norm_nonneg x)
    rw [hhom]
    nlinarith

theorem strongSupport_lower [ProperSpace E] {h : E → ℝ} (hh : SupportModel h) {μ ℓ R : ℝ}
    (hμ : 0 < μ) (hℓ : 0 ≤ ℓ) (hR : 0 ≤ R) {x : E} (hx : ‖x‖ ≤ R) :
    -radial μ R (ℓ * (-minimumValue 1 h)) ≤ strongSupport μ ℓ h x := by
  have hs : 0 ≤ ℓ * (-minimumValue 1 h) := mul_nonneg hℓ (support_depth_nonneg hh)
  have hr := radial_maximizer hs hμ hR (norm_nonneg x) hx
  have hl := mul_le_mul_of_nonneg_left (support_radial_lower hh x) hℓ
  dsimp [strongSupport, radial]
  nlinarith

theorem strongSupport_minimum [ProperSpace E] {h : E → ℝ} (hh : SupportModel h) {μ ℓ R : ℝ}
    (hμ : 0 < μ) (hℓ : 0 ≤ ℓ) (hR : 0 ≤ R) :
    minimumValue R (strongSupport μ ℓ h) = -radial μ R (ℓ * (-minimumValue 1 h)) := by
  obtain ⟨z, hz, hzval, _⟩ := support_minimum_attained hh
  let s := ℓ * (-minimumValue 1 h)
  let r := radius s μ R
  have hs : 0 ≤ s := mul_nonneg hℓ (support_depth_nonneg hh)
  have hr : 0 ≤ r := radius_nonneg hs hμ hR
  have hnorm : ‖r • z‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hr
  have hx : ‖r • z‖ ≤ R := hnorm.trans (radius_le_R s μ R)
  have hq : μ / 2 * ‖r • z‖ ^ 2 ≤ μ / 2 * r ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (by positivity)
  have hupper : strongSupport μ ℓ h (r • z) ≤ -radial μ R s := by
    rw [strongSupport, hh.homogeneous r hr, hzval]
    dsimp [radial, energy]
    change μ / 2 * ‖r • z‖ ^ 2 + ℓ * (r * minimumValue 1 h) ≤ -(s * r - μ / 2 * r ^ 2)
    dsimp [s] at *
    nlinarith
  have he : strongSupport μ ℓ h (r • z) = -radial μ R s :=
    le_antisymm hupper (strongSupport_lower hh hμ hℓ hR hx)
  rw [minimumValue_eq hx (fun y hy => by rw [he]; exact strongSupport_lower hh hμ hℓ hR hy), he]

theorem normalizedDirection_reconstruct (x : E) : ‖x‖ • normalizedDirection x = x := by
  by_cases hx : x = 0
  · simp [hx, normalizedDirection]
  · simp [normalizedDirection, smul_smul, norm_ne_zero_iff.mpr hx]

theorem support_radial_value {h : E → ℝ} (hh : SupportModel h) (x : E) :
    h x = ‖x‖ * h (normalizedDirection x) := by
  have h := hh.homogeneous ‖x‖ (norm_nonneg x) (normalizedDirection x)
  simpa only [normalizedDirection_reconstruct] using h

theorem strongSupport_output_lower {h : E → ℝ} (hh : SupportModel h) {μ ℓ R : ℝ}
    (hμ : 0 < μ) (hℓ : 0 ≤ ℓ) (hR : 0 ≤ R) {x : E} (hx : ‖x‖ ≤ R) :
    -radial μ R (ℓ * max (-h (normalizedDirection x)) 0) ≤ strongSupport μ ℓ h x := by
  have hs : 0 ≤ ℓ * max (-h (normalizedDirection x)) 0 := mul_nonneg hℓ (le_max_right _ _)
  have hr := radial_maximizer hs hμ hR (norm_nonneg x) hx
  have hc := mul_le_mul_of_nonneg_left (le_max_left (-h (normalizedDirection x)) 0)
    (mul_nonneg hℓ (norm_nonneg x))
  rw [strongSupport, support_radial_value hh x]
  dsimp [radial]
  nlinarith

/-- Deterministic risk on the intersection of the two support-hardness events. -/
theorem strongSupport_event_risk [ProperSpace E] {h : E → ℝ} (hh : SupportModel h) {μ ℓ R a : ℝ}
    (hμ : 0 < μ) (hℓ : 0 ≤ ℓ) (hR : 0 ≤ R) (ha : 0 ≤ a) {x : E} (hx : ‖x‖ ≤ R)
    (hdepth : a ≤ -minimumValue 1 h)
    (hgap : 7 * a / 16 ≤ h (normalizedDirection x) - minimumValue 1 h) :
    175 / 512 * min (ℓ * a * R) ((ℓ * a) ^ 2 / μ) ≤
      strongSupport μ ℓ h x - minimumValue R (strongSupport μ ℓ h) := by
  let s := ℓ * (-minimumValue 1 h)
  let s₀ := ℓ * a
  let q := 7 * s₀ / 16
  have hs₀ : 0 ≤ s₀ := mul_nonneg hℓ ha
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqs : q ≤ s₀ := by dsimp [q]; linarith
  have hss : s₀ ≤ s := mul_le_mul_of_nonneg_left hdepth hℓ
  have hm : max (-h (normalizedDirection x)) 0 ≤ -minimumValue 1 h - 7 * a / 16 := by
    apply max_le
    · linarith
    · linarith
  have harg : ℓ * max (-h (normalizedDirection x)) 0 ≤ s - q := by
    have h := mul_le_mul_of_nonneg_left hm hℓ
    dsimp [s, q, s₀]
    nlinarith
  have harg0 : 0 ≤ ℓ * max (-h (normalizedDirection x)) 0 := mul_nonneg hℓ (le_max_right _ _)
  have hD := radial_monotone hμ hR harg0 (by linarith : 0 ≤ s - q) harg
  have hinc := radial_fixed_increment_mono hμ hR hq hqs hss
  have hsub : s₀ - q = 9 * s₀ / 16 := by dsimp [q]; ring
  rw [hsub] at hinc
  have hnum := radial_increment hμ hR hs₀
  have hout := strongSupport_output_lower hh hμ hℓ hR hx
  rw [strongSupport_minimum hh hμ hℓ hR]
  change 175 / 512 * min (s₀ * R) (s₀ ^ 2 / μ) ≤ strongSupport μ ℓ h x - -radial μ R s
  linarith

end
end Nonsmooth

