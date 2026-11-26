import FreshGradientMinimax.SmoothMaximum
import FreshGradientMinimax.Calculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex

/-! The actual radial protection of Appendix B: the objective agrees with its
path energy in the core and with a frame-independent radial wall outside. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialWall (β R : ℝ) (x : E) : ℝ := 4 * β * (‖x‖ ^ 2 - R ^ 2)

def radialCap (Q : E → ℝ) (β R : ℝ) (x : E) : ℝ :=
  smoothMaximum (β * R ^ 2) (Q x) (radialWall β R x)

def radialCapWeight (Q : E → ℝ) (β R : ℝ) (x : E) : ℝ :=
  smoothRampSlope (β * R ^ 2) (radialWall β R x - Q x)

def radialCapGradient (Q : E → ℝ) (G : E → E) (β R : ℝ) (x : E) : E :=
  (1 - radialCapWeight Q β R x) • G x + radialCapWeight Q β R x • ((8 * β) • x)

theorem radialWall_hasFDerivAt (β R : ℝ) (x : E) :
    HasFDerivAt (radialWall β R) (innerSL ℝ ((8 * β) • x)) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const (R ^ 2)).const_mul (4 * β)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply, real_inner_smul_left, smul_eq_mul]
  ring

theorem radialWall_convex {β : ℝ} (hβ : 0 ≤ β) (R : ℝ) :
    ConvexOn ℝ Set.univ (radialWall (E := E) β R) := by
  have hn : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have ht := (convexOn_univ_norm (E := E)).2 hx hy ha hb hab
    simp only [smul_eq_mul] at ht ⊢
    have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
    have hid : a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - (a * ‖x‖ + b * ‖y‖) ^ 2 =
        a * b * (‖x‖ - ‖y‖) ^ 2 := by
      have hb' : b = 1 - a := by linarith
      rw [hb']; ring
    have hp : 0 ≤ a * b * (‖x‖ - ‖y‖) ^ 2 := by positivity
    nlinarith only [hs, hid, hp]
  have h := (hn.add_const (-(R ^ 2))).smul (show 0 ≤ 4 * β by positivity)
  simpa only [Pi.add_apply, smul_eq_mul, sub_eq_add_neg] using h

theorem radialCap_hasFDerivAt {Q : E → ℝ} {G : E → E} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hQ : ∀ x, HasFDerivAt Q (innerSL ℝ (G x)) x) (x : E) :
    HasFDerivAt (radialCap Q β R) (innerSL ℝ (radialCapGradient Q G β R x)) x := by
  have h := smoothMaximum_comp_hasFDerivAt (by positivity : 0 < β * R ^ 2)
    (hQ x) (radialWall_hasFDerivAt β R x)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [radialCapGradient, radialCapWeight, innerSL_apply, inner_add_left, real_inner_smul_left]

theorem radialCap_convex {Q : E → ℝ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hQ : ConvexOn ℝ Set.univ Q) : ConvexOn ℝ Set.univ (radialCap Q β R) :=
  smoothMaximum_comp_convex (by positivity) hQ (radialWall_convex hβ.le R)

omit [InnerProductSpace ℝ E] in
theorem radialCap_core {Q : E → ℝ} {β R : ℝ} (hβ : 0 ≤ β)
    (hQ : ∀ x, 0 ≤ Q x) {x : E} (hx : ‖x‖ ≤ R) : radialCap Q β R x = Q x := by
  apply smoothMaximum_left
  have hs : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hw : radialWall β R x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hs)
  exact hw.trans (hQ x)

omit [InnerProductSpace ℝ E] in
theorem radialCap_outside_gap {Q : E → ℝ} {β R : ℝ} (hβ : 0 ≤ β) (hR : 0 ≤ R)
    (hQ : ∀ x, Q x ≤ 2 * β * ‖x‖ ^ 2) {x : E} (hx : 2 * R ≤ ‖x‖) :
    β * R ^ 2 ≤ radialWall β R x - Q x := by
  have hs : 4 * R ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hm := mul_le_mul_of_nonneg_left hs hβ
  have hn : 0 ≤ β * R ^ 2 := by positivity
  have hq := hQ x
  unfold radialWall
  nlinarith only [hm, hn, hq]

omit [InnerProductSpace ℝ E] in
theorem radialCap_outside {Q : E → ℝ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hQ : ∀ x, Q x ≤ 2 * β * ‖x‖ ^ 2) {x : E} (hx : 2 * R ≤ ‖x‖) :
    radialCap Q β R x = radialWall β R x - β * R ^ 2 / 2 :=
  smoothMaximum_right (by positivity) (radialCap_outside_gap hβ.le hR.le hQ hx)

omit [InnerProductSpace ℝ E] in
theorem radialCapWeight_bounds {Q : E → ℝ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R) (x : E) :
    0 ≤ radialCapWeight Q β R x ∧ radialCapWeight Q β R x ≤ 1 :=
  smoothRampSlope_bounds (by positivity) _

omit [InnerProductSpace ℝ E] in
theorem radialCapWeight_outside {Q : E → ℝ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hQ : ∀ x, Q x ≤ 2 * β * ‖x‖ ^ 2) {x : E} (hx : 2 * R ≤ ‖x‖) :
    radialCapWeight Q β R x = 1 := by
  have he := radialCap_outside_gap hβ.le hR.le hQ hx
  have hh : 0 < β * R ^ 2 := by positivity
  unfold radialCapWeight
  rw [smoothRampSlope_clamp hh]
  exact min_eq_left ((one_le_div hh).mpr he |>.trans (le_max_right _ _))

omit [InnerProductSpace ℝ E] in
theorem radialCapWeight_core {Q : E → ℝ} {β R : ℝ} (hβ : 0 ≤ β)
    (hQ : ∀ x, 0 ≤ Q x) {x : E} (hx : ‖x‖ ≤ R) : radialCapWeight Q β R x = 0 := by
  have hs : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hw : radialWall β R x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hs)
  have he : radialWall β R x - Q x ≤ 0 := by linarith [hQ x]
  simp [radialCapWeight, smoothRampSlope, scalarJoin, he]

theorem radialCapGradient_core {Q : E → ℝ} {G : E → E} {β R : ℝ} (hβ : 0 ≤ β)
    (hQ : ∀ x, 0 ≤ Q x) {x : E} (hx : ‖x‖ ≤ R) : radialCapGradient Q G β R x = G x := by
  simp [radialCapGradient, radialCapWeight_core hβ hQ hx]

theorem radialCapGradient_outside {Q : E → ℝ} {G : E → E} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hQ : ∀ x, Q x ≤ 2 * β * ‖x‖ ^ 2)
    {x : E} (hx : 2 * R ≤ ‖x‖) : radialCapGradient Q G β R x = (8 * β) • x := by
  simp [radialCapGradient, radialCapWeight_outside hβ hR hQ hx]

end FreshGradientMinimax

