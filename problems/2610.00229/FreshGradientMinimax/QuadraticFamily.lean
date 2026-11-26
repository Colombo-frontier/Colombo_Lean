import FreshGradientMinimax.AccelerationGeometry
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-! Known dual quadratics, represented by their deterministic curvature
and random linear coefficient. Their actual unique minimizer varies
continuously with that coefficient, so it is a legitimate random point. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped InnerProductSpace
variable {d : ℕ}

def quadraticFamily (Q : Euclid d → ℝ) (a : ℝ) (b x : Euclid d) : ℝ :=
  Q x + a / 2 * ‖x‖ ^ 2 - ⟪b, x⟫_ℝ

def quadraticGradient (grad : Euclid d → Euclid d) (a : ℝ) (b x : Euclid d) : Euclid d :=
  grad x + a • x - b

theorem quadraticFamily_increment (Q : Euclid d → ℝ) (a w : ℝ) (b v x : Euclid d) :
    quadraticFamily Q (a + w) (b + w • v) x =
      quadraticFamily Q a b x + w / 2 * ‖x - v‖ ^ 2 - w / 2 * ‖v‖ ^ 2 := by
  simp only [quadraticFamily, norm_sub_sq_real, inner_add_left, real_inner_smul_left]
  rw [real_inner_comm v x]
  ring

theorem quadraticGradient_increment (grad : Euclid d → Euclid d) (a w : ℝ) (b v x : Euclid d) :
    quadraticGradient grad (a + w) (b + w • v) x = quadraticGradient grad a b x + w • (x - v) := by
  simp only [quadraticGradient]
  module

theorem quadraticFamily_taylor (Q : Euclid d → ℝ) (grad : Euclid d → Euclid d)
    (a : ℝ) (b x y : Euclid d) :
    quadraticFamily Q a b y - quadraticFamily Q a b x - ⟪quadraticGradient grad a b x, y - x⟫_ℝ =
      Q y - Q x - ⟪grad x, y - x⟫_ℝ + a / 2 * ‖y - x‖ ^ 2 := by
  have hn : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
    have h := norm_add_sq_real x (y - x)
    rw [show x + (y - x) = y by abel] at h
    linarith
  simp only [quadraticFamily, quadraticGradient, inner_sub_left, inner_add_left, real_inner_smul_left]
  rw [hn]
  simp only [inner_sub_right]
  ring

namespace SmoothStrongModel
variable {Q : Euclid d → ℝ} {grad : Euclid d → Euclid d} {m H : ℝ}
variable (model : SmoothStrongModel Q grad m H)
include model

theorem quadratic_model (a : ℝ) (b : Euclid d) :
    SmoothStrongModel (quadraticFamily Q a b) (quadraticGradient grad a b) (m + a) (H + a) := by
  constructor
  · intro x
    have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    convert ((model.derivative x).add (hn.const_mul (a / 2))).sub (innerSL ℝ b).hasFDerivAt using 1
    ext h
    simp [quadraticGradient, innerSL_apply, inner_add_left, inner_sub_left, real_inner_smul_left]
    ring
  · intro x y
    have ht := quadraticFamily_taylor Q grad a b x y
    have hl := model.lower x y
    nlinarith only [ht, hl]
  · intro x y
    have ht := quadraticFamily_taylor Q grad a b x y
    have hu := model.upper x y
    nlinarith only [ht, hu]

theorem quadratic_minimum_exists (a : ℝ) (ha : 0 < m + a) (b : Euclid d) :
    ∃ x, ∀ y, quadraticFamily Q a b x ≤ quadraticFamily Q a b y :=
  strong_convex_minimum_exists ha (model.quadratic_model a b).lower (model.quadratic_model a b).continuous

def quadraticMin (a : ℝ) (ha : 0 < m + a) (b : Euclid d) : Euclid d :=
  Classical.choose (model.quadratic_minimum_exists a ha b)

theorem quadraticMin_minimizes (a : ℝ) (ha : 0 < m + a) (b y : Euclid d) :
    quadraticFamily Q a b (model.quadraticMin a ha b) ≤ quadraticFamily Q a b y :=
  Classical.choose_spec (model.quadratic_minimum_exists a ha b) y

theorem quadraticMin_gradient_zero (a : ℝ) (ha : 0 < m + a) (b : Euclid d) :
    quadraticGradient grad a b (model.quadraticMin a ha b) = 0 :=
  gradient_zero_at_global_min _ ((model.quadratic_model a b).derivative _)
    (model.quadraticMin_minimizes a ha b)

theorem quadraticMin_unique (a : ℝ) (ha : 0 < m + a) (b x : Euclid d)
    (hx : ∀ y, quadraticFamily Q a b x ≤ quadraticFamily Q a b y) : x = model.quadraticMin a ha b := by
  have h := ((model.quadratic_model a b).gap_quadratic_bounds _ (model.quadraticMin_minimizes a ha b) x).1
  have hle := hx (model.quadraticMin a ha b)
  have hz : ‖x - model.quadraticMin a ha b‖ ^ 2 ≤ 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x - model.quadraticMin a ha b)]))

theorem quadraticMin_lip (a : ℝ) (ha : 0 < m + a) (b c : Euclid d) :
    ‖model.quadraticMin a ha b - model.quadraticMin a ha c‖ ≤ (m + a)⁻¹ * ‖b - c‖ := by
  let x := model.quadraticMin a ha b
  let y := model.quadraticMin a ha c
  have hx := ((model.quadratic_model a b).gap_quadratic_bounds x (model.quadraticMin_minimizes a ha b) y).1
  have hy := ((model.quadratic_model a c).gap_quadratic_bounds y (model.quadraticMin_minimizes a ha c) x).1
  rw [norm_sub_rev y x] at hx
  have he : (quadraticFamily Q a b y - quadraticFamily Q a b x) +
      (quadraticFamily Q a c x - quadraticFamily Q a c y) = ⟪b - c, x - y⟫_ℝ := by
    simp only [quadraticFamily, inner_sub_left, inner_sub_right]
    ring
  have hi := real_inner_le_norm (b - c) (x - y)
  have hb : (m + a) * ‖x - y‖ ^ 2 ≤ ‖b - c‖ * ‖x - y‖ := by linarith
  by_cases hz : ‖x - y‖ = 0
  · change ‖x - y‖ ≤ _
    rw [hz]
    positivity
  · have hn : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have h : (m + a) * ‖x - y‖ ≤ ‖b - c‖ := by nlinarith
    change ‖x - y‖ ≤ _
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ ha).mpr (by linarith)

theorem quadraticMin_continuous (a : ℝ) (ha : 0 < m + a) : Continuous (model.quadraticMin a ha) := by
  apply (show LipschitzWith ⟨(m + a)⁻¹, inv_nonneg.mpr ha.le⟩ (model.quadraticMin a ha) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro b c
  simpa only [dist_eq_norm, NNReal.coe_mk] using model.quadraticMin_lip a ha b c

theorem quadraticFamily_joint_continuous (a : ℝ) :
    Continuous (fun z : Euclid d × Euclid d => quadraticFamily Q a z.1 z.2) :=
  ((model.continuous.comp continuous_snd).add (continuous_const.mul (continuous_snd.norm.pow 2))).sub
    (continuous_fst.inner continuous_snd)

end SmoothStrongModel
end FreshGradientMinimax
