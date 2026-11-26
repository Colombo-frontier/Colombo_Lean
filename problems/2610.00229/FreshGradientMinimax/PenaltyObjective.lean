import FreshGradientMinimax.PenaltySaddle
import FreshGradientMinimax.RealCoordinate
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! An admissible NC--SC objective built from a convex differentiable penalty.
The following PathObjective module supplies the explicit capped path formula
and proves every analytic hypothesis of this general constructor. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def penaltyObjective {dy : ℕ} (Q : Euclid dy → ℝ) (G : Euclid dy → Euclid dy)
    (L μ d M : ℝ) (u v : Euclid dy) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hu : ‖u‖ ≤ 1)
    (hc : ConvexOn ℝ Set.univ Q) (hd : ∀ y, HasFDerivAt Q (innerSL ℝ (G y)) y)
    (hG : ∀ y y', ‖G y - G y'‖ ≤ L / 8 * ‖y - y'‖) : NCObjective 1 dy L μ where
  μ_pos := hμ
  μ_le_L := by linarith
  f x y := penaltySaddleFunction Q (L / 4) (L / 8) μ d M u v (realCoord x) y
  gradX x y := realVector (penaltySaddleGradX (L / 4) (L / 8) d u (realCoord x) y)
  gradY x y := penaltySaddleGradY G (L / 8) μ M u v (realCoord x) y
  derivative z := by
    have hx := (realCoord_hasFDerivAt z.1).comp z hasFDerivAt_fst
    have hu' := (innerSL ℝ u).hasFDerivAt.comp z hasFDerivAt_snd
    have hv' := (innerSL ℝ v).hasFDerivAt.comp z hasFDerivAt_snd
    have hy2 := (hasStrictFDerivAt_norm_sq z.2).hasFDerivAt.comp z hasFDerivAt_snd
    have hq := (hd z.2).comp z hasFDerivAt_snd
    have hx2 := ((hasDerivAt_id (realCoord z.1)).pow 2).comp_hasFDerivAt z hx
    apply (((((hx2.const_mul (L / 4 / 2)).add (hx.const_mul d)).add
      ((hx.const_mul (L / 8)).mul hu')).sub (hy2.const_mul (μ / 2))).sub hq).add
        (hv'.const_mul M) |>.congr_fderiv
    apply ContinuousLinearMap.ext
    intro w
    simp [innerSL_apply, penaltySaddleGradX, penaltySaddleGradY,
      real_inner_smul_left, inner_add_left, inner_sub_left, realVector, realCoord]
    ring
  joint_smooth x y x' y' := by
    rw [realVector_sub, realVector_norm, sq_abs]
    have h := penaltySaddle_jointSmooth hμ hκ hG d M u v hu (realCoord x) (realCoord x') y y'
    rw [← realCoord_sub, ← sq_abs (realCoord (x - x')), realCoord_norm] at h
    exact h
  dual_strong x := penaltySaddle_strongConcave hc hd (L / 4) (L / 8) μ d M u v (realCoord x)

theorem penaltyObjective_origin {dy : ℕ} (Q : Euclid dy → ℝ) (G : Euclid dy → Euclid dy)
    (L μ d M : ℝ) (u v : Euclid dy) (hμ : 0 < μ) (hκ : 4 * μ ≤ L) (hu : ‖u‖ ≤ 1)
    (hc : ConvexOn ℝ Set.univ Q) (hd : ∀ y, HasFDerivAt Q (innerSL ℝ (G y)) y)
    (hG : ∀ y y', ‖G y - G y'‖ ≤ L / 8 * ‖y - y'‖) (hG0 : G 0 = 0) :
    (penaltyObjective Q G L μ d M u v hμ hκ hu hc hd hG).gradY 0 0 = M • v := by
  simp [penaltyObjective, penaltySaddleGradY, hG0]

end FreshGradientMinimax
