import FreshGradientMinimax.TestingScalar

/-! The actual globally admissible testing objectives of Appendix D.
The perturbation is the explicit C² clip, with no analytic properties assumed. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

def testingObjective (L μ d R s : ℝ) (hμ : 0 < μ) (hR : 0 < R)
    (hκ : 1120 * μ ≤ L) (hs : |s| ≤ 1) : NCObjective 1 1 L μ where
  μ_pos := hμ
  μ_le_L := by linarith
  f x y := testingFunction (L / 16) (L / 16) μ d R s (realCoord x) (realCoord y)
  gradX x y := realVector (testingGradX (L / 16) (L / 16) d (realCoord x) (realCoord y))
  gradY x y := realVector (testingGradY (L / 16) μ R s (realCoord x) (realCoord y))
  derivative z := by
    have hx := (realCoord_hasFDerivAt z.1).comp z hasFDerivAt_fst
    have hy := (realCoord_hasFDerivAt z.2).comp z hasFDerivAt_snd
    have hc := (clipSquare_derivative hR (realCoord z.2)).comp_hasFDerivAt z hy
    have hx2 := ((hasDerivAt_id (realCoord z.1)).pow 2).comp_hasFDerivAt z hx
    have hy2 := ((hasDerivAt_id (realCoord z.2)).pow 2).comp_hasFDerivAt z hy
    apply ((((hx2.const_mul (L / 16 / 2)).add (hx.const_mul d)).add
      ((hx.const_mul (L / 16)).mul hy)).sub (hy2.const_mul (3 * μ))).add
        (hc.const_mul (s * μ)) |>.congr_fderiv
    apply ContinuousLinearMap.ext
    intro w
    simp [innerSL_apply, testingGradX, testingGradY, realVector, realCoord]
    ring
  joint_smooth x y x' y' := by
    simp only [realVector_sub, realVector_norm, sq_abs,
      ← realCoord_norm (x - x'), ← realCoord_norm (y - y'), realCoord_sub]
    exact testingFunction_jointSmooth hμ hR hκ hs d (realCoord x) (realCoord y)
      (realCoord x') (realCoord y')
  dual_strong x := by
    intro y z
    rw [realVector_inner, ← realCoord_norm (z - y), realCoord_sub, sq_abs]
    exact testingFunction_strongConcave hμ hR hs (L / 16) (L / 16) d
      (realCoord x) (realCoord y) (realCoord z)

variable {L μ d R s : ℝ} (hμ : 0 < μ) (hR : 0 < R)
  (hκ : 1120 * μ ≤ L) (hs : |s| ≤ 1)

theorem testingObjective_localized {G : ℝ} (hG : 0 ≤ G) :
    (testingObjective L μ d R s hμ hR hκ hs).DualLocalized G := by
  have hz := clipSquareSlope_identity hR (show |(0 : ℝ)| ≤ R by simpa using hR.le)
  simpa only [NCObjective.DualLocalized, testingObjective, testingGradY,
    realCoord_zero, hz, mul_zero, sub_self, add_zero, realVector_norm, abs_zero] using hG

theorem testingObjective_dualMax_of_root (x : Euclid 1) (y : ℝ)
    (hy : testingGradY (L / 16) μ R s (realCoord x) y = 0) :
    (testingObjective L μ d R s hμ hR hκ hs).dualMax x = realVector y := by
  apply Eq.symm
  apply NCObjective.dualMax_unique
  intro z
  have h := testingFunction_strongConcave hμ hR hs (L / 16) (L / 16) d
    (realCoord x) y (realCoord z)
  rw [hy, zero_mul, add_zero] at h
  have hn : 0 ≤ μ / 2 * (realCoord z - y) ^ 2 := by positivity
  change testingFunction (L / 16) (L / 16) μ d R s (realCoord x) (realCoord z) ≤
    testingFunction (L / 16) (L / 16) μ d R s (realCoord x) (realCoord (realVector y))
  rw [realCoord_vector]
  linarith

theorem testingObjective_dualMax_zero :
    (testingObjective L μ d R s hμ hR hκ hs).dualMax 0 = realVector 0 := by
  apply testingObjective_dualMax_of_root
  rw [testingGradY, realCoord_zero,
    clipSquareSlope_identity hR (show |(0 : ℝ)| ≤ R by simpa using hR.le)]
  ring

theorem testingObjective_value_zero :
    (testingObjective L μ d R s hμ hR hκ hs).value 0 = 0 := by
  rw [NCObjective.value_eq_max, testingObjective_dualMax_zero]
  simp only [testingObjective, realCoord_zero, realCoord_vector, testingFunction,
    clipSquare_identity hR (show |(0 : ℝ)| ≤ R by simpa using hR.le)]
  ring

end FreshGradientMinimax
