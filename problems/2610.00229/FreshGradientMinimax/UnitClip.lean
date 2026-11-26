import FreshGradientMinimax.ScalarJoin
import FreshGradientMinimax.ClipPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-! A concrete C² odd clip at unit radius. All derivatives at the joins
are established, not inferred merely from formulas away from the joins. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax

def positiveClip : ℝ → ℝ := scalarJoin 1 id
  (scalarJoin 2 (fun t => clipTransition (t - 1)) (fun _ => 3 / 2))
def positiveClipSlope : ℝ → ℝ := scalarJoin 1 (fun _ => 1)
  (scalarJoin 2 (fun t => clipTransitionSlope (t - 1)) (fun _ => 0))
def positiveClipCurve : ℝ → ℝ := scalarJoin 1 (fun _ => 0)
  (scalarJoin 2 (fun t => clipTransitionCurve (t - 1)) (fun _ => 0))

theorem positiveClip_derivative (t : ℝ) : HasDerivAt positiveClip (positiveClipSlope t) t := by
  apply scalarJoin_hasDerivAt
  · exact hasDerivAt_id
  · intro x
    apply scalarJoin_hasDerivAt
    · intro y
      simpa only [mul_one, id_eq, Function.comp_def] using (clipTransition_derivative (y - 1)).comp y ((hasDerivAt_id y).sub_const 1)
    · exact fun x => hasDerivAt_const x (3 / 2)
    · norm_num [clipTransition]
    · norm_num [clipTransitionSlope]
  · norm_num [scalarJoin, clipTransition]
  · norm_num [scalarJoin, clipTransitionSlope]

theorem positiveClipSlope_derivative (t : ℝ) : HasDerivAt positiveClipSlope (positiveClipCurve t) t := by
  apply scalarJoin_hasDerivAt
  · exact fun x => hasDerivAt_const x 1
  · intro x
    apply scalarJoin_hasDerivAt
    · intro y
      simpa only [mul_one, id_eq, Function.comp_def] using (clipTransitionSlope_derivative (y - 1)).comp y ((hasDerivAt_id y).sub_const 1)
    · exact fun x => hasDerivAt_const x 0
    · norm_num [clipTransitionSlope]
    · norm_num [clipTransitionCurve]
  · norm_num [scalarJoin, clipTransitionSlope]
  · norm_num [scalarJoin, clipTransitionCurve]

theorem positiveClipCurve_continuous : Continuous positiveClipCurve := by
  apply scalarJoin_continuous _ _ _ continuous_const
  · apply scalarJoin_continuous _ _ _ _ continuous_const
    · norm_num [clipTransitionCurve]
    · unfold clipTransitionCurve; fun_prop
  · norm_num [scalarJoin, clipTransitionCurve]

def unitClip (t : ℝ) : ℝ := scalarJoin 0 (fun x => -positiveClip (-x)) positiveClip t
def unitClipSlope (t : ℝ) : ℝ := scalarJoin 0 (fun x => positiveClipSlope (-x)) positiveClipSlope t
def unitClipCurve (t : ℝ) : ℝ := scalarJoin 0 (fun x => -positiveClipCurve (-x)) positiveClipCurve t

theorem unitClip_derivative (t : ℝ) : HasDerivAt unitClip (unitClipSlope t) t := by
  apply scalarJoin_hasDerivAt
  · intro x
    convert ((positiveClip_derivative (-x)).comp x (hasDerivAt_id x).neg).neg using 1
    simp
  · exact positiveClip_derivative
  · norm_num [positiveClip, scalarJoin]
  · norm_num [positiveClipSlope, scalarJoin]

theorem unitClipSlope_derivative (t : ℝ) : HasDerivAt unitClipSlope (unitClipCurve t) t := by
  apply scalarJoin_hasDerivAt
  · intro x
    convert (positiveClipSlope_derivative (-x)).comp x (hasDerivAt_id x).neg using 1
    simp
  · exact positiveClipSlope_derivative
  · norm_num [positiveClipSlope, scalarJoin]
  · norm_num [positiveClipCurve, scalarJoin]

theorem unitClipCurve_continuous : Continuous unitClipCurve := by
  apply scalarJoin_continuous
  · exact (positiveClipCurve_continuous.comp continuous_neg).neg
  · exact positiveClipCurve_continuous
  · norm_num [positiveClipCurve, scalarJoin]

theorem unitClip_continuous : Continuous unitClip := continuous_iff_continuousAt.mpr
  (fun t => (unitClip_derivative t).continuousAt)

theorem unitClipSlope_continuous : Continuous unitClipSlope := continuous_iff_continuousAt.mpr
  (fun t => (unitClipSlope_derivative t).continuousAt)

theorem unitClip_contDiff : ContDiff ℝ 2 unitClip := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun t => (unitClip_derivative t).differentiableAt, ?_, ?_⟩
  · norm_num
  · rw [deriv_eq unitClip_derivative, contDiff_one_iff_deriv]
    refine ⟨fun t => (unitClipSlope_derivative t).differentiableAt, ?_⟩
    rw [deriv_eq unitClipSlope_derivative]
    exact unitClipCurve_continuous

end FreshGradientMinimax
