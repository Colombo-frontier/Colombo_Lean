import SampleReuse.CurvatureGate
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace SampleReuse
noncomputable section

def curvaturePotential (u : ℝ) : ℝ := 4*(Real.exp (-(u^2)/4)-1)
def curvaturePotentialFirst (u : ℝ) : ℝ := -2*u*Real.exp (-(u^2)/4)
def curvaturePotentialSecond (u : ℝ) : ℝ := (u^2-2)*Real.exp (-(u^2)/4)

theorem curvaturePotential_contDiff (n : ℕ∞) : ContDiff ℝ n curvaturePotential :=
  contDiff_const.mul ((((contDiff_id.pow 2).neg.div_const 4).exp).sub contDiff_const)

theorem curvaturePotential_hasDerivAt (u : ℝ) :
    HasDerivAt curvaturePotential (curvaturePotentialFirst u) u := by
  have h := (((((hasDerivAt_id u).pow 2).neg.div_const 4).exp).sub_const 1).const_mul 4
  convert h using 1
  dsimp [curvaturePotential, curvaturePotentialFirst]
  ring

theorem curvaturePotentialFirst_hasDerivAt (u : ℝ) :
    HasDerivAt curvaturePotentialFirst (curvaturePotentialSecond u) u := by
  have h := ((hasDerivAt_id u).const_mul (-2)).mul
    ((((hasDerivAt_id u).pow 2).neg.div_const 4).exp)
  convert h using 1
  dsimp [curvaturePotentialFirst, curvaturePotentialSecond]
  ring

theorem curvaturePotential_deriv : deriv curvaturePotential = curvaturePotentialFirst :=
  funext (fun u => (curvaturePotential_hasDerivAt u).deriv)

theorem curvaturePotential_second_deriv :
    deriv (deriv curvaturePotential) = curvaturePotentialSecond := by
  rw [curvaturePotential_deriv]
  exact funext (fun u => (curvaturePotentialFirst_hasDerivAt u).deriv)

theorem curvaturePotential_range (u : ℝ) : -4 ≤ curvaturePotential u ∧ curvaturePotential u ≤ 0 := by
  have hp := Real.exp_nonneg (-(u^2)/4)
  have hu : Real.exp (-(u^2)/4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
  unfold curvaturePotential
  constructor <;> linarith

theorem curvaturePotential_zero : curvaturePotential 0 = 0 := by
  norm_num [curvaturePotential]

theorem curvaturePotential_negative_curvature {u : ℝ} (hu : |u| ≤ 1) :
    deriv (deriv curvaturePotential) u ≤ -Real.exp (-(1:ℝ)/4) := by
  have hs : u^2 ≤ 1 := by nlinarith [(abs_le.mp hu).1, (abs_le.mp hu).2]
  have he : Real.exp (-(1:ℝ)/4) ≤ Real.exp (-(u^2)/4) :=
    Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right (show u^2-2 ≤ -1 by linarith)
    (Real.exp_nonneg (-(u^2)/4))
  rw [curvaturePotential_second_deriv]
  unfold curvaturePotentialSecond
  linarith

theorem glue_monotone : Monotone expNegInvGlue := by
  apply monotone_of_deriv_nonneg (fun u => (glue_hasDerivAt u).differentiableAt)
  intro u
  rw [(glue_hasDerivAt u).deriv]
  exact mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _)

theorem glue_le_one (u : ℝ) : expNegInvGlue u ≤ 1 := by
  by_cases hu : u ≤ 0
  · simp [expNegInvGlue.zero_of_nonpos hu]
  · rw [expNegInvGlue, if_neg hu]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge hu)))

theorem curvatureGate_le_one (u : ℝ) : curvatureGate u ≤ 1 := by
  unfold curvatureGate
  rcases le_total 0 u with hu | hu
  · rw [expNegInvGlue.zero_of_nonpos (show -u-1/2 ≤ 0 by linarith), add_zero]
    exact glue_le_one _
  · rw [expNegInvGlue.zero_of_nonpos (show u-1/2 ≤ 0 by linarith), zero_add]
    exact glue_le_one _

theorem curvatureGate_completed {u : ℝ} (hu : 1 ≤ |u|) :
    Real.exp (-2) ≤ curvatureGate u := by
  have hh : expNegInvGlue (1/2) = Real.exp (-2) := by norm_num [expNegInvGlue]
  unfold curvatureGate
  rcases le_total 0 u with hp | hn
  · rw [abs_of_nonneg hp] at hu
    have hm := glue_monotone (show (1:ℝ)/2 ≤ u-1/2 by linarith)
    rw [hh] at hm
    linarith [expNegInvGlue.nonneg (-u-1/2)]
  · rw [abs_of_nonpos hn] at hu
    have hm := glue_monotone (show (1:ℝ)/2 ≤ -u-1/2 by linarith)
    rw [hh] at hm
    linarith [expNegInvGlue.nonneg (u-1/2)]

/-- The scalar diagonal estimate used at the first incomplete coordinate. -/
theorem curvature_link_negative {p u : ℝ} (hp : 1 ≤ |p|) (hu : |u| ≤ 1) (v : ℝ) :
    curvatureGate p * deriv (deriv curvaturePotential) u +
      deriv (deriv curvatureGate) u * curvaturePotential v ≤ -Real.exp (-(9:ℝ)/4) := by
  have hfirst := mul_le_mul_of_nonneg_left (curvaturePotential_negative_curvature hu)
    (curvatureGate_nonneg p)
  have hsecond := mul_le_mul_of_nonpos_right (curvatureGate_completed hp)
    (neg_nonpos.mpr (Real.exp_nonneg (-(1:ℝ)/4)))
  have hout := mul_nonpos_of_nonneg_of_nonpos (curvatureGate_convex_region hu)
    (curvaturePotential_range v).2
  have he : Real.exp (-2)*(-Real.exp (-(1:ℝ)/4)) = -Real.exp (-(9:ℝ)/4) := by
    rw [mul_neg, ← Real.exp_add]
    norm_num
  rw [he] at hsecond
  linarith

end
end SampleReuse
