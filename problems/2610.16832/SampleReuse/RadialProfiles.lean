import SampleReuse.CurvatureScalarBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory
open scoped Topology

namespace SampleReuse
noncomputable section

/-- Concrete choices of S and chi in the manuscript's radial extension. -/
def radialRise (r : ℝ) : ℝ := Real.smoothTransition (2*r-1)
def radialCutoff (r : ℝ) : ℝ := 1-Real.smoothTransition (r-1)
def radialWallPrimitive (r : ℝ) : ℝ := ∫ u in (0:ℝ)..r, radialRise u

theorem radialRise_contDiff (n : ℕ∞) : ContDiff ℝ n radialRise :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem radialCutoff_contDiff (n : ℕ∞) : ContDiff ℝ n radialCutoff :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem radialRise_mem (r : ℝ) : 0 ≤ radialRise r ∧ radialRise r ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem radialCutoff_mem (r : ℝ) : 0 ≤ radialCutoff r ∧ radialCutoff r ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (r-1)
  have h1 := Real.smoothTransition.le_one (r-1)
  dsimp [radialCutoff]
  constructor <;> linarith

theorem radialRise_zero {r : ℝ} (hr : r ≤ 1/2) : radialRise r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem radialRise_one {r : ℝ} (hr : 1 ≤ r) : radialRise r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem radialCutoff_one {r : ℝ} (hr : r ≤ 1) : radialCutoff r = 1 := by
  simp only [radialCutoff, Real.smoothTransition.zero_of_nonpos (by linarith : r-1 ≤ 0), sub_zero]

theorem radialCutoff_zero {r : ℝ} (hr : 2 ≤ r) : radialCutoff r = 0 := by
  simp only [radialCutoff, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ r-1), sub_self]

theorem smoothTransition_monotone : Monotone Real.smoothTransition := by
  intro x y hxy
  have ha := glue_monotone hxy
  have hb := glue_monotone (show 1-y ≤ 1-x by linarith)
  have hm := mul_le_mul ha hb (expNegInvGlue.nonneg (1-y)) (expNegInvGlue.nonneg y)
  change expNegInvGlue x / (expNegInvGlue x+expNegInvGlue (1-x)) ≤
    expNegInvGlue y / (expNegInvGlue y+expNegInvGlue (1-y))
  apply (div_le_div_iff₀ (Real.smoothTransition.pos_denom x) (Real.smoothTransition.pos_denom y)).mpr
  nlinarith

theorem radialRise_monotone : Monotone radialRise := by
  intro x y hxy
  exact smoothTransition_monotone (by linarith)

theorem radialCutoff_antitone : Antitone radialCutoff := by
  intro x y hxy
  have hh := smoothTransition_monotone (show x-1 ≤ y-1 by linarith)
  dsimp [radialCutoff]
  linarith

theorem radialWallPrimitive_hasDerivAt (r : ℝ) :
    HasDerivAt radialWallPrimitive (radialRise r) r := by
  have hc := (radialRise_contDiff 0).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem radialWallPrimitive_deriv : deriv radialWallPrimitive = radialRise :=
  funext (fun r => (radialWallPrimitive_hasDerivAt r).deriv)

theorem radialWallPrimitive_contDiff (n : ℕ∞) : ContDiff ℝ n radialWallPrimitive := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) n
  have hd : Differentiable ℝ radialWallPrimitive :=
    fun r => (radialWallPrimitive_hasDerivAt r).differentiableAt
  cases m with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ m =>
    rw [show ((m+1 : ℕ) : WithTop ℕ∞) = m+1 from rfl]
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨hd, by simp, ?_⟩
    rw [radialWallPrimitive_deriv]
    exact radialRise_contDiff m

theorem radialWallPrimitive_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ radialWallPrimitive r :=
  intervalIntegral.integral_nonneg_of_forall hr (fun u => (radialRise_mem u).1)

theorem radialWallPrimitive_zero {r : ℝ} (hr : r ≤ 1/2) :
    radialWallPrimitive r = 0 := by
  have he : (∫ u in (0:ℝ)..r, radialRise u) = ∫ _ in (0:ℝ)..r, (0:ℝ) :=
    intervalIntegral.integral_congr (fun u hu =>
      radialRise_zero (hu.2.trans (max_le (by norm_num) hr)))
  simpa only [radialWallPrimitive, intervalIntegral.integral_zero] using he

theorem radialWallPrimitive_tail {r : ℝ} (hr : 1 ≤ r) :
    radialWallPrimitive r = r+(radialWallPrimitive 1-1) := by
  have hc := (radialRise_contDiff 0).continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (0:ℝ) 1) (hc.intervalIntegrable 1 r)
  have he : (∫ u in (1:ℝ)..r, radialRise u) = ∫ _ in (1:ℝ)..r, (1:ℝ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (1:ℝ) r := by simpa only [Set.uIcc_of_le hr] using hu
    exact radialRise_one hu'.1
  rw [he, intervalIntegral.integral_const] at hadd
  simp only [smul_eq_mul, mul_one] at hadd
  dsimp [radialWallPrimitive]
  linarith

def radialWall (b R r : ℝ) : ℝ := b*R*radialWallPrimitive (r/R)

theorem radialWall_contDiff (b R : ℝ) (n : ℕ∞) : ContDiff ℝ n (radialWall b R) :=
  contDiff_const.mul ((radialWallPrimitive_contDiff n).comp (contDiff_id.div_const R))

theorem radialWall_hasDerivAt (b : ℝ) {R : ℝ} (hR : 0 < R) (r : ℝ) :
    HasDerivAt (radialWall b R) (b*radialRise (r/R)) r := by
  have h := ((radialWallPrimitive_hasDerivAt (r/R)).comp r
    ((hasDerivAt_id r).div_const R)).const_mul (b*R)
  convert h using 1
  field_simp
  ring

theorem radialWall_zero (b : ℝ) {R r : ℝ} (hR : 0 < R) (hr : r ≤ R/2) :
    radialWall b R r = 0 := by
  have hs : r/R ≤ 1/2 := (div_le_iff₀ hR).mpr (by linarith)
  simp only [radialWall, radialWallPrimitive_zero hs, mul_zero]

theorem radialWall_nonneg {b R r : ℝ} (hb : 0 ≤ b) (hR : 0 < R) (hr : 0 ≤ r) :
    0 ≤ radialWall b R r :=
  mul_nonneg (mul_nonneg hb hR.le) (radialWallPrimitive_nonneg (div_nonneg hr hR.le))

theorem radialWall_deriv_exterior (b : ℝ) {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    deriv (radialWall b R) r = b := by
  rw [(radialWall_hasDerivAt b hR r).deriv,
    radialRise_one ((le_div_iff₀ hR).mpr (by simpa using hr)), mul_one]

end
end SampleReuse
