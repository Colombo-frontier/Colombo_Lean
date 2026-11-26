import NCBall.ClarkeSmooth
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-! # The upper statement needs to exclude a zero-radius query ball

If a closed ball of radius zero is admitted, f(x)=2x has zero local gap
but no Goldstein-stationary output at accuracy one. This records the
parameter-boundary issue independently of the positive-radius results.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff
namespace NCBall

def zeroRadiusFunction (x : ℝ) : ℝ := 2 * x

theorem zeroRadiusFunction_smooth : ContDiff ℝ ∞ zeroRadiusFunction :=
  contDiff_const.mul contDiff_id

theorem zeroRadiusFunction_lipschitz (x y : ℝ) :
    |zeroRadiusFunction x - zeroRadiusFunction y| ≤ 2 * |x - y| := by
  simp only [zeroRadiusFunction, ← mul_sub, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  exact le_rfl

theorem zeroRadiusFunction_gradient (x : ℝ) : gradient zeroRadiusFunction x = 2 := by
  apply HasGradientAt.gradient
  simpa only [mul_one] using ((hasDerivAt_id x).const_mul 2).hasGradientAt'

theorem zeroRadiusFunction_residual {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) :
    clarkeGoldsteinResidual zeroRadiusFunction δ x = 2 := by
  rw [clarkeGoldsteinResidual_eq_of_C1 (zeroRadiusFunction_smooth.of_le (by norm_num))]
  have himage : (gradient zeroRadiusFunction) '' closedBall x δ = {2} := by
    ext v
    constructor
    · rintro ⟨y, _, rfl⟩
      exact zeroRadiusFunction_gradient y
    · intro hv
      refine ⟨x, mem_closedBall_self hδ, ?_⟩
      simpa only [mem_singleton_iff] using (zeroRadiusFunction_gradient x).trans (mem_singleton_iff.mp hv).symm
  rw [smoothGoldsteinResidual, smoothGoldsteinSet, himage, closedConvexHull_eq_closure_convexHull,
    convexHull_singleton, closure_singleton, infDist_singleton]
  norm_num [Real.dist_eq]

theorem zeroRadiusFunction_gap :
    ∃ xmin ∈ closedBall (0 : ℝ) 0,
      (∀ x ∈ closedBall (0 : ℝ) 0, zeroRadiusFunction xmin ≤ zeroRadiusFunction x) ∧
        zeroRadiusFunction 0 - zeroRadiusFunction xmin ≤ 0 := by
  refine ⟨0, by simp, ?_, by simp⟩
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  simp only [hx0, le_refl]

theorem zero_radius_success_impossible {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {δ : ℝ} (hδ : 0 ≤ δ) (output : Ω → ℝ) :
    μ.real {w | clarkeGoldsteinResidual zeroRadiusFunction δ (output w) ≤ 1} = 0 := by
  have hs : {w | clarkeGoldsteinResidual zeroRadiusFunction δ (output w) ≤ 1} = ∅ := by
    ext w
    simp [zeroRadiusFunction_residual hδ]
  rw [hs, measureReal_empty]

end NCBall
