import MatchingBounds1005.CUPGMonitor
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # The actual proximal objective used in each accelerated phase -/
noncomputable section
open InnerProductSpace
open scoped ContDiff

namespace MatchingBounds1005.CUPG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def regularized (f : E → ℝ) (α : ℝ) (start x : E) : ℝ := f x + α * ‖x - start‖ ^ 2

theorem regularized_smooth {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (α : ℝ) (start : E) :
    ContDiff ℝ ∞ (regularized f α start) :=
  hf.add (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))

theorem regularized_hasGradientAt {f : E → ℝ} (hf : Differentiable ℝ f)
    (α : ℝ) (start x : E) :
    HasGradientAt (regularized f α start) (gradient f x + (2 * α) • (x - start)) x := by
  have hq := (((hasStrictFDerivAt_norm_sq (x - start)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const start)).const_mul α)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert (hf x).hasGradientAt.hasFDerivAt.add hq using 1
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, toDual_apply,
    innerSL_apply, smul_eq_mul, inner_add_left, real_inner_smul_left]
  ring

theorem regularized_gradient {f : E → ℝ} (hf : Differentiable ℝ f) (α : ℝ) (start x : E) :
    gradient (regularized f α start) x = gradient f x + (2 * α) • (x - start) :=
  (regularized_hasGradientAt hf α start x).gradient

theorem regularized_taylor_identity {f : E → ℝ} (hf : Differentiable ℝ f)
    (α : ℝ) (start x y : E) :
    regularized f α start y - regularized f α start x -
      ⟪gradient (regularized f α start) x, y - x⟫_ℝ =
        f y - f x - ⟪gradient f x, y - x⟫_ℝ + α * ‖y - x‖ ^ 2 := by
  rw [regularized_gradient hf]
  unfold regularized
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, real_inner_smul_left]
  simp only [real_inner_comm]
  ring

theorem regularized_smoothUpper {f : E → ℝ} (hf : Differentiable ℝ f) {L : ℝ}
    (hsm : SmoothUpper f L) (α : ℝ) (start : E) :
    SmoothUpper (regularized f α start) (L + 2 * α) := by
  intro x y
  have he := regularized_taylor_identity hf α start x y
  have h := hsm x y
  linarith

theorem regularized_gap_le {f : E → ℝ} {α Δ : ℝ} (hα : 0 ≤ α) (start : E)
    (hgap : ∀ z, f start - f z ≤ Δ) (z : E) :
    progressGap (regularized f α start) α start z ≤ Δ := by
  unfold progressGap regularized
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  have hn : 0 ≤ α * ‖z - start‖ ^ 2 := mul_nonneg hα (sq_nonneg _)
  linarith [hgap z]

theorem regularized_violation {f : E → ℝ} (hf : Differentiable ℝ f) (α : ℝ)
    (start u v : E) (hv : ¬ LocalConvex (regularized f α start) α v u) :
    f u - f v - ⟪gradient f v, u - v⟫_ℝ < -α / 2 * ‖u - v‖ ^ 2 := by
  have he := regularized_taylor_identity hf α start v u
  unfold LocalConvex at hv
  push_neg at hv
  linarith

/-- A small proximal gradient either gives stationarity or guaranteed
decrease in the original objective. -/
theorem regularized_small_gradient_decrease {f : E → ℝ} (hf : Differentiable ℝ f)
    {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) (start y : E)
    (hvalue : regularized f α start y ≤ f start)
    (hgrad : ‖gradient (regularized f α start) y‖ ≤ ε / 10)
    (hnonstationary : ε < ‖gradient f y‖) :
    f y ≤ f start - ε ^ 2 / (5 * α) := by
  rw [regularized_gradient hf] at hgrad
  have ht : ‖gradient f y‖ ≤ ‖gradient f y + (2 * α) • (y - start)‖ +
      ‖(2 * α) • (y - start)‖ := by
    have he : gradient f y = (gradient f y + (2 * α) • (y - start)) - (2 * α) • (y - start) := by abel
    conv_lhs => rw [he]
    exact norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * α)] at ht
  have hd : 9 * ε / 10 < 2 * α * ‖y - start‖ := by linarith
  have hsq : (9 * ε / 10) ^ 2 ≤ (2 * α * ‖y - start‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hd.le
  have hgoal : ε ^ 2 / (5 * α) ≤ α * ‖y - start‖ ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 5 * α)).2
    nlinarith only [hsq, sq_nonneg ε]
  unfold regularized at hvalue
  linarith

end MatchingBounds1005.CUPG
