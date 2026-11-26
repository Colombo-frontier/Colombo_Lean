import GradientHessian.GaussianClipping
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic

/-! A compact Lipschitz truncation with constants converging to the input
constant. A fixed actual smooth bump supplies the spatial cutoff. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem compact_smooth_lipschitz_exists {u : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) : ∃ K : ℝ≥0, LipschitzWith K u := by
  obtain ⟨C, hC⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hu.continuous_fderiv (by norm_num))
  have hCn : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨⟨C, hCn⟩, lipschitzWith_of_nnnorm_fderiv_le (hu.differentiable (by norm_num)) ?_⟩
  intro x
  exact_mod_cast hC x

def approximationWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem approximationWidth_pos (n : ℕ) : 0 < approximationWidth n := by
  dsimp [approximationWidth]
  positivity

theorem approximationWidth_le_one (n : ℕ) : approximationWidth n ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem approximationWidth_tendsto : Tendsto approximationWidth atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def approximationLipschitz (B : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  B + ⟨approximationWidth n, (approximationWidth_pos n).le⟩

theorem approximationLipschitz_tendsto (B : ℝ≥0) :
    Tendsto (fun n => (approximationLipschitz B n : ℝ)) atTop (𝓝 (B : ℝ)) := by
  simpa only [approximationLipschitz, NNReal.coe_add, NNReal.coe_mk, add_zero] using
    approximationWidth_tendsto.const_add (B : ℝ)

def cutoffScale (K : ℝ≥0) (n : ℕ) : ℝ := approximationWidth n ^ 2 / ((K : ℝ) + 1)

theorem cutoffScale_pos (K : ℝ≥0) (n : ℕ) : 0 < cutoffScale K n := by
  exact div_pos (sq_pos_of_pos (approximationWidth_pos n)) (by positivity)

theorem cutoffScale_tendsto (K : ℝ≥0) : Tendsto (cutoffScale K) atTop (𝓝 0) := by
  simpa only [cutoffScale, zero_pow (by norm_num : 2 ≠ 0), zero_div] using
    (approximationWidth_tendsto.pow 2).div_const ((K : ℝ) + 1)

def cutoffApproximation (φ : ContDiffBump (0 : E)) (K : ℝ≥0) (f : E → ℝ) (n : ℕ) (x : E) : ℝ :=
  φ (cutoffScale K n • x) * scalarClip ((n : ℝ) + 1) (f x)

theorem cutoffApproximation_compact (φ : ContDiffBump (0 : E)) (K : ℝ≥0) (f : E → ℝ) (n : ℕ) :
    HasCompactSupport (cutoffApproximation φ K f n) :=
  (φ.hasCompactSupport.comp_smul (cutoffScale_pos K n).ne').mul_right

theorem cutoffApproximation_norm_le (φ : ContDiffBump (0 : E)) (K : ℝ≥0) (f : E → ℝ)
    (n : ℕ) (x : E) : ‖cutoffApproximation φ K f n x‖ ≤ ‖f x‖ := by
  rw [cutoffApproximation, norm_mul, Real.norm_of_nonneg φ.nonneg]
  exact (mul_le_mul φ.le_one (scalarClip_norm_le_input (by positivity) (f x))
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem cutoffApproximation_tendsto (φ : ContDiffBump (0 : E)) (K : ℝ≥0) (f : E → ℝ) (x : E) :
    Tendsto (fun n => cutoffApproximation φ K f n x) atTop (𝓝 (f x)) := by
  have hs : Tendsto (fun n => cutoffScale K n • x) atTop (𝓝 (0 : E)) := by
    simpa only [zero_smul] using (cutoffScale_tendsto K).smul_const x
  have hp : φ (0 : E) = 1 := φ.one_of_mem_closedBall (by simp [φ.rIn_pos.le])
  have h := (φ.continuous.continuousAt.tendsto.comp hs).mul (scalarClip_tendsto (f x))
  simpa only [cutoffApproximation, hp, one_mul] using h

theorem cutoffApproximation_lipschitz (φ : ContDiffBump (0 : E)) {K B : ℝ≥0}
    (hφ : LipschitzWith K (φ : E → ℝ)) {f : E → ℝ} (hLip : LipschitzWith B f) (n : ℕ) :
    LipschitzWith (approximationLipschitz B n) (cutoffApproximation φ K f n) := by
  have hclip : LipschitzWith B (fun x => scalarClip ((n : ℝ) + 1) (f x)) := by
    simpa only [one_mul] using (scalarClip_lipschitz ((n : ℝ) + 1)).comp hLip
  have hcoef : (K : ℝ) * cutoffScale K n * ((n : ℝ) + 1) ≤ approximationWidth n := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hk : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have he : (K : ℝ) * cutoffScale K n * ((n : ℝ) + 1) =
        ((K : ℝ) / ((K : ℝ) + 1)) * approximationWidth n := by
      dsimp [cutoffScale, approximationWidth]
      field_simp
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_right ((div_le_one hk).mpr (by linarith))
      (approximationWidth_pos n).le).trans_eq (one_mul _)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let ux := φ (cutoffScale K n • x)
  let uy := φ (cutoffScale K n • y)
  let vx := scalarClip ((n : ℝ) + 1) (f x)
  let vy := scalarClip ((n : ℝ) + 1) (f y)
  have hu : ‖ux - uy‖ ≤ (K : ℝ) * cutoffScale K n * dist x y := by
    have h := hφ.dist_le_mul (cutoffScale K n • x) (cutoffScale K n • y)
    simpa only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (cutoffScale_pos K n), mul_assoc] using h
  have hv : ‖vx - vy‖ ≤ (B : ℝ) * dist x y := hclip.dist_le_mul x y
  have he : ux * vx - uy * vy = ux * (vx - vy) + (ux - uy) * vy := by ring
  change ‖ux * vx - uy * vy‖ ≤ ((B : ℝ) + approximationWidth n) * dist x y
  rw [he]
  calc
    _ ≤ ‖ux * (vx - vy)‖ + ‖(ux - uy) * vy‖ := norm_add_le _ _
    _ ≤ (B : ℝ) * dist x y + ((K : ℝ) * cutoffScale K n * dist x y) * ((n : ℝ) + 1) := by
      rw [norm_mul, norm_mul]
      apply add_le_add
      · exact (mul_le_mul (show ‖ux‖ ≤ 1 by rw [Real.norm_of_nonneg φ.nonneg]; exact φ.le_one)
          hv (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      · exact mul_le_mul hu (scalarClip_norm_le (by positivity) (f y)) (norm_nonneg _)
          (mul_nonneg (mul_nonneg K.coe_nonneg (cutoffScale_pos K n).le) dist_nonneg)
    _ ≤ ((B : ℝ) + approximationWidth n) * dist x y := by
      have h := mul_le_mul_of_nonneg_right hcoef (dist_nonneg (x := x) (y := y))
      nlinarith only [h]

end GradientHessian.GaussianConcentration
