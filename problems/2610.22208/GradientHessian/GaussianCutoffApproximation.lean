import GradientHessian.GaussianBumpCutoff
import GradientHessian.GaussianMollifier

/-! Explicit compact smooth approximation of an arbitrary Lipschitz
function, with asymptotically unchanged Lipschitz constant and a uniform
pointwise growth bound. The functions are constructed by clipping,
spatial cutoff, and convolution against an actual normalized bump. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_compact_smooth_lipschitz_approximation {f : E → ℝ} {B : ℝ≥0}
    (hLip : LipschitzWith B f) :
    ∃ F : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ 2 (F n)) ∧
      (∀ n, HasCompactSupport (F n)) ∧
      (∀ n, LipschitzWith (approximationLipschitz B n) (F n)) ∧
      (∀ n x, ‖F n x‖ ≤ ‖f x‖ + ((B : ℝ) + 1)) ∧
      (∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) := by
  let φ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  obtain ⟨K, hK⟩ := compact_smooth_lipschitz_exists
    (show ContDiff ℝ 1 (φ : E → ℝ) from φ.contDiff) φ.hasCompactSupport
  let ψ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨approximationWidth n / 2, approximationWidth n,
      half_pos (approximationWidth_pos n), half_lt_self (approximationWidth_pos n)⟩
  let F : ℕ → E → ℝ := fun n =>
    mollify (ψ n) Measure.addHaar (cutoffApproximation φ K f n)
  have hc (n) := cutoffApproximation_lipschitz φ hK hLip n
  have herr (n) (x : E) : dist (F n x) (cutoffApproximation φ K f n x) ≤
      (approximationLipschitz B n : ℝ) * approximationWidth n :=
    mollify_error (ψ n) (hc n) x
  have hBn (n) : (approximationLipschitz B n : ℝ) ≤ (B : ℝ) + 1 :=
    add_le_add_left (approximationWidth_le_one n) _
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact mollify_smooth (ψ n) (hc n).continuous
  · intro n
    exact mollify_compact (ψ n) (cutoffApproximation_compact φ K f n)
  · intro n
    exact mollify_lipschitz (ψ n) (hc n)
  · intro n x
    have herror : dist (F n x) (cutoffApproximation φ K f n x) ≤ (B : ℝ) + 1 := by
      apply (herr n x).trans
      exact (mul_le_mul (hBn n) (approximationWidth_le_one n)
        (approximationWidth_pos n).le (by positivity)).trans_eq (mul_one _)
    have htri := dist_triangle (F n x) (cutoffApproximation φ K f n x) 0
    simp only [dist_zero_right] at htri
    linarith [cutoffApproximation_norm_le φ K f n x]
  · intro x
    have hzero : Tendsto (fun n => (approximationLipschitz B n : ℝ) * approximationWidth n)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using (approximationLipschitz_tendsto B).mul approximationWidth_tendsto
    have hd : Tendsto (fun n => dist (F n x) (cutoffApproximation φ K f n x)) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun n => herr n x) hzero
    exact (cutoffApproximation_tendsto φ K f x).congr_dist (by simpa only [dist_comm] using hd)

end GradientHessian.GaussianConcentration
