import FreshGradientMinimax.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

/-! Existence, uniqueness and quantitative stability of the dual maximizer.
The maximizer is derived from strong concavity and properness of the underlying
finite-dimensional space; it is not supplied as instance data. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def StrongConcaveGradient (f : E → ℝ) (g : E → E) (μ : ℝ) : Prop :=
  ∀ y z, f z ≤ f y + ⟪g y, z - y⟫_ℝ - μ / 2 * ‖z - y‖ ^ 2

theorem strong_concave_gradient_monotone {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hc : StrongConcaveGradient f g μ) (y z : E) :
    μ * ‖y - z‖ ^ 2 ≤ ⟪g z - g y, y - z⟫_ℝ := by
  have h1 := hc y z
  have h2 := hc z y
  rw [norm_sub_rev z y] at h1
  have hi : ⟪g y, z - y⟫_ℝ = -⟪g y, y - z⟫_ℝ := by
    simp only [inner_sub_right]
    ring
  rw [hi] at h1
  rw [inner_sub_left]
  linarith

theorem gradient_zero_at_global_max {f : E → ℝ} {g : E → E} (y : E)
    (hder : HasFDerivAt f (innerSL ℝ (g y)) y) (hmax : ∀ z, f z ≤ f y) : g y = 0 := by
  have hl : IsLocalMax f y := Filter.Eventually.of_forall hmax
  have he := hl.hasFDerivAt_eq_zero hder
  have hv := congrArg (fun l : E →L[ℝ] ℝ => l (g y)) he
  simp only [innerSL_apply, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at hv
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (g y)]

theorem strong_concave_maximum_unique {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hμ : 0 < μ) (hc : StrongConcaveGradient f g μ)
    (hder : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (y z : E) (hy : ∀ w, f w ≤ f y) (hz : ∀ w, f w ≤ f z) : y = z := by
  have h := strong_concave_gradient_monotone hc y z
  rw [gradient_zero_at_global_max y (hder y) hy,
    gradient_zero_at_global_max z (hder z) hz, sub_self, inner_zero_left] at h
  have hsq : ‖y - z‖ ^ 2 ≤ 0 := (mul_le_mul_left hμ).mp (by simpa using h)
  have hn : ‖y - z‖ = 0 := by nlinarith [norm_nonneg (y - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem strong_concave_maximum_exists [ProperSpace E]
    {f : E → ℝ} {g : E → E} {μ : ℝ} (hμ : 0 < μ)
    (hc : StrongConcaveGradient f g μ) (hf : Continuous f) :
    ∃ y, ∀ z, f z ≤ f y := by
  let R := 2 * ‖g 0‖ / μ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall (0 : E) R).exists_isMaxOn
    (show (Metric.closedBall (0 : E) R).Nonempty from ⟨0, by simpa using hR⟩) hf.continuousOn
  refine ⟨y, fun z => ?_⟩
  by_cases hz : z ∈ Metric.closedBall (0 : E) R
  · exact hmax hz
  · have hnorm : R < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have h0 : f 0 ≤ f y := hmax (by simpa using hR)
    have hs := hc 0 z
    simp only [sub_zero] at hs
    have hcs := real_inner_le_norm (g 0) z
    have hRμ : R * μ = 2 * ‖g 0‖ + μ := by dsimp [R]; field_simp
    have hμnorm : 2 * ‖g 0‖ < μ * ‖z‖ := by nlinarith
    have hquad : ‖g 0‖ * ‖z‖ ≤ μ / 2 * ‖z‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hμnorm.le (norm_nonneg z)]
    linarith

theorem dual_residual_distance_bounds {f : E → ℝ} {g : E → E} {μ L : ℝ}
    (hc : StrongConcaveGradient f g μ) (ystar : E) (hz : g ystar = 0)
    (hLip : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (y : E) :
    μ * ‖y - ystar‖ ≤ ‖g y‖ ∧ ‖g y‖ ≤ L * ‖y - ystar‖ := by
  have hmono := strong_concave_gradient_monotone hc y ystar
  rw [hz, zero_sub] at hmono
  have hl := residual_controls_distance μ (-g y) (y - ystar) hmono
  have hu := hLip y ystar
  simp only [norm_neg] at hl
  simpa only [hz, sub_zero] using And.intro hl hu

end FreshGradientMinimax
