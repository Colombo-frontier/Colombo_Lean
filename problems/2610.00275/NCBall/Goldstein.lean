import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
# The smooth Goldstein reduction (Section 10)

For a smooth function, the Goldstein set is the closed convex hull of nearby
gradients. We first prove the geometric statement for an arbitrary Lipschitz
vector field, then specialize it to the actual gradient.
-/

noncomputable section
open Set Metric

namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def smoothGoldsteinSet (g : E → E) (δ : ℝ) (x : E) : Set E :=
  closedConvexHull ℝ (g '' closedBall x δ)

def smoothGoldsteinResidual (g : E → E) (δ : ℝ) (x : E) : ℝ :=
  infDist 0 (smoothGoldsteinSet g δ x)

theorem mem_smoothGoldsteinSet_self (g : E → E) {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    g x ∈ smoothGoldsteinSet g δ x := by
  apply subset_closedConvexHull
  exact mem_image_of_mem g (mem_closedBall_self hδ)

theorem smoothGoldsteinSet_nonempty (g : E → E) {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    (smoothGoldsteinSet g δ x).Nonempty :=
  ⟨g x, mem_smoothGoldsteinSet_self g hδ x⟩

theorem smoothGoldsteinSet_subset_closedBall (g : E → E) {δ H : ℝ}
    (hH : 0 ≤ H) (x : E)
    (hg : ∀ y ∈ closedBall x δ, ‖g y - g x‖ ≤ H * ‖y - x‖) :
    smoothGoldsteinSet g δ x ⊆ closedBall (g x) (H * δ) := by
  apply closedConvexHull_min _ (convex_closedBall (g x) (H * δ)) isClosed_closedBall
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_closedBall, dist_eq_norm]
  exact (hg y hy).trans (mul_le_mul_of_nonneg_left (by
    simpa only [mem_closedBall, dist_eq_norm] using hy) hH)

/-- Equation (10.1), including the closure and infimum steps. -/
theorem norm_le_smoothGoldsteinResidual_add (g : E → E) {δ H : ℝ}
    (hδ : 0 ≤ δ) (hH : 0 ≤ H) (x : E)
    (hg : ∀ y ∈ closedBall x δ, ‖g y - g x‖ ≤ H * ‖y - x‖) :
    ‖g x‖ ≤ smoothGoldsteinResidual g δ x + H * δ := by
  have h : ‖g x‖ - H * δ ≤ infDist 0 (smoothGoldsteinSet g δ x) := by
    apply (le_infDist (smoothGoldsteinSet_nonempty g hδ x)).2
    intro v hv
    have hv' := smoothGoldsteinSet_subset_closedBall g hH x hg hv
    rw [mem_closedBall, dist_eq_norm] at hv'
    have hnorm : ‖g x‖ ≤ ‖v - g x‖ + ‖v‖ := by
      calc
        ‖g x‖ = ‖(g x - v) + v‖ := by rw [sub_add_cancel]
        _ ≤ ‖g x - v‖ + ‖v‖ := norm_add_le _ _
        _ = ‖v - g x‖ + ‖v‖ := by rw [norm_sub_rev]
    rw [dist_zero_left]
    linarith
  exact sub_le_iff_le_add.mp h

/-- Equation (10.3): Goldstein accuracy ε implies gradient accuracy 2ε. -/
theorem smoothGoldstein_implies_norm_le_two_mul (g : E → E) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (x : E)
    (hg : ∀ y ∈ closedBall x δ, ‖g y - g x‖ ≤ (ε / δ) * ‖y - x‖)
    (hstat : smoothGoldsteinResidual g δ x ≤ ε) :
    ‖g x‖ ≤ 2 * ε := by
  have h := norm_le_smoothGoldsteinResidual_add g hδ.le (div_nonneg hε hδ.le) x hg
  rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at h
  linarith

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The same reduction for mathlib's gradient of a real-valued function. -/
theorem gradient_le_goldstein_add (f : E → ℝ) {δ H : ℝ}
    (hδ : 0 ≤ δ) (hH : 0 ≤ H) (x : E)
    (hg : ∀ y ∈ closedBall x δ,
      ‖gradient f y - gradient f x‖ ≤ H * ‖y - x‖) :
    ‖gradient f x‖ ≤ smoothGoldsteinResidual (gradient f) δ x + H * δ :=
  norm_le_smoothGoldsteinResidual_add (gradient f) hδ hH x hg

end NCBall
