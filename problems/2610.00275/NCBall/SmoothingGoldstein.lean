import NCBall.ClarkeSmooth
import Mathlib.Analysis.Convex.Integral

/-! # Goldstein transfer from an averaged-gradient formula

This proves the convex-geometric part of smoothing. The analytic identity
for the concrete ball smoothing, integrability, and almost-everywhere
differentiability must be established when this theorem is instantiated.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology
namespace NCBall

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_mem_clarke {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    gradient f x ∈ clarkeSubdifferential f x := by
  apply subset_closedConvexHull
  exact ⟨fun _ : ℕ => x, fun _ => hf, tendsto_const_nhds, tendsto_const_nhds⟩

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integral_gradient_mem_clarkeGoldstein (f : E → ℝ) (z : Ω → E) (x : E) (δ : ℝ)
    (hz : ∀ᵐ ω ∂μ, z ω ∈ closedBall x δ)
    (hdiff : ∀ᵐ ω ∂μ, DifferentiableAt ℝ f (z ω))
    (hint : Integrable (fun ω => gradient f (z ω)) μ) :
    (∫ ω, gradient f (z ω) ∂μ) ∈ clarkeGoldsteinSet f δ x := by
  apply Convex.integral_mem convex_closedConvexHull isClosed_closedConvexHull _ hint
  filter_upwards [hz, hdiff] with ω hzw hfw
  apply subset_closedConvexHull
  exact ⟨z ω, hzw, gradient_mem_clarke hfw⟩

theorem averaged_gradient_goldstein_subset (f h : E → ℝ) (z : E → Ω → E) {ρ ν : ℝ} (x : E)
    (hz : ∀ y, ∀ᵐ ω ∂μ, z y ω ∈ closedBall y ρ)
    (hdiff : ∀ y, ∀ᵐ ω ∂μ, DifferentiableAt ℝ f (z y ω))
    (hint : ∀ y, Integrable (fun ω => gradient f (z y ω)) μ)
    (hmean : ∀ y, gradient h y = ∫ ω, gradient f (z y ω) ∂μ) :
    smoothGoldsteinSet (gradient h) ν x ⊆ clarkeGoldsteinSet f (ρ + ν) x := by
  apply closedConvexHull_min _ convex_closedConvexHull isClosed_closedConvexHull
  rintro v ⟨y, hy, rfl⟩
  rw [hmean y]
  apply integral_gradient_mem_clarkeGoldstein f (z y) x (ρ + ν) _ (hdiff y) (hint y)
  filter_upwards [hz y] with ω hω
  rw [mem_closedBall] at hy hω ⊢
  exact (dist_triangle (z y ω) y x).trans (add_le_add hω hy)

theorem averaged_gradient_clarke_subset (f h : E → ℝ) (hh : ContDiff ℝ 1 h)
    (z : E → Ω → E) {ρ ν : ℝ} (x : E)
    (hz : ∀ y, ∀ᵐ ω ∂μ, z y ω ∈ closedBall y ρ)
    (hdiff : ∀ y, ∀ᵐ ω ∂μ, DifferentiableAt ℝ f (z y ω))
    (hint : ∀ y, Integrable (fun ω => gradient f (z y ω)) μ)
    (hmean : ∀ y, gradient h y = ∫ ω, gradient f (z y ω) ∂μ) :
    clarkeGoldsteinSet h ν x ⊆ clarkeGoldsteinSet f (ρ + ν) x := by
  rw [clarkeGoldsteinSet_eq_smooth (hh.differentiable le_rfl) (gradient_continuous_of_C1 hh)]
  exact averaged_gradient_goldstein_subset f h z x hz hdiff hint hmean

theorem averaged_gradient_residual_bound (f h : E → ℝ) (hh : ContDiff ℝ 1 h)
    (z : E → Ω → E) {ρ ν : ℝ} (hν : 0 ≤ ν) (x : E)
    (hz : ∀ y, ∀ᵐ ω ∂μ, z y ω ∈ closedBall y ρ)
    (hdiff : ∀ y, ∀ᵐ ω ∂μ, DifferentiableAt ℝ f (z y ω))
    (hint : ∀ y, Integrable (fun ω => gradient f (z y ω)) μ)
    (hmean : ∀ y, gradient h y = ∫ ω, gradient f (z y ω) ∂μ) :
    clarkeGoldsteinResidual f (ρ + ν) x ≤ clarkeGoldsteinResidual h ν x := by
  rw [clarkeGoldsteinResidual_eq_of_C1 hh]
  exact infDist_le_infDist_of_subset (averaged_gradient_goldstein_subset f h z x hz hdiff hint hmean)
    (smoothGoldsteinSet_nonempty (gradient h) hν x)

end NCBall
