import NCBall.Goldstein
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Clarke limits and the smooth Goldstein definition

In finite-dimensional Euclidean spaces the Clarke subdifferential can be
described by the closed convex hull of limits of gradients at differentiable
points. This file states that definition explicitly and proves its reduction
for differentiable functions with continuous gradient. No nonsmooth
regularity or Rademacher theorem is assumed in this reduction.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def limitingGradients (f : E → ℝ) (x : E) : Set E :=
  {v | ∃ z : ℕ → E, (∀ k, DifferentiableAt ℝ f (z k)) ∧
    Tendsto z atTop (𝓝 x) ∧ Tendsto (fun k => gradient f (z k)) atTop (𝓝 v)}

def clarkeSubdifferential (f : E → ℝ) (x : E) : Set E :=
  closedConvexHull ℝ (limitingGradients f x)

def clarkeGoldsteinSet (f : E → ℝ) (δ : ℝ) (x : E) : Set E :=
  closedConvexHull ℝ {v | ∃ y ∈ closedBall x δ, v ∈ clarkeSubdifferential f y}

def clarkeGoldsteinResidual (f : E → ℝ) (δ : ℝ) (x : E) : ℝ :=
  infDist 0 (clarkeGoldsteinSet f δ x)

theorem limitingGradients_eq_singleton {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : ContinuousAt (gradient f) x) :
    limitingGradients f x = {gradient f x} := by
  ext v
  constructor
  · rintro ⟨z, _, hz, hv⟩
    exact tendsto_nhds_unique hv (hg.tendsto.comp hz)
  · intro hv
    have he : v = gradient f x := mem_singleton_iff.mp hv
    subst v
    exact ⟨fun _ => x, fun _ => hf, tendsto_const_nhds, tendsto_const_nhds⟩

theorem clarkeSubdifferential_eq_singleton {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : ContinuousAt (gradient f) x) :
    clarkeSubdifferential f x = {gradient f x} := by
  rw [clarkeSubdifferential, limitingGradients_eq_singleton hf hg]
  rw [closedConvexHull_eq_closure_convexHull, convexHull_singleton, closure_singleton]

theorem clarkeGoldsteinSet_eq_smooth {f : E → ℝ}
    (hf : Differentiable ℝ f) (hg : Continuous (gradient f)) (δ : ℝ) (x : E) :
    clarkeGoldsteinSet f δ x = smoothGoldsteinSet (gradient f) δ x := by
  unfold clarkeGoldsteinSet smoothGoldsteinSet
  congr 1
  ext v
  simp only [clarkeSubdifferential_eq_singleton (hf _) hg.continuousAt,
    mem_setOf_eq, mem_singleton_iff, mem_image]
  constructor
  · rintro ⟨y, hy, hv⟩
    exact ⟨y, hy, hv.symm⟩
  · rintro ⟨y, hy, hv⟩
    exact ⟨y, hy, hv.symm⟩

theorem clarkeGoldsteinResidual_eq_smooth {f : E → ℝ}
    (hf : Differentiable ℝ f) (hg : Continuous (gradient f)) (δ : ℝ) (x : E) :
    clarkeGoldsteinResidual f δ x = smoothGoldsteinResidual (gradient f) δ x := by
  rw [clarkeGoldsteinResidual, smoothGoldsteinResidual, clarkeGoldsteinSet_eq_smooth hf hg]

theorem gradient_continuous_of_C1 {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv le_rfl)

theorem clarkeGoldsteinResidual_eq_of_C1 {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (δ : ℝ) (x : E) :
    clarkeGoldsteinResidual f δ x = smoothGoldsteinResidual (gradient f) δ x :=
  clarkeGoldsteinResidual_eq_smooth (hf.differentiable le_rfl) (gradient_continuous_of_C1 hf) δ x

end NCBall
