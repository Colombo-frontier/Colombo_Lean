import RandomizedFO2003.GradientCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue

namespace RandomizedFO2003.Calculus

open InnerProductSpace

theorem norm_fderiv_eq_iterated_one {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (x : X) :
    ‖fderiv ℝ f x‖ = ‖iteratedFDeriv ℝ 1 f x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Riesz duality preserves the operator norms of all derivative tensors. -/
theorem norm_iteratedFDeriv_gradient (n : ℕ) (f : E → ℝ) (x : E) :
    ‖iteratedFDeriv ℝ n (gradient f) x‖ = ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  change ‖iteratedFDeriv ℝ n ((toDual ℝ E).symm ∘ fderiv ℝ f) x‖ = _
  rw [(toDual ℝ E).symm.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

theorem gradient_contDiff (n : ℕ) {f : E → ℝ} (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ n (gradient f) :=
  (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp (hf.fderiv_right (by simp))

theorem norm_fderiv_gradient (f : E → ℝ) (x : E) :
    ‖fderiv ℝ (gradient f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [norm_fderiv_eq_iterated_one, norm_iteratedFDeriv_gradient]

theorem norm_fderiv_hessian (f : E → ℝ) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ = ‖iteratedFDeriv ℝ 3 f x‖ := by
  rw [norm_fderiv_eq_iterated_one, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_gradient]

/-- Converts a global second derivative bound into the exact gradient
Lipschitz inequality used in the target function class. -/
theorem gradient_lipschitz_of_second_bound {f : E → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hb : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ M) (x y : E) :
    ‖gradient f x - gradient f y‖ ≤ M * ‖x - y‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_hz : z ∈ (Set.univ : Set E)) => (gradient_contDiff 1 hf).differentiable (by norm_num) z)
    (fun z _ => by rw [norm_fderiv_gradient]; exact hb z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)

/-- Converts the global third derivative bound into the actual Hessian
Lipschitz inequality, without changing the ambient Hilbert norm. -/
theorem hessian_lipschitz_of_third_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f) {M : ℝ}
    (hb : ∀ z, ‖iteratedFDeriv ℝ 3 f z‖ ≤ M) (x y : E) :
    ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖ := by
  have hg : ContDiff ℝ 2 (gradient f) := gradient_contDiff 2 hf
  have hH : ContDiff ℝ 1 (fderiv ℝ (gradient f)) := hg.fderiv_right (by norm_num)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_hz : z ∈ (Set.univ : Set E)) => hH.differentiable (by norm_num) z)
    (fun z _ => by rw [norm_fderiv_hessian]; exact hb z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)

end RandomizedFO2003.Calculus
