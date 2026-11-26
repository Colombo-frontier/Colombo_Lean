import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Pointwise second derivative chain rule for the Gaussian comparison
functions, expressed with the actual iterated Frechet derivative. -/

noncomputable section
namespace GradientHessian.GaussianConcentration

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem second_fderiv_comp_apply {f : F → G} {g : E → F}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x u v =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) +
      fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x u v) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have hg2 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have he : fderiv ℝ (f ∘ g) = fun y => (fderiv ℝ f (g y)).comp (fderiv ℝ g y) :=
    funext (fun y => fderiv_comp y (hfd _) (hgd _))
  have hc := ((hf2 _).hasFDerivAt.comp x (hgd x).hasFDerivAt).clm_comp (hg2 x).hasFDerivAt
  simp only [Function.comp_def] at hc
  rw [he, hc.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem second_fderiv_linear_comp_apply {f : F → G} (hf : ContDiff ℝ 2 f)
    (A : E →L[ℝ] F) (x u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (A y))) x u v =
      fderiv ℝ (fderiv ℝ f) (A x) (A u) (A v) := by
  have h := second_fderiv_comp_apply hf A.contDiff x u v
  have he : fderiv ℝ (fun y => A y) = fun _ => A := funext (fun y => A.fderiv)
  rw [he, fderiv_const] at h
  simpa only [A.fderiv, fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
    map_zero, add_zero, Function.comp_def] using h

theorem second_fderiv_linear_postcomp_apply {g : E → F} (hg : ContDiff ℝ 2 g)
    (A : F →L[ℝ] G) (x u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => A (g y))) x u v =
      A (fderiv ℝ (fderiv ℝ g) x u v) := by
  have h := second_fderiv_comp_apply A.contDiff hg x u v
  have he : fderiv ℝ (fun y => A y) = fun _ => A := funext (fun y => A.fderiv)
  rw [he, fderiv_const] at h
  simpa only [Pi.zero_apply, ContinuousLinearMap.zero_apply, zero_add, Function.comp_def] using h

end GradientHessian.GaussianConcentration
