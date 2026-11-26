import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace RandomizedFO2003.Calculus

open InnerProductSpace
open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem hasGradientAt_of_pairing {f : E → ℝ} {L : E →L[ℝ] ℝ} {g x : E}
    (hf : HasFDerivAt f L x) (hL : ∀ v, L v = inner (𝕜 := ℝ) g v) : HasGradientAt f g x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have heq : L = toDual ℝ E g := by ext v; exact hL v
  rwa [← heq]

theorem hasGradientAt_add {f g : E → ℝ} {df dg x : E}
    (hf : HasGradientAt f df x) (hg : HasGradientAt g dg x) :
    HasGradientAt (fun y => f y + g y) (df + dg) x := by
  apply hasGradientAt_of_pairing (hf.hasFDerivAt.add hg.hasFDerivAt)
  intro v
  simp only [ContinuousLinearMap.add_apply, toDual_apply, inner_add_left]

theorem hasGradientAt_sub {f g : E → ℝ} {df dg x : E}
    (hf : HasGradientAt f df x) (hg : HasGradientAt g dg x) :
    HasGradientAt (fun y => f y - g y) (df - dg) x := by
  apply hasGradientAt_of_pairing (hf.hasFDerivAt.sub hg.hasFDerivAt)
  intro v
  simp only [ContinuousLinearMap.sub_apply, toDual_apply, inner_sub_left]

theorem hasGradientAt_const_mul {f : E → ℝ} {df x : E}
    (hf : HasGradientAt f df x) (c : ℝ) :
    HasGradientAt (fun y => c * f y) (c • df) x := by
  apply hasGradientAt_of_pairing (hf.hasFDerivAt.const_mul c)
  intro v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, toDual_apply, real_inner_smul_left]

theorem hasGradientAt_mul {f g : E → ℝ} {df dg x : E}
    (hf : HasGradientAt f df x) (hg : HasGradientAt g dg x) :
    HasGradientAt (fun y => f y * g y) (f x • dg + g x • df) x := by
  apply hasGradientAt_of_pairing (hf.hasFDerivAt.mul hg.hasFDerivAt)
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    toDual_apply, inner_add_left, real_inner_smul_left]

theorem hasGradientAt_comp_linear (A : E →L[ℝ] F) {f : F → ℝ} {g : F} (x : E)
    (hf : HasGradientAt f g (A x)) : HasGradientAt (f ∘ A) (A.adjoint g) x := by
  apply hasGradientAt_of_pairing (hf.hasFDerivAt.comp x A.hasFDerivAt)
  intro v
  simp only [ContinuousLinearMap.comp_apply, toDual_apply, ContinuousLinearMap.adjoint_inner_left]

theorem hasGradientAt_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {g : ι → E} {x : E}
    (hf : ∀ i ∈ s, HasGradientAt (f i) (g i) x) :
    HasGradientAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, g i) x := by
  apply hasGradientAt_of_pairing (HasFDerivAt.sum (fun i hi => (hf i hi).hasFDerivAt))
  intro v
  simp only [ContinuousLinearMap.sum_apply, toDual_apply, sum_inner]

theorem norm_gradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := (toDual ℝ E).symm.norm_map _

end RandomizedFO2003.Calculus
