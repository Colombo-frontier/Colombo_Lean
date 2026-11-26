import SecondOrder.LocalHessian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

variable {Ω E F : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Differentiation of a finite law is differentiation of a finite weighted sum. -/
theorem fderiv_finiteMean (p : PMF Ω) (f : Ω → E → F) (x : E)
    (hf : ∀ z, DifferentiableAt ℝ (f z) x) :
    fderiv ℝ (fun y => ∫ z, f z y ∂p.toMeasure) x =
      ∫ z, fderiv ℝ (f z) x ∂p.toMeasure := by
  simp only [PMF.integral_eq_sum]
  rw [fderiv_sum (fun z _ => (hf z).const_smul _)]
  apply Finset.sum_congr rfl
  intro z _
  exact fderiv_const_smul (hf z) _

theorem contDiff_finiteMean (p : PMF Ω) (f : Ω → E → F) (k : WithTop ℕ∞)
    (hf : ∀ z, ContDiff ℝ k (f z)) :
    ContDiff ℝ k (fun y => ∫ z, f z y ∂p.toMeasure) := by
  simp only [PMF.integral_eq_sum]
  exact ContDiff.sum (fun z _ => (hf z).const_smul _)

theorem iteratedFDeriv_finiteMean (p : PMF Ω) (f : Ω → E → F) (k : ℕ) (x : E)
    (hf : ∀ z, ContDiff ℝ k (f z)) :
    iteratedFDeriv ℝ k (fun y => ∫ z, f z y ∂p.toMeasure) x =
      ∫ z, iteratedFDeriv ℝ k (f z) x ∂p.toMeasure := by
  simp only [PMF.integral_eq_sum]
  rw [iteratedFDeriv_sum (fun z _ => (hf z).const_smul _)]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro z _
  exact iteratedFDeriv_const_smul_apply' (hf z).contDiffAt

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem gradient_finiteMean (p : PMF Ω) (f : Ω → H → ℝ) (x : H)
    (hf : ∀ z, DifferentiableAt ℝ (f z) x) :
    gradient (fun y => ∫ z, f z y ∂p.toMeasure) x =
      ∫ z, gradient (f z) x ∂p.toMeasure := by
  unfold gradient
  rw [fderiv_finiteMean p f x hf]
  simp only [PMF.integral_eq_sum, map_sum, map_smul]

theorem fderiv_gradient_finiteMean (p : PMF Ω) (f : Ω → H → ℝ) (x : H)
    (hf : ∀ z, ContDiff ℝ 2 (f z)) :
    fderiv ℝ (gradient (fun y => ∫ z, f z y ∂p.toMeasure)) x =
      ∫ z, fderiv ℝ (gradient (f z)) x ∂p.toMeasure := by
  have he : gradient (fun y => ∫ z, f z y ∂p.toMeasure) =
      fun y => ∫ z, gradient (f z) y ∂p.toMeasure :=
    funext (fun y => gradient_finiteMean p f y
      (fun z => (hf z).differentiable (by norm_num) y))
  rw [he]
  apply fderiv_finiteMean
  intro z
  exact ((InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp
    ((hf z).fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num))).differentiable
      (by norm_num) x

end Hilbert
end
end SecondOrder
