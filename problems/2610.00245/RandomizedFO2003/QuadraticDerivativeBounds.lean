import RandomizedFO2003.BlockGradient
import RandomizedFO2003.GradientDerivativeBounds

namespace RandomizedFO2003.Cascade

open RandomizedFO2003.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem quadratic_gradient_eq (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) :
    gradient (quadratic A) = A := funext (fun x => (quadratic_hasGradientAt A hA x).gradient)

theorem quadratic_second_derivative_norm (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (x : E) :
    ‖iteratedFDeriv ℝ 2 (quadratic A) x‖ = ‖A‖ := by
  rw [← norm_fderiv_gradient, quadratic_gradient_eq A hA, A.fderiv]

theorem quadratic_third_derivative_zero (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (x : E) :
    iteratedFDeriv ℝ 3 (quadratic A) x = 0 := by
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_gradient 2, quadratic_gradient_eq A hA,
    ← norm_iteratedFDeriv_fderiv (n := 1)]
  have hd : fderiv ℝ A = fun _ => A := funext (fun _ => A.fderiv)
  rw [hd, iteratedFDeriv_succ_const 0, Pi.zero_apply, norm_zero]

end RandomizedFO2003.Cascade
