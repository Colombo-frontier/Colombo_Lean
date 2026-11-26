import SecondOrder.Calculus
import SecondOrder.FiniteMean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace SecondOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Population identity underlying the fresh random-line estimator. -/
theorem hessian_line_integral {G : E → E} {H : E → E →L[ℝ] E}
    (hG : ∀ x, HasFDerivAt G (H x) x) (hH : Continuous H) (x y : E) :
    (∫ t in (0:ℝ)..1, H (x+t•(y-x)) (y-x)) = G y-G x := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => G (x+t•(y-x)))
      (H (x+t•(y-x)) (y-x)) t := by
    simpa only [id_eq, one_smul] using
      (hG _).comp_hasDerivAt t (((hasDerivAt_id t).smul_const (y-x)).const_add x)
  have hc : Continuous (fun t : ℝ => H (x+t•(y-x)) (y-x)) := by
    exact (hH.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  simpa using h

/-- Compatibility at the level of actual sample derivatives. Probability and
the squared-norm integral inequality are separate from this exact identity. -/
theorem centered_gradient_line_integral {G g : E → E} {H h : E → E →L[ℝ] E}
    (hG : ∀ x, HasFDerivAt G (H x) x) (hg : ∀ x, HasFDerivAt g (h x) x)
    (hH : Continuous H) (hh : Continuous h) (x y : E) :
    (∫ t in (0:ℝ)..1, (h (x+t•(y-x))-H (x+t•(y-x))) (y-x)) =
      (g y-G y)-(g x-G x) := by
  have hd (x : E) : HasFDerivAt (fun z => g z-G z) (h x-H x) x := (hg x).sub (hG x)
  exact hessian_line_integral hd (hh.sub hH) x y

/-- Conditional variance decomposition for finite line-point and sample laws.
The bound uses the Hessian norm, not a Hölder quadrature error. -/
theorem finite_random_line_variance {U Z : Type*} [Fintype U] [Fintype Z]
    (p : PMF U) (q : PMF Z) (Y : U → Z → E) (A : U → E) {σ L r : ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hmean : ∀ u, pmfMean q (Y u) = A u)
    (hnoise : ∀ u, pmfMean q (fun z => ‖Y u z-A u‖^2) ≤ σ^2*r^2)
    (hbound : ∀ u, ‖A u‖ ≤ L*r) :
    pmfMean p (fun u => pmfMean q (fun z => ‖Y u z-pmfMean p A‖^2)) ≤
      (σ^2+L^2)*r^2 := by
  have hconditional (u : U) :
      pmfMean q (fun z => ‖Y u z-pmfMean p A‖^2) =
        ‖A u-pmfMean p A‖^2+pmfMean q (fun z => ‖Y u z-A u‖^2) := by
    have he (z : Z) : Y u z-pmfMean p A = (A u-pmfMean p A)+(Y u z-A u) := by abel
    simp only [he, pmfMean_norm_add_sq, pmfMean_sub, hmean, pmfMean_const,
      sub_self, inner_zero_right, mul_zero, add_zero]
  simp only [hconditional, pmfMean_add]
  have hv := pmfMean_variance_le p A
  have hb : pmfMean p (fun u => ‖A u‖^2) ≤ (L*r)^2 :=
    pmfMean_le_const p _ (fun u => pow_le_pow_left₀ (norm_nonneg _) (hbound u) 2)
  have hn := pmfMean_le_const p _ hnoise
  nlinarith

end SecondOrder
