import Nonsmooth.SoftVectorHessianBounds
import Nonsmooth.C2StrongQuadraticPotential

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem softVectorPotential_quadratic_envelope {ρ : ℝ} (hρ : 0 < ρ)
    (f : ι → E → ℝ) (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hb : ∀ i x, |f i x| ≤ B i * (1 + ‖x‖ ^ 2)) :
    ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ x,
      a * ‖x‖ ^ 2 - K ≤ softVectorPotential ρ f x ∧
      softVectorPotential ρ f x ≤ K * (1 + ‖x‖ ^ 2) := by
  let A := ∑ i, (Real.log 2 + B i)
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => add_nonneg hl (hB i))
  let K := 1 + ρ + A
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨ρ / 2, K, by linarith, hK, ?_⟩
  intro x
  have hs0 : 0 ≤ ∑ i, softplus (f i x) :=
    Finset.sum_nonneg (fun i _ => Real.log_nonneg (by linarith [Real.exp_pos (f i x)]))
  have hs1 : (∑ i, softplus (f i x)) ≤ A * (1 + ‖x‖ ^ 2) := by
    dsimp only [A]
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => softplus_quadratic_envelope (f i) (hb i) x)
  dsimp only [softVectorPotential, K]
  constructor <;> nlinarith [mul_nonneg hρ.le (sq_nonneg ‖x‖), sq_nonneg ‖x‖]

/-- Finite softplus sums of explicit convex functions with quadratic
value bounds and bounded Hessians belong to the repeated-integration
class. Their gradients and all marginal assumptions are derived. -/
theorem softVectorPotential_c2StrongQuadratic {ρ : ℝ} (hρ : 0 < ρ)
    (f : ι → E → ℝ) (s : ι → E → E →L[ℝ] ℝ)
    (H : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hd : ∀ i x, HasFDerivAt (f i) (s i x) x)
    (hds : ∀ i x, HasFDerivAt (s i) (H i x) x)
    (hsym : ∀ i x v w, H i x v w = H i x w v)
    (hpos : ∀ i x v, 0 ≤ H i x v v)
    (B D : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hD : ∀ i, 0 ≤ D i)
    (hfb : ∀ i x, |f i x| ≤ B i * (1 + ‖x‖ ^ 2))
    (hHb : ∀ i x, ‖H i x‖ ≤ D i) :
    C2StrongQuadraticPotential (softVectorPotential ρ f) ρ := by
  let C := fun i => 6 * B i
  have hC (i : ι) : 0 ≤ C i := mul_nonneg (by norm_num) (hB i)
  have hs (i : ι) (x : E) : ‖s i x‖ ≤ C i * (1 + ‖x‖) :=
    convex_quadratic_gradient_bound (f i)
      (convexOn_of_nonnegative_hessian (f i) (s i) (H i) (hd i) (hds i) (hpos i))
      (hB i) (hfb i) x (s i x) (hd i x)
  refine {
    smooth := softVectorPotential_contDiff ρ f hf
    hessian_symmetric := ?_
    hessian_lower := ?_
    envelope := softVectorPotential_quadratic_envelope hρ f B hB hfb
    hessian_growth := ?_
  }
  · intro x v w
    rw [softVectorPotential_fderiv_fderiv ρ f s H hd hds]
    exact softVectorHessian_symmetric ρ f s H hsym x v w
  · intro x v
    rw [softVectorPotential_fderiv_fderiv ρ f s H hd hds]
    exact softVectorHessian_lower ρ f s H hpos x v
  · refine ⟨|ρ| * ‖realInnerBilinear (E := E)‖ + ∑ i, (D i + 2 * (C i) ^ 2), ?_, ?_⟩
    · exact add_nonneg (mul_nonneg (abs_nonneg ρ) (norm_nonneg (realInnerBilinear (E := E))))
        (Finset.sum_nonneg (fun i _ => add_nonneg (hD i) (mul_nonneg (by norm_num) (sq_nonneg (C i)))))
    · intro x
      rw [softVectorPotential_fderiv_fderiv ρ f s H hd hds]
      exact softVectorHessian_polynomial_bound ρ f s H C D hC hD hs hHb x

end
end Nonsmooth
