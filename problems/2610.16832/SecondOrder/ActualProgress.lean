import SecondOrder.Progress
import SecondOrder.ContinuousChord
import SecondOrder.SignOrthogonality
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- Algebraically equivalent to the manuscript's 8^(-1/ν) (γ/L)^(1/ν). -/
def curvatureRadius (L ν γ : ℝ) : ℝ := (γ/(8*L))^(1/ν)

theorem curvatureRadius_pos {L ν γ : ℝ} (hL : 0 < L) (hγ : 0 < γ) :
    0 < curvatureRadius L ν γ := Real.rpow_pos_of_pos (by positivity) _

theorem curvatureRadius_scale {L ν γ : ℝ} (hL : 0 < L) (hν : 0 < ν) (hγ : 0 < γ) :
    L*(curvatureRadius L ν γ)^ν = γ/8 := by
  have hb : 0 ≤ γ/(8*L) := by positivity
  rw [curvatureRadius, ← Real.rpow_mul hb, one_div_mul_cancel hν.ne', Real.rpow_one]
  field_simp
  ring

theorem curvatureRadius_original {L ν γ : ℝ} (hL : 0 < L) (hγ : 0 < γ) :
    curvatureRadius L ν γ = (8 : ℝ)^(-(1/ν))*(γ/L)^(1/ν) := by
  unfold curvatureRadius
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 8), ← Real.inv_rpow (by norm_num : (0:ℝ) ≤ 8),
    ← Real.mul_rpow (by positivity : 0 ≤ (8:ℝ)⁻¹) (by positivity : 0 ≤ γ/L)]
  congr 1
  field_simp

def gradientNext {d : ℕ} (L : ℝ) (x g : Point d) : Point d := x+(-1/(4*L))•g

def curvatureNext {d : ℕ} (s : ℝ) (x u : Point d) (b : Bool) : Point d :=
  x+(signValue b*s)•u

theorem curvatureNext_displacement {d : ℕ} (s : ℝ) (x u : Point d) (hu : ‖u‖ = 1) (b : Bool) :
    ‖curvatureNext s x u b-x‖^2 = s^2 := by
  cases b <;> simp [curvatureNext, signValue, norm_smul, hu, Real.norm_eq_abs, sq_abs]

theorem curvatureNext_mean {d : ℕ} (F : Point d → ℝ) (s : ℝ) (x u : Point d) :
    (∫ b, F (curvatureNext s x u b) ∂(PMF.uniformOfFintype Bool).toMeasure) =
      (F (x+s•u)+F (x+(-s)•u))/2 := by
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, curvatureNext, signValue, Fintype.sum_bool, add_comm, div_eq_mul_inv]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.population_derivative (h : CommonLoss μ P ν F f) (x : Point d) :
    HasFDerivAt F (innerSL ℝ (gradient F x)) x :=
  ((h.population_smooth.differentiable (by norm_num)) x).hasGradientAt.hasFDerivAt

theorem CommonLoss.gradientNext_progress (h : CommonLoss μ P ν F f) (x g : Point d)
    {τ : ℝ} (hτ : 0 ≤ τ) (he : ‖g-gradient F x‖ ≤ τ) (hg : 4*τ ≤ ‖g‖) :
    τ^2/P.gradientLip ≤ F x-F (gradientNext P.gradientLip x g) ∧
      P.gradientLip*‖gradientNext P.gradientLip x g-x‖^2 ≤ F x-F (gradientNext P.gradientLip x g) := by
  have hh := gradient_move_progress P.gradientLip_pos hτ h.population_derivative
    h.gradient_lipschitz x g he hg
  simpa only [gradientNext, add_sub_cancel_left] using hh

/-- The exact radius from the algorithm satisfies the one-step expected
curvature progress estimate under the original oracle model. -/
theorem CommonLoss.curvatureNext_progress (h : CommonLoss μ P ν F f) (x u : Point d)
    {γ : ℝ} (hγ : 0 < γ) (hu : ‖u‖ = 1) (hc : ⟪hessian F x u,u⟫_ℝ ≤ -γ/2) :
    3*γ*(curvatureRadius P.hessianHolder ν γ)^2/16 ≤ F x-
      ∫ b, F (curvatureNext (curvatureRadius P.hessianHolder ν γ) x u b)
        ∂(PMF.uniformOfFintype Bool).toMeasure := by
  rw [curvatureNext_mean]
  exact signed_curvature_progress h.nu_pos P.hessianHolder_pos.le
    (curvatureRadius_pos P.hessianHolder_pos hγ).le h.population_derivative
    (gradient_has_hessian h.population_smooth) h.hessian_holder x u hu hc
    (curvatureRadius_scale P.hessianHolder_pos h.nu_pos hγ).le

end
end SecondOrder
