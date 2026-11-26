import Bilevel.MixedDerivative
import Bilevel.HypergradientFormula

/-! The zero-variation class has an actual affine lower stationarity map. -/
noncomputable section
namespace Bilevel.ZeroVariation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem affine_of_constant_derivative (f : E → F) (D : E →L[ℝ] F)
    (hf : ∀ x, HasFDerivAt f D x) (x : E) : f x = D x + f 0 := by
  have hd : ∀ z : E, HasFDerivAt (fun z => f z - D z) (0 : E →L[ℝ] F) z := by
    intro z
    simpa using (hf z).sub D.hasFDerivAt
  have h := is_const_of_fderiv_eq_zero (fun z => (hd z).differentiableAt)
    (fun z => (hd z).fderiv) x 0
  simpa only [map_zero, sub_zero, add_comm] using (eq_add_of_sub_eq h)

theorem amplified_affine_action (D : E →L[ℝ] F) (b : F) (v : E) (A : ℝ) (hA : A ≠ 0) :
    (2 * A)⁻¹ • ((D (A • v) + b) - (D ((-A) • v) + b)) = D v := by
  have he : (D (A • v) + b) - (D ((-A) • v) + b) = (2 * A) • D v := by
    simp only [map_smul]
    module
  rw [he, smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num) hA), one_smul]
end Bilevel.ZeroVariation

namespace Bilevel.Model.Primitive
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

theorem zero_variation_yy (hρ : ρ = 0) (x x' : X) (y y' : Y) :
    P.gyy x y = P.gyy x' y' := by
  have h := P.variation_yy x x' y y'
  have hz : ρ * Model.jointDistance x x' y y' = 0 := by simp [hρ]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (h.trans_eq hz))

theorem zero_variation_xy (hρ : ρ = 0) (x x' : X) (y y' : Y) :
    P.gxy x y = P.gxy x' y' := by
  have h := P.variation_xy x x' y y'
  have hz : ρ * Model.jointDistance x x' y y' = 0 := by simp [hρ]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (h.trans_eq hz))

theorem affine_lower_gradient (hρ : ρ = 0) (x : X) (y : Y) :
    P.gy x y = P.gyy 0 0 y + (P.gxy 0 0).adjoint x + P.gy 0 0 := by
  let D : (X × Y) →L[ℝ] Y := (P.gxy 0 0).adjoint.comp (ContinuousLinearMap.fst ℝ X Y) +
    (P.gyy 0 0).comp (ContinuousLinearMap.snd ℝ X Y)
  have hd : ∀ z : X × Y, HasFDerivAt (fun z : X × Y => P.gy z.1 z.2) D z := by
    intro z
    have h := P.has_joint_gy z.1 z.2
    rw [P.zero_variation_xy hρ z.1 0 z.2 0, P.zero_variation_yy hρ z.1 0 z.2 0] at h
    exact h
  have h := ZeroVariation.affine_of_constant_derivative (fun z : X × Y => P.gy z.1 z.2) D hd (x,y)
  simpa [D, add_comm, add_left_comm] using h

theorem affine_outer_gradient_in_y (hρ : ρ = 0) (x : X) (y : Y) :
    P.gx x y = P.gxy 0 0 y + P.gx x 0 := by
  apply ZeroVariation.affine_of_constant_derivative
  intro z
  have h := P.has_gxy x z
  rw [P.zero_variation_xy hρ x 0 z 0] at h
  exact h

end Bilevel.Model.Primitive
