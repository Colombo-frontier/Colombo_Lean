import SpectralCondition254
import InverseStability254

noncomputable section
open scoped Matrix.Norms.Operator
namespace Paper254

theorem unit_inverse_difference_bound {R : Type*} [NormedRing R] (x y : Rˣ)
    (M e : ℝ) (hM : 0≤M) (he : 0≤e)
    (hx : ‖(↑x⁻¹:R)‖≤M) (hy : ‖(↑y⁻¹:R)‖≤M) (hxy : ‖(y:R)-x‖≤e) :
    ‖(↑y⁻¹:R)-(↑x⁻¹:R)‖≤M^2*e := by
  rw [unit_inverse_difference x y]
  calc
    _ ≤ ‖(↑y⁻¹:R)‖*‖(x:R)-y‖*‖(↑x⁻¹:R)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ M*e*M := by rw [norm_sub_rev]; gcongr
    _ = _ := by ring

theorem covariance_precision_entry_error {d : ℕ} (C R : Precision d)
    (hC : C.PosDef) (hR : R.PosDef) (M e : ℝ) (hM : 0≤M) (he : 0≤e)
    (hCI : ‖C⁻¹‖≤M) (hRI : ‖R⁻¹‖≤M) (hCR : ∀ i j,|R i j-C i j|≤e) :
    ∀ i j,|R⁻¹ i j-C⁻¹ i j|≤M^2*d*e := by
  let x := hC.isUnit.unit
  let y := hR.isUnit.unit
  have hx : (x:Precision d)=C := hC.isUnit.unit_spec
  have hy : (y:Precision d)=R := hR.isUnit.unit_spec
  have hxi : (↑x⁻¹:Precision d)=C⁻¹ := by
    rw [← Ring.inverse_unit x,hx,← Matrix.nonsing_inv_eq_ringInverse]
  have hyi : (↑y⁻¹:Precision d)=R⁻¹ := by
    rw [← Ring.inverse_unit y,hy,← Matrix.nonsing_inv_eq_ringInverse]
  have hh := unit_inverse_difference_bound x y M ((d:ℝ)*e) hM (by positivity)
    (by rw [hxi]; exact hCI) (by rw [hyi]; exact hRI)
    (by rw [hx,hy]; exact matrix_operator_norm_of_entries (R-C) e he hCR)
  rw [hxi,hyi] at hh
  intro i j
  have hn := (matrix_entry_le_operator_norm (R⁻¹-C⁻¹) i j).trans hh
  change |R⁻¹ i j-C⁻¹ i j|≤M^2*((d:ℝ)*e) at hn
  nlinarith

end Paper254
#print axioms Paper254.covariance_precision_entry_error
