import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Module.Basic

noncomputable section
namespace Paper254

/-- The resolvent identity requires no commutation between the two matrices. -/
theorem unit_inverse_difference {R : Type*} [Ring R] (x y : Rˣ) :
    (↑y⁻¹ : R) - ↑x⁻¹ = ↑y⁻¹ * ((x : R) - y) * ↑x⁻¹ := by
  simp only [mul_sub, sub_mul, mul_assoc, Units.mul_inv, mul_one]
  rw [← mul_assoc, Units.inv_mul, one_mul]

/-- Explicit inverse stability in a half-sized invertibility neighbourhood. -/
theorem inverse_perturbation {R : Type*} [NormedRing R] [Nontrivial R]
    [HasSummableGeomSeries R] (x : Rˣ) (y : R) (M : ℝ)
    (hM : 0 < M) (hx : ‖(↑x⁻¹ : R)‖ ≤ M)
    (hnear : ‖y-(x:R)‖ * M ≤ 1/2) :
    IsUnit y ∧ ‖Ring.inverse y‖ ≤ 2*M ∧
      ‖Ring.inverse y-(↑x⁻¹:R)‖ ≤ 2*M^2*‖y-(x:R)‖ := by
  have hxpos : 0 < ‖(↑x⁻¹:R)‖ := Units.norm_pos _
  have hn : ‖y-(x:R)‖ < ‖(↑x⁻¹:R)‖⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hxpos).mpr
    have hm := mul_le_mul_of_nonneg_left hx (norm_nonneg (y-(x:R)))
    nlinarith
  let z := x.ofNearby y hn
  have hz : (z:R)=y := rfl
  have hid := unit_inverse_difference x z
  have herr : ‖(↑z⁻¹:R)-(↑x⁻¹:R)‖ ≤ ‖(↑z⁻¹:R)‖*‖y-(x:R)‖*M := by
    rw [hid]
    calc
      _ ≤ ‖(↑z⁻¹:R)‖ * ‖(x:R)-(z:R)‖ * ‖(↑x⁻¹:R)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖(↑z⁻¹:R)‖ * ‖y-(x:R)‖ * M := by rw [hz, norm_sub_rev]; gcongr
  have htri : ‖(↑z⁻¹:R)‖ ≤ ‖(↑z⁻¹:R)-(↑x⁻¹:R)‖+M :=
    (norm_le_norm_sub_add _ _).trans (add_le_add_left hx _)
  have hzi : ‖(↑z⁻¹:R)‖ ≤ 2*M := by
    have hm := mul_le_mul_of_nonneg_left hnear (norm_nonneg (↑z⁻¹:R))
    nlinarith
  have hlast : ‖(↑z⁻¹:R)-(↑x⁻¹:R)‖ ≤ 2*M^2*‖y-(x:R)‖ := by
    calc
      _ ≤ ‖(↑z⁻¹:R)‖*‖y-(x:R)‖*M := herr
      _ ≤ (2*M)*‖y-(x:R)‖*M := by gcongr
      _ = _ := by ring
  have hzinv : Ring.inverse y=(↑z⁻¹:R) := by rw [← hz, Ring.inverse_unit]
  exact ⟨hz ▸ z.isUnit, hzinv ▸ hzi, hzinv ▸ hlast⟩

def algebraNewtonStep {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (A X : R) : R := (1/2:ℝ) • (X+Ring.inverse X*A)

/-- Perturbations need not share the eigenbasis of the exact Newton iterate. -/
theorem algebraNewtonStep_stability {R : Type*} [NormedRing R] [Nontrivial R]
    [NormedAlgebra ℝ R] [HasSummableGeomSeries R]
    (A : R) (x : Rˣ) (y : R) (M : ℝ)
    (hM : 0 < M) (hx : ‖(↑x⁻¹:R)‖ ≤ M)
    (hnear : ‖y-(x:R)‖*M ≤ 1/2) :
    IsUnit y ∧ ‖algebraNewtonStep A y-algebraNewtonStep A (x:R)‖ ≤
      (1+2*M^2*‖A‖)/2*‖y-(x:R)‖ := by
  obtain ⟨hy, _, hi⟩ := inverse_perturbation x y M hM hx hnear
  refine ⟨hy, ?_⟩
  have he : algebraNewtonStep A y-algebraNewtonStep A (x:R) =
      (1/2:ℝ) • ((y-(x:R))+(Ring.inverse y-(↑x⁻¹:R))*A) := by
    simp only [algebraNewtonStep, Ring.inverse_unit, ← smul_sub, sub_mul]
    congr 1
    abel
  rw [he, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hn := norm_add_le (y-(x:R)) ((Ring.inverse y-(↑x⁻¹:R))*A)
  have hm := (norm_mul_le (Ring.inverse y-(↑x⁻¹:R)) A).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg A))
  nlinarith

end Paper254
#print axioms Paper254.inverse_perturbation
#print axioms Paper254.algebraNewtonStep_stability
