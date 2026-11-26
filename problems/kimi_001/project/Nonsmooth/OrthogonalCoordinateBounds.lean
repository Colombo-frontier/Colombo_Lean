import Nonsmooth.LinearCoordinateCalculus
import Nonsmooth.FirstOrder

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem orthogonal_coordinate_norm_sq (L : F →ₗᵢ[ℝ] E) (u : E) (hu : ‖u‖ = 1)
    (ho : ∀ t, inner ℝ (L t) u = (0 : ℝ)) (t : F) (x : ℝ) :
    ‖coordinatePoint L.toContinuousLinearMap u t x‖ ^ 2 = ‖t‖ ^ 2 + x ^ 2 := by
  change ‖L t + x • u‖ ^ 2 = _
  rw [norm_add_sq_real, L.norm_map, norm_smul, hu, mul_one, Real.norm_eq_abs,
    sq_abs, inner_smul_right, ho, mul_zero]
  ring

theorem orthogonal_coordinate_norm_le (L : F →ₗᵢ[ℝ] E) (u : E) (hu : ‖u‖ = 1)
    (t : F) (x : ℝ) :
    ‖coordinatePoint L.toContinuousLinearMap u t x‖ ≤ ‖t‖ + |x| := by
  have h := norm_add_le (L t) (x • u)
  simpa only [coordinatePoint, LinearIsometry.coe_toContinuousLinearMap,
    L.norm_map, norm_smul, hu, mul_one, Real.norm_eq_abs] using h

theorem coordinatePrecompose_norm_le_one (L : F →L[ℝ] E) (hL : ‖L‖ ≤ 1) :
    ‖coordinatePrecompose L‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖A.comp L‖ ≤ 1 * ‖A‖
  have h := ContinuousLinearMap.opNorm_comp_le A L
  nlinarith [mul_le_mul_of_nonneg_left hL (norm_nonneg A)]

theorem coordinateScore_norm_le (S : E → E →L[ℝ] ℝ)
    (L : F →L[ℝ] E) (hL : ‖L‖ ≤ 1) (u : E) (t : F) (x : ℝ) :
    ‖coordinateScore S L u t x‖ ≤ ‖S (coordinatePoint L u t x)‖ := by
  have h := (coordinatePrecompose L).le_opNorm (S (coordinatePoint L u t x))
  have hm := mul_le_mul_of_nonneg_right (coordinatePrecompose_norm_le_one L hL)
    (norm_nonneg (S (coordinatePoint L u t x)))
  change ‖coordinatePrecompose L (S (coordinatePoint L u t x))‖ ≤ _
  exact h.trans (by simpa only [one_mul] using hm)

theorem coordinateHessian_norm_le (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (L : F →L[ℝ] E) (hL : ‖L‖ ≤ 1) (u : E) (t : F) (x : ℝ) :
    ‖coordinateHessian H L u t x‖ ≤ ‖H (coordinatePoint L u t x)‖ := by
  let A := (coordinatePrecompose L).comp (H (coordinatePoint L u t x))
  have h1 : ‖A‖ ≤ ‖H (coordinatePoint L u t x)‖ := by
    have h := ContinuousLinearMap.opNorm_comp_le (coordinatePrecompose L) (H (coordinatePoint L u t x))
    have hm := mul_le_mul_of_nonneg_right (coordinatePrecompose_norm_le_one L hL)
      (norm_nonneg (H (coordinatePoint L u t x)))
    change ‖A‖ ≤ _
    nlinarith
  have h2 := ContinuousLinearMap.opNorm_comp_le A L
  have hm := mul_le_mul_of_nonneg_left hL (norm_nonneg A)
  change ‖A.comp L‖ ≤ _
  nlinarith

theorem orthogonal_coordinate_global_bounds (U : E → ℝ) (S : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (L : F →ₗᵢ[ℝ] E) (u : E) (hu : ‖u‖ = 1)
    (ho : ∀ t, inner ℝ (L t) u = (0 : ℝ)) {a B C D : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hU : ∀ z, a * ‖z‖ ^ 2 - B ≤ U z)
    (hS : ∀ z, ‖S z‖ ≤ C * (1 + ‖z‖))
    (hH : ∀ z, ‖H z‖ ≤ D * (1 + ‖z‖ ^ 2)) (t : F) (x : ℝ) :
    a * x ^ 2 - B ≤ coordinatePotential U L.toContinuousLinearMap u t x ∧
    ‖coordinateScore S L.toContinuousLinearMap u t x‖ ≤ C * (1 + ‖t‖ + |x|) ∧
    ‖coordinateHessian H L.toContinuousLinearMap u t x‖ ≤ D * (1 + ‖t‖ ^ 2 + |x| ^ 2) := by
  have hz := orthogonal_coordinate_norm_sq L u hu ho t x
  refine ⟨?_, ?_, ?_⟩
  · have hb := hU (coordinatePoint L.toContinuousLinearMap u t x)
    rw [hz] at hb
    change _ ≤ U (coordinatePoint L.toContinuousLinearMap u t x)
    nlinarith [mul_nonneg ha (sq_nonneg ‖t‖)]
  · apply (coordinateScore_norm_le S _ L.norm_toContinuousLinearMap_le u t x).trans
    apply (hS _).trans
    have hm := mul_le_mul_of_nonneg_left (orthogonal_coordinate_norm_le L u hu t x) hC
    nlinarith
  · apply (coordinateHessian_norm_le H _ L.norm_toContinuousLinearMap_le u t x).trans
    simpa only [hz, sq_abs, add_assoc] using hH (coordinatePoint L.toContinuousLinearMap u t x)

def orthogonalCoordinateRegularFamily (U : E → ℝ) (S : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hcU : Continuous U) (hcS : Continuous S) (hcH : Continuous H)
    (hdU : ∀ z, HasFDerivAt U (S z) z) (hdS : ∀ z, HasFDerivAt S (H z) z)
    (L : F →ₗᵢ[ℝ] E) (u : E) (hu : ‖u‖ = 1)
    (ho : ∀ t, inner ℝ (L t) u = (0 : ℝ)) {a B C D : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hU : ∀ z, a * ‖z‖ ^ 2 - B ≤ U z)
    (hS : ∀ z, ‖S z‖ ≤ C * (1 + ‖z‖))
    (hH : ∀ z, ‖H z‖ ≤ D * (1 + ‖z‖ ^ 2)) :
    RegularVectorCoordinateFamily (coordinatePotential U L.toContinuousLinearMap u) := by
  have hc := coordinate_data_continuous U S H hcU hcS hcH L.toContinuousLinearMap u
  have hb := orthogonal_coordinate_global_bounds U S H L u hu ho ha.le hC hU hS hH
  exact regularVectorCoordinateFamilyOfGrowth _ _ _ hc.1 hc.2.1 hc.2.2
    (coordinatePotential_hasFDerivAt U S hdU L.toContinuousLinearMap u)
    (coordinateScore_hasFDerivAt S H hdS L.toContinuousLinearMap u) ha hC hD
    (fun t x => (hb t x).1) (fun t x => (hb t x).2.1) (fun t x => (hb t x).2.2)

end
end Nonsmooth
