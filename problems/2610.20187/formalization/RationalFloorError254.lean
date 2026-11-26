import RationalGaussianBridge254
import CovariancePrecisionError254

noncomputable section
open scoped Matrix.Norms.Operator
namespace Paper254

theorem rationalNextCovariance_exact_floor_error {d : ℕ} (hd : 0<d) {D : ℝ}
    (W : Domain d D) (S : RationalHistoryData d) (lo hi : ℝ)
    (hlo : 0<lo) (hhi : 0<hi) (hlohi : lo≤hi) (hS : RationalHistoryInvariant W lo hi S)
    (cfg : RationalHistoryParameters) (hguard : UniformHistoryGuards d cfg lo hi)
    (lam : ℚ) (g : Fin d→ℚ) (P : PrecisionGaussian d)
    (hP : P.precision=realMatrix (rationalTiltPrecision S lam g))
    (h : ℝ) (hh : 0≤h) (hl : |(cfg.lowerThreshold:ℝ)-lo|≤h)
    (hu : |(cfg.upperThreshold:ℝ)-hi|≤h) :
    ∀ i j,|realMatrix (rationalNextCovariance cfg S lam g) i j-
      (P.floorCovariance lo hlo).precision⁻¹ i j|≤
      ((2:ℝ)^cfg.storagePrecision)⁻¹+((2:ℝ)^cfg.accuracy)⁻¹+
        (d:ℝ)^2*(cfg.smoothing:ℝ)+(d:ℝ)^2*h := by
  let U := star P.positive.isHermitian.eigenvectorUnitary
  let c := fun j=>(P.positive.isHermitian.eigenvalues j)⁻¹
  have hC : realMatrix (rationalMatrixInverse (rationalTiltPrecision S lam g))=rotatedPrecision U c := by
    rw [realMatrix_inverse,←Matrix.nonsing_inv_eq_ringInverse,←hP]
    exact P.inverse_spectral
  have hbound : ∀ x : Space d,matrixQuadratic P.precision⁻¹ x≤hi*‖x‖^2 := by
    have hb := rationalTiltCovariance_upper S hS.covariance_pos lo hi hlo hhi
      hS.covariance_lower hS.covariance_upper lam g
    rw [realMatrix_inverse,←Matrix.nonsing_inv_eq_ringInverse,←hP] at hb
    exact hb
  have hc : ∀ j,0<c j ∧ c j≤hi := fun j=>
    ⟨inv_pos.mpr (P.positive.eigenvalues_pos j),P.inverse_eigenvalue_bound hi hbound j⟩
  have he := rounded_spectralClip_original_error hd cfg.dimensionLog cfg.spectralLog cfg.accuracy
    cfg.storagePrecision hguard.dimension cfg.smoothing cfg.lowerThreshold cfg.upperThreshold
    hguard.smoothing_pos (rationalMatrixInverse (rationalTiltPrecision S lam g)) U c hC
    hguard.smoothing_lower
    (fun j=>hguard.lower_spectral (c j) (hc j).1.le (hc j).2)
    (fun j=>hguard.upper_spectral (c j) (hc j).1.le (hc j).2)
    lo hi h hguard.thresholds hlohi hh hl hu
  rw [P.floor_inverse_clip lo hi hlo hlohi hbound]
  exact he

theorem covariance_inverse_norm_bound {d : ℕ} (C : Precision d) (hC : C.PosDef)
    (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi)
    (hL : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic C x)
    (hU : ∀ x : Space d,matrixQuadratic C x≤hi*‖x‖^2) :
    ‖C⁻¹‖≤(d:ℝ)^3/lo := by
  have he := (precision_bounds_from_covariance C hC lo hi hlo hhi hL hU).2.2
  have hn := matrix_operator_norm_of_entries C⁻¹ ((d:ℝ)^2/lo) (by positivity) he
  convert hn using 1 <;> ring

theorem rationalFloor_precision_error {d : ℕ} (C R : Precision d) (hC : C.PosDef)
    (hR : R.PosDef) (lo hi e : ℝ) (hlo : 0<lo) (hhi : 0<hi) (he : 0≤e)
    (hCL : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic C x)
    (hCU : ∀ x : Space d,matrixQuadratic C x≤hi*‖x‖^2)
    (hRL : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic R x)
    (hRU : ∀ x : Space d,matrixQuadratic R x≤hi*‖x‖^2)
    (hCR : ∀ i j,|R i j-C i j|≤e) :
    ∀ i j,|R⁻¹ i j-C⁻¹ i j|≤((d:ℝ)^3/lo)^2*d*e :=
  covariance_precision_entry_error C R hC hR ((d:ℝ)^3/lo) e (by positivity) he
    (covariance_inverse_norm_bound C hC lo hi hlo hhi hCL hCU)
    (covariance_inverse_norm_bound R hR lo hi hlo hhi hRL hRU) hCR

end Paper254
#print axioms Paper254.rationalNextCovariance_exact_floor_error
#print axioms Paper254.rationalFloor_precision_error
