import ClippingPerturbation254
import TiltCovarianceBounds254

noncomputable section
namespace Paper254

theorem inverse_min_clip (c q H : ℝ) (hc : 0<c) (hq : 0<q) (hqH : q≤H)
    (hcH : c⁻¹≤H) : (min c (1/q))⁻¹=scalarClip q H c⁻¹ := by
  rw [scalarClip_eq_max_min _ _ _ hqH,min_eq_right hcH]
  by_cases h : c≤1/q
  · rw [min_eq_left h,max_eq_right]
    have hh := (inv_le_inv₀ (by positivity : 0<1/q) hc).mpr h
    simpa only [one_div,inv_inv] using hh
  · have h' : 1/q≤c := le_of_not_ge h
    have hh := (inv_le_inv₀ hc (by positivity : 0<1/q)).mpr h'
    rw [min_eq_right h',one_div,inv_inv,max_eq_left]
    simpa only [one_div,inv_inv] using hh

theorem PrecisionGaussian.inverse_spectral {d : ℕ} (P : PrecisionGaussian d) :
    P.precision⁻¹=rotatedPrecision (star P.positive.isHermitian.eigenvectorUnitary)
      (fun j=>(P.positive.isHermitian.eigenvalues j)⁻¹) := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  calc
    _ = Ring.inverse (rotatedPrecision (star P.positive.isHermitian.eigenvectorUnitary)
      P.positive.isHermitian.eigenvalues) := congrArg Ring.inverse (precision_spectral_rotated P.positive)
    _ = _ := rotatedPrecision_inverse _ _ (fun j=>(P.positive.eigenvalues_pos j).ne')

theorem PrecisionGaussian.inverse_eigenvalue_bound {d : ℕ} (P : PrecisionGaussian d)
    (H : ℝ) (hH : ∀ x : Space d,matrixQuadratic P.precision⁻¹ x≤H*‖x‖^2) :
    ∀ j,(P.positive.isHermitian.eigenvalues j)⁻¹≤H := by
  intro j
  have hh := hH (spectralCoordinateVector (star P.positive.isHermitian.eigenvectorUnitary) j)
  rw [spectralCoordinateVector_norm,mul_one,P.inverse_spectral,spectralCoordinateVector_quadratic] at hh
  exact hh

/-- The exact Gaussian floor and the clipping target use the same spectral
representation, including repeated eigenvalues. -/
theorem PrecisionGaussian.floor_inverse_clip {d : ℕ} (P : PrecisionGaussian d)
    (q H : ℝ) (hq : 0<q) (hqH : q≤H)
    (hH : ∀ x : Space d,matrixQuadratic P.precision⁻¹ x≤H*‖x‖^2) :
    (P.floorCovariance q hq).precision⁻¹=
      rotatedPrecision (star P.positive.isHermitian.eigenvectorUnitary)
        (fun j=>scalarClip q H (P.positive.isHermitian.eigenvalues j)⁻¹) := by
  change (rotatedPrecision (star P.positive.isHermitian.eigenvectorUnitary)
    (fun j=>min (P.positive.isHermitian.eigenvalues j) (1/q)))⁻¹=_
  rw [Matrix.nonsing_inv_eq_ringInverse,rotatedPrecision_inverse _ _
    (fun j=>(lt_min (P.positive.eigenvalues_pos j) (by positivity : 0<1/q)).ne')]
  congr 1
  funext j
  exact inverse_min_clip _ q H (P.positive.eigenvalues_pos j) hq hqH
    (P.inverse_eigenvalue_bound H hH j)

theorem PrecisionGaussian.floor_covariance_interval {d : ℕ} (P : PrecisionGaussian d)
    (q H : ℝ) (hq : 0<q) (hqH : q≤H)
    (hH : ∀ x : Space d,matrixQuadratic P.precision⁻¹ x≤H*‖x‖^2) :
    ∀ x : Space d,q*‖x‖^2≤matrixQuadratic (P.floorCovariance q hq).precision⁻¹ x ∧
      matrixQuadratic (P.floorCovariance q hq).precision⁻¹ x≤H*‖x‖^2 := by
  intro x
  rw [P.floor_inverse_clip q H hq hqH hH]
  exact ⟨rotatedPrecision_lower_bound _ _ q (fun j=>(scalarClip_bounds _ _ _ hqH).1) x,
    rotatedPrecision_quadratic_bound _ _ H (fun j=>(scalarClip_bounds _ _ _ hqH).2) x⟩

end Paper254
#print axioms Paper254.PrecisionGaussian.floor_inverse_clip
