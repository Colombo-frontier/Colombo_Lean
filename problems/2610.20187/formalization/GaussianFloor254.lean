import GaussianSpectral254

noncomputable section
open scoped Matrix BigOperators
open Matrix
namespace Paper254

theorem precision_coordinate_cap (q c r : ℝ) (hq : 0 < q) (hc : 0 < c) :
    (q*min c (1/q)-1-Real.log (q*min c (1/q))+min c (1/q)*r^2)/2 ≤
      (q*c-1-Real.log (q*c)+c*r^2)/2 := by
  by_cases h : c ≤ 1/q
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]
    have hp := Real.log_le_sub_one_of_pos (mul_pos hq hc)
    have hm := mul_le_mul_of_nonneg_right (le_of_not_ge h) (sq_nonneg r)
    have he : q*(1/q) = 1 := by field_simp
    rw [he, Real.log_one]
    linarith

def PrecisionGaussian.floorCovariance {d : ℕ} (P : PrecisionGaussian d)
    (q : ℝ) (hq : 0 < q) : PrecisionGaussian d :=
  let U := star P.positive.isHermitian.eigenvectorUnitary
  let c := fun j => min (P.positive.isHermitian.eigenvalues j) (1/q)
  ⟨P.mean, rotatedPrecision U c,
    rotatedPrecision_posDef U c (fun j => lt_min (P.positive.eigenvalues_pos j) (by positivity))⟩

theorem precision_spectral_rotated {d : ℕ} {A : Precision d} (hA : A.PosDef) :
    A = rotatedPrecision (star hA.isHermitian.eigenvectorUnitary) hA.isHermitian.eigenvalues := by
  have he := hA.isHermitian.spectral_theorem
  simpa only [rotatedPrecision, unitary.coe_star, star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, RCLike.ofReal_real_eq_id, Function.id_comp] using he

theorem PrecisionGaussian.floor_potential_decreases {d : ℕ} (P : PrecisionGaussian d)
    (q : ℝ) (hq : 0 < q) (u : Coordinates d) :
    (P.floorCovariance q hq).potential q u ≤ P.potential q u := by
  let U := star P.positive.isHermitian.eigenvectorUnitary
  let c := P.positive.isHermitian.eigenvalues
  have hc : ∀ j, 0 < c j := P.positive.eigenvalues_pos
  have hcap : ∀ j, 0 < min (c j) (1/q) := fun j => lt_min (hc j) (by positivity)
  change (precisionCovariancePart q (rotatedPrecision U (fun j => min (c j) (1/q)))+
      matrixQuadratic (rotatedPrecision U (fun j => min (c j) (1/q))) (u-P.mean))/2 ≤
    (precisionCovariancePart q P.precision+matrixQuadratic P.precision (u-P.mean))/2
  have he : P.precision = rotatedPrecision U c := precision_spectral_rotated P.positive
  rw [he, rotatedPrecision_potential U _ _ q hq hcap,
    rotatedPrecision_potential U _ _ q hq hc]
  exact Finset.sum_le_sum (fun j _ => precision_coordinate_cap q (c j)
    (((U : Precision d) *ᵥ (u-P.mean)) j) hq (hc j))

end Paper254
#print axioms Paper254.PrecisionGaussian.floor_potential_decreases
