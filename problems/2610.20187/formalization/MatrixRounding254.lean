import GaussianNorm254
import RationalNewton254

noncomputable section
open scoped Matrix BigOperators
open Matrix
namespace Paper254

/-- Coordinate errors translate to a dimension-explicit quadratic-form error. -/
theorem matrix_entry_error_quadratic {d : ℕ} (E : Precision d) (ε : ℝ)
    (hε : 0 ≤ ε) (hE : ∀ i j,|E i j| ≤ ε) (x : Space d) :
    |matrixQuadratic E x| ≤ d*ε*‖x‖^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin d => |x i|) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,sq_abs] at hcs
  have hbound : |matrixQuadratic E x| ≤ ε*(∑ i,|x i|)^2 := by
    calc
      _ = |∑ i,∑ j,x i*E i j*x j| := by
        congr 1
        simp only [matrixQuadratic,dotProduct,mulVec,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ i,|∑ j,x i*E i j*x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i,∑ j,|x i*E i j*x j| := Finset.sum_le_sum
        (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i,∑ j,|x i| * ε * |x j| := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simp only [abs_mul]
        gcongr
        exact hE i j
      _ = ε*(∑ i,|x i|)^2 := by
        simp only [← Finset.mul_sum,← Finset.sum_mul]
        ring
  have hm := mul_le_mul_of_nonneg_left hcs hε
  have hn : ‖x‖^2=∑ i,x i^2 := by simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  rw [hn]
  nlinarith

/-- An inward spectral margin survives entrywise rounding. Both endpoints
are preserved, so the covariance remains feasible after rounding. -/
theorem covariance_interval_rounding {d : ℕ} (B R : Precision d) (lo hi ε : ℝ)
    (hε : 0 ≤ ε) (hentry : ∀ i j,|R i j-B i j| ≤ ε)
    (hlo : ∀ x : Space d,(lo+d*ε)*‖x‖^2 ≤ matrixQuadratic B x)
    (hhi : ∀ x : Space d,matrixQuadratic B x ≤ (hi-d*ε)*‖x‖^2) :
    ∀ x : Space d,lo*‖x‖^2 ≤ matrixQuadratic R x ∧ matrixQuadratic R x ≤ hi*‖x‖^2 := by
  intro x
  have hh := matrix_entry_error_quadratic (R-B) ε hε hentry x
  have he : matrixQuadratic (R-B) x=matrixQuadratic R x-matrixQuadratic B x := by
    simp only [matrixQuadratic,Matrix.sub_mulVec,dotProduct_sub]
  rw [he] at hh
  have hb := abs_le.mp hh
  constructor <;> nlinarith [hlo x,hhi x]

def roundRationalMatrix {d : ℕ} (p : ℕ) (B : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℚ :=
  fun i j => dyadicCeil p (B i j)

theorem roundRationalMatrix_entry {d : ℕ} (p : ℕ) (B : Matrix (Fin d) (Fin d) ℚ)
    (i j : Fin d) : |(roundRationalMatrix p B i j:ℝ)-(B i j:ℝ)| ≤ ((2:ℝ)^p)⁻¹ := by
  have hh := dyadicCeil_real_bounds p (B i j)
  dsimp [roundRationalMatrix]
  rw [abs_of_nonneg (sub_nonneg.mpr hh.1)]
  linarith [hh.2]

theorem roundRationalMatrix_symmetric {d : ℕ} (p : ℕ) (B : Matrix (Fin d) (Fin d) ℚ)
    (hB : ∀ i j,B i j=B j i) : ∀ i j,roundRationalMatrix p B i j=roundRationalMatrix p B j i := by
  intro i j
  exact congrArg (dyadicCeil p) (hB i j)

theorem rational_covariance_interval {d : ℕ} (p : ℕ) (B : Matrix (Fin d) (Fin d) ℚ)
    (lo hi : ℝ)
    (hlo : ∀ x : Space d,(lo+d*((2:ℝ)^p)⁻¹)*‖x‖^2 ≤ matrixQuadratic (fun i j => (B i j:ℝ)) x)
    (hhi : ∀ x : Space d,matrixQuadratic (fun i j => (B i j:ℝ)) x ≤ (hi-d*((2:ℝ)^p)⁻¹)*‖x‖^2) :
    ∀ x : Space d,lo*‖x‖^2 ≤ matrixQuadratic (fun i j => (roundRationalMatrix p B i j:ℝ)) x ∧
      matrixQuadratic (fun i j => (roundRationalMatrix p B i j:ℝ)) x ≤ hi*‖x‖^2 :=
  covariance_interval_rounding _ _ lo hi (((2:ℝ)^p)⁻¹) (by positivity)
    (roundRationalMatrix_entry p B) hlo hhi

end Paper254
#print axioms Paper254.matrix_entry_error_quadratic
#print axioms Paper254.covariance_interval_rounding
#print axioms Paper254.rational_covariance_interval
