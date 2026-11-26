import RationalHistory254
import SpectralCondition254

noncomputable section
open scoped Matrix.Norms.Operator BigOperators
open Matrix
namespace Paper254

theorem rationalMatrixInverse_symmetric {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ)
    (hC : (realMatrix C).PosDef) :
    ∀ i j,rationalMatrixInverse C i j=rationalMatrixInverse C j i := by
  intro i j
  apply Rat.cast_injective (α := ℝ)
  have hh := congrArg (fun A : Precision d=>A j i) hC.inv.isHermitian.eq
  rw [Matrix.nonsing_inv_eq_ringInverse,← realMatrix_inverse C] at hh
  simpa only [Matrix.conjTranspose_apply,star_trivial] using hh

theorem rationalMetricRound_posDef {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ)
    (hC : (realMatrix C).PosDef) (lo hi : ℝ) (hl : 0<lo) (hh : 0<hi)
    (hlo : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic (realMatrix C) x)
    (hhi : ∀ x : Space d,matrixQuadratic (realMatrix C) x≤hi*‖x‖^2)
    (p : ℕ) (hguard : (d:ℝ)*((2:ℝ)^p)⁻¹≤1/(2*hi)) :
    (realMatrix (roundRationalMatrix p (rationalMatrixInverse C))).PosDef := by
  let A := (realMatrix C)⁻¹
  let B := realMatrix (roundRationalMatrix p (rationalMatrixInverse C))
  have hprec := (precision_bounds_from_covariance (realMatrix C) hC lo hi hl hh hlo hhi).1
  have hentry : ∀ i j,|B i j-A i j|≤((2:ℝ)^p)⁻¹ := by
    intro i j
    have he := roundRationalMatrix_entry p (rationalMatrixInverse C) i j
    have hc := congrArg (fun X : Precision d=>X i j) (realMatrix_inverse C)
    rw [← Matrix.nonsing_inv_eq_ringInverse] at hc
    change (rationalMatrixInverse C i j:ℝ)=A i j at hc
    rw [hc] at he
    exact he
  apply symmetric_quadratic_lower_posDef B (1/(2*hi)) (by positivity)
  · intro i j
    exact congrArg (fun z : ℚ=>(z:ℝ))
      (roundRationalMatrix_symmetric p (rationalMatrixInverse C) (rationalMatrixInverse_symmetric C hC) i j)
  · intro x
    have he := matrix_entry_error_quadratic (B-A) (((2:ℝ)^p)⁻¹) (by positivity) hentry x
    have hid : matrixQuadratic (B-A) x=matrixQuadratic B x-matrixQuadratic A x := by
      simp only [matrixQuadratic,Matrix.sub_mulVec,dotProduct_sub]
    rw [hid] at he
    have hlow := (hprec x).1
    change (1/hi)*‖x‖^2≤matrixQuadratic A x at hlow
    have hb := (abs_le.mp he).1
    have hm := mul_le_mul_of_nonneg_right hguard (sq_nonneg ‖x‖)
    have hr : 1/hi=2*(1/(2*hi)) := by field_simp
    rw [hr] at hlow
    nlinarith

end Paper254
#print axioms Paper254.rationalMetricRound_posDef
