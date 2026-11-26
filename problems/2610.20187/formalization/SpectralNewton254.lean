import RationalMatrixNewton254
import RoundedIteration254

noncomputable section
open scoped Matrix.Norms.Operator BigOperators
open Matrix
namespace Paper254

theorem unitary_entry_abs_le_one {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (i j : Fin d) : |(U:Precision d) i j|≤1 := by
  have he := congrArg (fun A : Precision d => A j j) (unitary.coe_star_mul_self U)
  have hs : ∑ k,(U:Precision d) k j^2=1 := by
    simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply_eq,
      pow_two] using he
  have ht : (U:Precision d) i j^2≤∑ k,(U:Precision d) k j^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg ((U:Precision d) k j)) (Finset.mem_univ i)
  rw [hs] at ht
  nlinarith [sq_abs ((U:Precision d) i j), abs_nonneg ((U:Precision d) i j)]

theorem rotatedPrecision_norm_bound {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (B : ℝ) (hB : 0≤B) (hc : ∀ j,|c j|≤B) :
    ‖rotatedPrecision U c‖≤(d:ℝ)^2*B := by
  have hU : ‖(U:Precision d)‖≤d := by
    simpa using matrix_operator_norm_of_entries (U:Precision d) 1 (by norm_num)
      (unitary_entry_abs_le_one U)
  have hstar : ‖(U:Precision d)ᴴ‖≤d := by
    have hh := matrix_operator_norm_of_entries ((star U:Matrix.unitaryGroup (Fin d) ℝ):Precision d)
      1 (by norm_num) (unitary_entry_abs_le_one (star U))
    simpa only [unitary.coe_star, star_eq_conjTranspose, mul_one] using hh
  have hdiag : ‖Matrix.diagonal c‖≤B := by
    rw [Matrix.linfty_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hB).mpr hc
  calc
    _ ≤ ‖(U:Precision d)ᴴ‖*‖Matrix.diagonal c‖*‖(U:Precision d)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (d:ℝ)*B*d := by gcongr
    _ = _ := by ring

theorem rotatedPrecision_sub {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (a b : Coordinates d) :
    rotatedPrecision U a-rotatedPrecision U b=rotatedPrecision U (a-b) := by
  unfold rotatedPrecision
  rw [← sub_mul, ← mul_sub, Matrix.diagonal_sub]
  rfl

theorem rotatedPrecision_mul {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (a b : Coordinates d) :
    rotatedPrecision U a*rotatedPrecision U b=rotatedPrecision U (a*b) := by
  have hu : (U:Precision d)*(U:Precision d)ᴴ=1 := unitary.coe_mul_star_self U
  calc
    _ = (U:Precision d)ᴴ*(Matrix.diagonal a*((U:Precision d)*(U:Precision d)ᴴ)*
      Matrix.diagonal b)*(U:Precision d) := by simp only [rotatedPrecision, mul_assoc]
    _ = rotatedPrecision U (a*b) := by
      rw [hu, mul_one, Matrix.diagonal_mul_diagonal]
      rfl

theorem rotatedPrecision_inverse {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hc : ∀ j,c j≠0) :
    Ring.inverse (rotatedPrecision U c)=rotatedPrecision U (c⁻¹) := by
  have hid : rotatedPrecision U (c⁻¹)*rotatedPrecision U c=1 := by
    rw [rotatedPrecision_mul]
    have he : c⁻¹*c=(fun _=>1) := by ext j; exact inv_mul_cancel₀ (hc j)
    rw [he, rotatedPrecision_one]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact Matrix.inv_eq_left_inv hid

def scalarExactNewton (a x : ℝ) : ℕ → ℝ
  | 0 => x
  | n+1 => (scalarExactNewton a x n+a/scalarExactNewton a x n)/2

theorem scalarExactNewton_bounds (a x : ℝ) (ha : 0<a) (hx : Real.sqrt a≤x) (n : ℕ) :
    Real.sqrt a≤scalarExactNewton a x n ∧
      scalarExactNewton a x n-Real.sqrt a≤(x-Real.sqrt a)*(1/2:ℝ)^n := by
  induction n with
  | zero => simp [scalarExactNewton,hx]
  | succ n ih =>
    have hs := newton_sqrt_contraction a (scalarExactNewton a x n) ha ih.1
    refine ⟨hs.1,?_⟩
    change (scalarExactNewton a x n+a/scalarExactNewton a x n)/2-Real.sqrt a≤_
    rw [pow_succ]
    linarith [hs.2,ih.2]

theorem rotatedNewton_step {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (a c : Coordinates d) (hc : ∀ j,c j≠0) :
    algebraNewtonStep (rotatedPrecision U a) (rotatedPrecision U c)=
      rotatedPrecision U (fun j=>(c j+a j/c j)/2) := by
  rw [algebraNewtonStep, rotatedPrecision_inverse U c hc, rotatedPrecision_mul]
  have hadd : rotatedPrecision U c+rotatedPrecision U (c⁻¹*a)=
      rotatedPrecision U (c+c⁻¹*a) := by
    unfold rotatedPrecision
    rw [← add_mul, ← mul_add, Matrix.diagonal_add]
    rfl
  rw [hadd]
  have he : (fun j=>(c j+a j/c j)/2)=(1/2:ℝ) • (c+c⁻¹*a) := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    ring
  rw [he]
  simp only [rotatedPrecision, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

end Paper254
#print axioms Paper254.rotatedPrecision_norm_bound
#print axioms Paper254.rotatedNewton_step
