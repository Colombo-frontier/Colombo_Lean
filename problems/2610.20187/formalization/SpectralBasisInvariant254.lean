import ExactRealArithmetic254

noncomputable section
open scoped Matrix
open Matrix
namespace Paper254

theorem real_unitary_mul_conjTranspose {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) :
    (U : Precision d)*(U : Precision d)ᴴ=1 := by
  rw [←star_eq_conjTranspose,←unitary.coe_star,unitary.coe_mul_star_self]

theorem real_unitary_conjTranspose_mul {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) :
    (U : Precision d)ᴴ*(U : Precision d)=1 := by
  rw [←star_eq_conjTranspose,unitary.coe_star_mul_self]

theorem unitary_rotated_left {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) (c : Coordinates d) :
    (U : Precision d)*rotatedPrecision U c=Matrix.diagonal c*(U : Precision d) := by
  calc
    _=((U : Precision d)*(U : Precision d)ᴴ)*Matrix.diagonal c*(U : Precision d) := by
      simp only [rotatedPrecision]; noncomm_ring
    _=_ := by rw [real_unitary_mul_conjTranspose,Matrix.one_mul]

theorem unitary_rotated_right {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) (c : Coordinates d) :
    rotatedPrecision U c*(U : Precision d)ᴴ=(U : Precision d)ᴴ*Matrix.diagonal c := by
  calc
    _=(U : Precision d)ᴴ*Matrix.diagonal c*((U : Precision d)*(U : Precision d)ᴴ) := by
      simp only [rotatedPrecision]; noncomm_ring
    _=_ := by rw [real_unitary_mul_conjTranspose,Matrix.mul_one]

/-- Applying any scalar function to a diagonalized real symmetric matrix
is independent of the chosen orthonormal eigenbasis, including repeated
eigenvalues. No regularity assumption on the scalar function is needed. -/
theorem rotatedPrecision_map_eq {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℝ)
    (c e : Coordinates d) (h : rotatedPrecision U c=rotatedPrecision V e) (f : ℝ→ℝ) :
    rotatedPrecision U (fun j=>f (c j))=rotatedPrecision V (fun j=>f (e j)) := by
  let B := (U : Precision d)*(V : Precision d)ᴴ
  have hd : Matrix.diagonal c*B=B*Matrix.diagonal e := by
    calc
      _=((U : Precision d)*rotatedPrecision U c)*(V : Precision d)ᴴ := by
        rw [unitary_rotated_left]; dsimp [B]; rw [Matrix.mul_assoc]
      _=(U : Precision d)*(rotatedPrecision V e*(V : Precision d)ᴴ) := by
        rw [h,Matrix.mul_assoc]
      _=_ := by rw [unitary_rotated_right,←Matrix.mul_assoc]
  have hf : Matrix.diagonal (fun j=>f (c j))*B=B*Matrix.diagonal (fun j=>f (e j)) := by
    ext i j
    have hij := congrArg (fun M : Precision d=>M i j) hd
    simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at hij ⊢
    by_cases he : c i=e j
    · rw [he,mul_comm]
    · have hz : B i j=0 := by
        have hm : (c i-e j)*B i j=0 := by nlinarith [hij]
        exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr he)
      simp [hz]
  have hh := congrArg (fun M : Precision d=>(U : Precision d)ᴴ*M*(V : Precision d)) hf
  have hleft : (U : Precision d)ᴴ*(Matrix.diagonal (fun j=>f (c j))*B)*(V : Precision d)=
      rotatedPrecision U (fun j=>f (c j)) := by
    calc
      _=rotatedPrecision U (fun j=>f (c j))*((V : Precision d)ᴴ*(V : Precision d)) := by
        dsimp [B,rotatedPrecision]; noncomm_ring
      _=_ := by rw [real_unitary_conjTranspose_mul,Matrix.mul_one]
  have hright : (U : Precision d)ᴴ*(B*Matrix.diagonal (fun j=>f (e j)))*(V : Precision d)=
      rotatedPrecision V (fun j=>f (e j)) := by
    calc
      _=((U : Precision d)ᴴ*(U : Precision d))*rotatedPrecision V (fun j=>f (e j)) := by
        dsimp [B,rotatedPrecision]; noncomm_ring
      _=_ := by rw [real_unitary_conjTranspose_mul,Matrix.one_mul]
  dsimp only at hh
  rwa [hleft,hright] at hh

theorem spectral_cap_independent {d : ℕ} (A : Precision d) (hA : A.PosDef)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (c : Coordinates d)
    (h : A=rotatedPrecision U c) (q : ℝ) :
    rotatedPrecision U (fun j=>min (c j) (1/q))=
      rotatedPrecision (star hA.isHermitian.eigenvectorUnitary)
        (fun j=>min (hA.isHermitian.eigenvalues j) (1/q)) := by
  apply rotatedPrecision_map_eq U (star hA.isHermitian.eigenvectorUnitary)
    c hA.isHermitian.eigenvalues _ (fun x=>min x (1/q))
  rw [←h,←precision_spectral_rotated hA]

end Paper254
#print axioms Paper254.rotatedPrecision_map_eq
#print axioms Paper254.spectral_cap_independent
