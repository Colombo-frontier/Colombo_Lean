import CertifiedMatrixSqrt254
import MatrixEntryBounds254

open scoped Matrix.Norms.Operator BigOperators
open Matrix
namespace Paper254

theorem rotatedPrecision_add {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (a b : Coordinates d) :
    rotatedPrecision U a+rotatedPrecision U b=rotatedPrecision U (a+b) := by
  unfold rotatedPrecision
  rw [← add_mul,← mul_add,Matrix.diagonal_add]
  rfl

theorem rotatedPrecision_smul {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (x : ℝ) (a : Coordinates d) : x • rotatedPrecision U a=rotatedPrecision U (x • a) := by
  simp only [rotatedPrecision,Matrix.diagonal_smul,Matrix.mul_smul,Matrix.smul_mul]

theorem rotatedPrecision_symmetric {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (a : Coordinates d) : ∀ i j,rotatedPrecision U a i j=rotatedPrecision U a j i := by
  have hh : (rotatedPrecision U a).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul U.val (Matrix.isHermitian_diagonal a)
  intro i j
  have he := congrArg (fun A : Precision d=>A j i) hh.eq
  simpa only [Matrix.conjTranspose_apply,star_trivial] using he

def rationalSqrtInput {d : ℕ} (ε : ℚ) (M : Matrix (Fin d) (Fin d) ℚ) := M*M+ε^2 • 1
def rationalPositivePart {d : ℕ} (a L s : ℕ) (ε : ℚ) (M : Matrix (Fin d) (Fin d) ℚ) :=
  (1/2:ℚ) • (M+rationalSymmetrize (certifiedMatrixSqrt a L s (rationalSqrtInput ε M)))

theorem rationalSqrtInput_spectral {d : ℕ} (ε : ℚ) (M : Matrix (Fin d) (Fin d) ℚ)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (c : Coordinates d)
    (hM : realMatrix M=rotatedPrecision U c) :
    realMatrix (rationalSqrtInput ε M)=rotatedPrecision U (fun j=>c j^2+(ε:ℝ)^2) := by
  have he : realMatrix (rationalSqrtInput ε M)=realMatrix M*realMatrix M+(ε:ℝ)^2 • 1 := by
    change (Rat.castHom ℝ).mapMatrix (M*M+ε^2 • 1)=_
    rw [map_add,map_mul]
    rw [show (Rat.castHom ℝ).mapMatrix (ε^2 • 1)=((ε^2:ℚ):ℝ) • (1:Precision d)
      from realMatrix_scalar (ε^2)]
    push_cast
    rfl
  rw [he,hM,rotatedPrecision_mul,← rotatedPrecision_const U ((ε:ℝ)^2),rotatedPrecision_add]
  congr 1
  ext j
  simp only [Pi.add_apply,Pi.mul_apply,pow_two]

theorem rationalPositivePart_error {d : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (ε : ℚ) (hε : 0<(ε:ℝ))
    (M : Matrix (Fin d) (Fin d) ℚ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hM : realMatrix M=rotatedPrecision U c)
    (hlo : ((2:ℝ)^L)⁻¹≤(ε:ℝ)) (hhi : ∀ j,|c j|+(ε:ℝ)≤(2:ℝ)^L) :
    ∀ i j,|realMatrix (rationalPositivePart a L s ε M) i j-
      rotatedPrecision U (fun k=>max (c k) 0) i j| ≤
      (((2:ℝ)^s)⁻¹+(d:ℝ)^2*(ε:ℝ))/2 := by
  let v : Coordinates d := fun j=>c j^2+(ε:ℝ)^2
  have hv : ∀ j,0<v j := by intro j; dsimp [v]; nlinarith [sq_nonneg (c j)]
  have hslo : ∀ j,((2:ℝ)^L)⁻¹≤Real.sqrt (v j) := by
    intro j
    have hh := Real.sq_sqrt (hv j).le
    have hn := Real.sqrt_nonneg (v j)
    have he : (ε:ℝ)≤Real.sqrt (v j) := by dsimp [v] at hh; nlinarith [sq_nonneg (c j)]
    exact hlo.trans he
  have hshi : ∀ j,Real.sqrt (v j)≤(2:ℝ)^L := by
    intro j
    have hh := Real.sq_sqrt (hv j).le
    have hn := Real.sqrt_nonneg (v j)
    have he : Real.sqrt (v j)≤|c j|+(ε:ℝ) := by
      dsimp [v] at hh
      nlinarith [sq_abs (c j),abs_nonneg (c j),mul_nonneg (abs_nonneg (c j)) hε.le]
    exact he.trans (hhi j)
  have hroot := certifiedMatrixSqrt_error hd a L s hdim (rationalSqrtInput ε M) U v hv
    (rationalSqrtInput_spectral ε M U c hM) hslo hshi
  have hsym := rationalSymmetrize_error (certifiedMatrixSqrt a L s (rationalSqrtInput ε M))
    (rotatedPrecision U (fun j=>Real.sqrt (v j)))
    (rotatedPrecision_symmetric U _) (((2:ℝ)^s)⁻¹) hroot
  let t : Coordinates d := fun j=>(c j+Real.sqrt (v j))/2
  let cp : Coordinates d := fun j=>max (c j) 0
  have hdiag : ∀ j,|t j-cp j|≤(ε:ℝ)/2 := by
    intro j
    have hh := smooth_positive_part_error (c j) (ε:ℝ) hε.le
    change |(c j+Real.sqrt (c j^2+(ε:ℝ)^2))/2-max (c j) 0|≤_
    rw [abs_of_nonneg (sub_nonneg.mpr hh.1)]
    linarith [hh.2]
  have hn := rotatedPrecision_norm_bound U (t-cp) ((ε:ℝ)/2) (by positivity) hdiag
  rw [← rotatedPrecision_sub] at hn
  have ht : rotatedPrecision U t=(1/2:ℝ) •
      (realMatrix M+rotatedPrecision U (fun j=>Real.sqrt (v j))) := by
    rw [hM,rotatedPrecision_add,rotatedPrecision_smul]
    congr 1
    ext j
    change (c j+Real.sqrt (v j))/2=(1/2:ℝ)*(c j+Real.sqrt (v j))
    ring
  intro i j
  have hsm := (matrix_entry_le_operator_norm (rotatedPrecision U t-rotatedPrecision U cp) i j).trans hn
  have hr := hsym i j
  rw [ht] at hsm
  change |(1/2:ℝ)*((M i j:ℝ)+rotatedPrecision U (fun j=>Real.sqrt (v j)) i j)-rotatedPrecision U cp i j|≤_ at hsm
  change |(rationalSymmetrize (certifiedMatrixSqrt a L s (rationalSqrtInput ε M)) i j:ℝ)-
    rotatedPrecision U (fun j=>Real.sqrt (v j)) i j|≤_ at hr
  change |(((1/2:ℚ)*(M i j+rationalSymmetrize (certifiedMatrixSqrt a L s (rationalSqrtInput ε M)) i j):ℚ):ℝ)-
    rotatedPrecision U cp i j|≤_
  push_cast
  obtain ⟨hr0,hr1⟩ := abs_le.mp hr
  obtain ⟨hs0,hs1⟩ := abs_le.mp hsm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end Paper254
#print axioms Paper254.rationalPositivePart_error
