import EfficientNewton254
import RationalSpectralClip254

open scoped Matrix.Norms.Operator
open Matrix
namespace Paper254

theorem matrix_of_cached_rows {d : ℕ} (M : Matrix (Fin d) (Fin d) ℚ) :
    rationalMatrixOfRows (rationalMatrixRows M)=M := by
  ext i j
  simp [rationalMatrixOfRows,rationalMatrixRows,Vector.get]

/-- Materialize the squared input and Newton output before forming the positive part. -/
def efficientPositivePartRows {d : ℕ} (a L s : ℕ) (ε : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) : Vector (Vector ℚ d) d :=
  let inputRows := rationalMatrixRows (rationalSqrtInput ε M)
  let rootRows := efficientNewtonRows (matrixSqrtPrecision a L s)
    (rationalMatrixOfRows inputRows) ((2:ℚ)^L • 1) (matrixSqrtIterations a L s)
  rationalMatrixRows ((1/2:ℚ) • (M+rationalSymmetrize (rationalMatrixOfRows rootRows)))

def efficientPositivePart {d : ℕ} (a L s : ℕ) (ε : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) :=
  rationalMatrixOfRows (efficientPositivePartRows a L s ε M)

theorem efficientPositivePart_eq {d : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (ε : ℚ) (hε : 0<(ε:ℝ))
    (M : Matrix (Fin d) (Fin d) ℚ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hM : realMatrix M=rotatedPrecision U c)
    (hlo : ((2:ℝ)^L)⁻¹≤(ε:ℝ)) (hhi : ∀ j,|c j|+(ε:ℝ)≤(2:ℝ)^L) :
    efficientPositivePart a L s ε M=rationalPositivePart a L s ε M := by
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
  have he := efficientCertifiedMatrixSqrt_eq hd a L s hdim (rationalSqrtInput ε M)
    U v hv (rationalSqrtInput_spectral ε M U c hM) hslo hshi
  unfold efficientPositivePart efficientPositivePartRows
  rw [matrix_of_cached_rows,matrix_of_cached_rows]
  change (1/2:ℚ) • (M+rationalSymmetrize (efficientCertifiedMatrixSqrt a L s _))=_
  rw [he]
  rfl

/-- Both shifted positive parts are stored as arrays; each is computed once. -/
def efficientSpectralClipRows {d : ℕ} (a L s : ℕ) (ε l u : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) : Vector (Vector ℚ d) d :=
  let leftInput := rationalMatrixRows (M-l • 1)
  let rightInput := rationalMatrixRows (M-u • 1)
  let left := efficientPositivePartRows a L s ε (rationalMatrixOfRows leftInput)
  let right := efficientPositivePartRows a L s ε (rationalMatrixOfRows rightInput)
  rationalMatrixRows (l • 1+rationalMatrixOfRows left-rationalMatrixOfRows right)

def efficientSpectralClip {d : ℕ} (a L s : ℕ) (ε l u : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) :=
  rationalMatrixOfRows (efficientSpectralClipRows a L s ε l u M)

theorem efficientSpectralClip_eq {d : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (ε l u : ℚ) (hε : 0<(ε:ℝ))
    (M : Matrix (Fin d) (Fin d) ℚ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hM : realMatrix M=rotatedPrecision U c)
    (hsmall : ((2:ℝ)^L)⁻¹≤(ε:ℝ))
    (hl : ∀ j,|c j-(l:ℝ)|+(ε:ℝ)≤(2:ℝ)^L)
    (hu : ∀ j,|c j-(u:ℝ)|+(ε:ℝ)≤(2:ℝ)^L) :
    efficientSpectralClip a L s ε l u M=rationalSpectralClip a L s ε l u M := by
  have hleft := efficientPositivePart_eq hd a L s hdim ε hε (M-l • 1) U
    (fun j=>c j-(l:ℝ)) (realMatrix_shift_spectral M U c hM l) hsmall hl
  have hright := efficientPositivePart_eq hd a L s hdim ε hε (M-u • 1) U
    (fun j=>c j-(u:ℝ)) (realMatrix_shift_spectral M U c hM u) hsmall hu
  unfold efficientSpectralClip efficientSpectralClipRows
  rw [matrix_of_cached_rows,matrix_of_cached_rows,matrix_of_cached_rows]
  change l • 1+efficientPositivePart a L s ε (M-l • 1)-
    efficientPositivePart a L s ε (M-u • 1)=_
  rw [hleft,hright]
  rfl

theorem efficientSpectralClip_error {d : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (ε l u : ℚ) (hε : 0<(ε:ℝ))
    (M : Matrix (Fin d) (Fin d) ℚ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hM : realMatrix M=rotatedPrecision U c)
    (hsmall : ((2:ℝ)^L)⁻¹≤(ε:ℝ))
    (hl : ∀ j,|c j-(l:ℝ)|+(ε:ℝ)≤(2:ℝ)^L)
    (hu : ∀ j,|c j-(u:ℝ)|+(ε:ℝ)≤(2:ℝ)^L) :
    ∀ i j,|realMatrix (efficientSpectralClip a L s ε l u M) i j-
      rotatedPrecision U (fun k=>scalarClip (l:ℝ) (u:ℝ) (c k)) i j|≤
      ((2:ℝ)^s)⁻¹+(d:ℝ)^2*(ε:ℝ) := by
  rw [efficientSpectralClip_eq hd a L s hdim ε l u hε M U c hM hsmall hl hu]
  exact rationalSpectralClip_error hd a L s hdim ε l u hε M U c hM hsmall hl hu

theorem efficientSpectralClip_interval {d : ℕ} (hd : 0<d) (a L s p : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (ε l u : ℚ) (hε : 0<(ε:ℝ))
    (M : Matrix (Fin d) (Fin d) ℚ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hM : realMatrix M=rotatedPrecision U c)
    (hsmall : ((2:ℝ)^L)⁻¹≤(ε:ℝ))
    (hl : ∀ j,|c j-(l:ℝ)|+(ε:ℝ)≤(2:ℝ)^L)
    (hu : ∀ j,|c j-(u:ℝ)|+(ε:ℝ)≤(2:ℝ)^L)
    (lo hi : ℝ) (hlu : (l:ℝ)≤(u:ℝ))
    (hmarginL : lo+d*(((2:ℝ)^s)⁻¹+(d:ℝ)^2*(ε:ℝ)+((2:ℝ)^p)⁻¹)≤(l:ℝ))
    (hmarginU : (u:ℝ)≤hi-d*(((2:ℝ)^s)⁻¹+(d:ℝ)^2*(ε:ℝ)+((2:ℝ)^p)⁻¹)) :
    ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic
      (realMatrix (roundRationalMatrix p (efficientSpectralClip a L s ε l u M))) x ∧
      matrixQuadratic (realMatrix (roundRationalMatrix p (efficientSpectralClip a L s ε l u M))) x≤hi*‖x‖^2 := by
  rw [efficientSpectralClip_eq hd a L s hdim ε l u hε M U c hM hsmall hl hu]
  exact rationalSpectralClip_interval hd a L s p hdim ε l u hε M U c hM hsmall hl hu
    lo hi hlu hmarginL hmarginU

end Paper254
#print axioms Paper254.efficientSpectralClip_eq
#print axioms Paper254.efficientSpectralClip_interval
