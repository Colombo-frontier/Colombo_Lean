import RationalPositivePart254

open scoped Matrix.Norms.Operator BigOperators
open Matrix
namespace Paper254

def scalarClip (l u x : ℝ) := l+max (x-l) 0-max (x-u) 0

theorem scalarClip_bounds (l u x : ℝ) (hlu : l≤u) :
    l≤scalarClip l u x ∧ scalarClip l u x≤u := by
  unfold scalarClip
  by_cases hl : x≤l
  · rw [max_eq_right (by linarith),max_eq_right (by linarith)]
    constructor <;> linarith
  · by_cases hu : x≤u
    · rw [max_eq_left (by linarith),max_eq_right (by linarith)]
      constructor <;> linarith
    · rw [max_eq_left (by linarith),max_eq_left (by linarith)]
      constructor <;> linarith

def rationalSpectralClip {d : ℕ} (a L s : ℕ) (ε l u : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) :=
  l • 1+rationalPositivePart a L s ε (M-l • 1)-rationalPositivePart a L s ε (M-u • 1)

theorem realMatrix_shift_spectral {d : ℕ} (M : Matrix (Fin d) (Fin d) ℚ)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (c : Coordinates d)
    (hM : realMatrix M=rotatedPrecision U c) (l : ℚ) :
    realMatrix (M-l • 1)=rotatedPrecision U (fun j=>c j-(l:ℝ)) := by
  change (Rat.castHom ℝ).mapMatrix (M-l • 1)=_
  rw [map_sub]
  change realMatrix M-realMatrix (l • 1)=_
  rw [realMatrix_scalar,hM,← rotatedPrecision_const U (l:ℝ),rotatedPrecision_sub]
  rfl

theorem rationalSpectralClip_error {d : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (ε l u : ℚ) (hε : 0<(ε:ℝ))
    (M : Matrix (Fin d) (Fin d) ℚ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (hM : realMatrix M=rotatedPrecision U c)
    (hsmall : ((2:ℝ)^L)⁻¹≤(ε:ℝ))
    (hl : ∀ j,|c j-(l:ℝ)|+(ε:ℝ)≤(2:ℝ)^L)
    (hu : ∀ j,|c j-(u:ℝ)|+(ε:ℝ)≤(2:ℝ)^L) :
    ∀ i j,|realMatrix (rationalSpectralClip a L s ε l u M) i j-
      rotatedPrecision U (fun k=>scalarClip (l:ℝ) (u:ℝ) (c k)) i j|≤
      ((2:ℝ)^s)⁻¹+(d:ℝ)^2*(ε:ℝ) := by
  have hleft := rationalPositivePart_error hd a L s hdim ε hε (M-l • 1) U
    (fun j=>c j-(l:ℝ)) (realMatrix_shift_spectral M U c hM l) hsmall hl
  have hright := rationalPositivePart_error hd a L s hdim ε hε (M-u • 1) U
    (fun j=>c j-(u:ℝ)) (realMatrix_shift_spectral M U c hM u) hsmall hu
  have he : rotatedPrecision U (fun k=>scalarClip (l:ℝ) (u:ℝ) (c k))=
      (l:ℝ) • 1+rotatedPrecision U (fun k=>max (c k-(l:ℝ)) 0)-
      rotatedPrecision U (fun k=>max (c k-(u:ℝ)) 0) := by
    rw [← rotatedPrecision_const U (l:ℝ),rotatedPrecision_add,rotatedPrecision_sub]
    rfl
  have hr : realMatrix (rationalSpectralClip a L s ε l u M)=
      (l:ℝ) • 1+realMatrix (rationalPositivePart a L s ε (M-l • 1))-
      realMatrix (rationalPositivePart a L s ε (M-u • 1)) := by
    change (Rat.castHom ℝ).mapMatrix (l • 1+_-_)=_
    rw [map_sub,map_add]
    rw [show (Rat.castHom ℝ).mapMatrix (l • 1)=(l:ℝ) • (1:Precision d) from realMatrix_scalar l]
    rfl
  intro i j
  rw [hr,he]
  have ha := abs_le.mp (hleft i j)
  have hb := abs_le.mp (hright i j)
  change |((l:ℝ) • (1:Precision d)) i j+_-_-(((l:ℝ) • (1:Precision d)) i j+_-_)|≤_
  exact abs_le.mpr ⟨by linarith [ha.1,ha.2,hb.1,hb.2],by linarith [ha.1,ha.2,hb.1,hb.2]⟩

theorem rotatedPrecision_lower_bound {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ)
    (c : Coordinates d) (l : ℝ) (hc : ∀ j,l≤c j) (x : Space d) :
    l*‖x‖^2≤matrixQuadratic (rotatedPrecision U c) x := by
  rw [rotatedPrecision_quadratic]
  calc
    _ = ∑ j,l*((U:Precision d)*ᵥ (x:Coordinates d)) j^2 := by
      rw [← Finset.mul_sum,unitary_sum_squares]
      simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
    _ ≤ _ := Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right (hc j) (sq_nonneg _))

/-- The stored rational covariance satisfies both spectral constraints.
The thresholds are moved inward before smoothing and rounding. -/
theorem rationalSpectralClip_interval {d : ℕ} (hd : 0<d) (a L s p : ℕ)
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
      (realMatrix (roundRationalMatrix p (rationalSpectralClip a L s ε l u M))) x ∧
      matrixQuadratic (realMatrix (roundRationalMatrix p (rationalSpectralClip a L s ε l u M))) x≤hi*‖x‖^2 := by
  let B := rotatedPrecision U (fun j=>scalarClip (l:ℝ) (u:ℝ) (c j))
  let E := ((2:ℝ)^s)⁻¹+(d:ℝ)^2*(ε:ℝ)+((2:ℝ)^p)⁻¹
  apply covariance_interval_rounding B _ lo hi E (by dsimp [E]; positivity)
  · intro i j
    have he := rationalSpectralClip_error hd a L s hdim ε l u hε M U c hM hsmall hl hu i j
    change |(rationalSpectralClip a L s ε l u M i j:ℝ)-B i j|≤_ at he
    have hr := roundRationalMatrix_entry p (rationalSpectralClip a L s ε l u M) i j
    have ht := abs_add_le ((roundRationalMatrix p (rationalSpectralClip a L s ε l u M) i j:ℝ)-
      (rationalSpectralClip a L s ε l u M i j:ℝ))
      ((rationalSpectralClip a L s ε l u M i j:ℝ)-B i j)
    change |(roundRationalMatrix p (rationalSpectralClip a L s ε l u M) i j:ℝ)-B i j|≤_
    dsimp [E]
    rw [sub_add_sub_cancel] at ht
    exact ht.trans (by linarith)
  · intro x
    exact (mul_le_mul_of_nonneg_right hmarginL (sq_nonneg _)).trans
      (rotatedPrecision_lower_bound U _ (l:ℝ) (fun j=>(scalarClip_bounds _ _ _ hlu).1) x)
  · intro x
    exact (rotatedPrecision_quadratic_bound U _ (u:ℝ) (fun j=>(scalarClip_bounds _ _ _ hlu).2) x).trans
      (mul_le_mul_of_nonneg_right hmarginU (sq_nonneg _))

theorem rationalPositivePart_symmetric {d : ℕ} (a L s : ℕ) (ε : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) (hM : ∀ i j,M i j=M j i) :
    ∀ i j,rationalPositivePart a L s ε M i j=rationalPositivePart a L s ε M j i := by
  intro i j
  change (1/2:ℚ)*(M i j+_)=(1/2:ℚ)*(M j i+_)
  rw [hM i j,rationalSymmetrize_symmetric]

theorem rationalSpectralClip_symmetric {d : ℕ} (a L s p : ℕ) (ε l u : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) (hM : ∀ i j,M i j=M j i) :
    ∀ i j,roundRationalMatrix p (rationalSpectralClip a L s ε l u M) i j=
      roundRationalMatrix p (rationalSpectralClip a L s ε l u M) j i := by
  apply roundRationalMatrix_symmetric
  have hshift : ∀ z : ℚ,∀ i j,(M-z • 1) i j=(M-z • 1) j i := by
    intro z i j
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    rw [hM i j,Matrix.one_apply,Matrix.one_apply]
    by_cases hij : i=j <;> simp [hij,Ne.symm]
  intro i j
  change (l • (1:Matrix (Fin d) (Fin d) ℚ)) i j+_-_=(l • (1:Matrix (Fin d) (Fin d) ℚ)) j i+_-_
  rw [rationalPositivePart_symmetric a L s ε (M-l • 1) (hshift l) i j,
    rationalPositivePart_symmetric a L s ε (M-u • 1) (hshift u) i j]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  by_cases hij : i=j <;> simp [hij,Ne.symm]

theorem symmetric_quadratic_lower_posDef {d : ℕ} (A : Precision d) (l : ℝ)
    (hl : 0<l) (hA : ∀ i j,A i j=A j i)
    (hlo : ∀ x : Space d,l*‖x‖^2≤matrixQuadratic A x) : A.PosDef := by
  have hherm : A.IsHermitian := by
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hA j i
  refine ⟨hherm,?_⟩
  intro x hx
  let y : Space d := WithLp.toLp 2 x
  have hy : y≠0 := by
    intro hy
    apply hx
    ext j
    exact congrArg (fun z : Space d=>z j) hy
  have hh := hlo y
  have hp : 0<l*‖y‖^2 := mul_pos hl (sq_pos_of_pos (norm_pos_iff.mpr hy))
  have ht : 0<matrixQuadratic A x := hp.trans_le hh
  simpa only [matrixQuadratic,star_trivial] using ht

end Paper254
#print axioms Paper254.rationalSpectralClip_error
#print axioms Paper254.rationalSpectralClip_interval
