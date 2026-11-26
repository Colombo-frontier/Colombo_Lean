import HistoryIntermediateHeight254

noncomputable section
open Matrix
namespace Paper254

def inverseWorkHeight (d b : ℕ) := generalInverseStageHeight d b+
  inverseHeight d (2*b+d)+inverseHeight d b+4*b+2*d+10

def InverseWorkHeights {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) (b : ℕ) : Prop :=
  MatrixHeight A b ∧ MatrixHeight (Aᵀ*A) b ∧
  MatrixHeight (efficientInverse (Aᵀ*A)) b ∧ MatrixHeight (efficientGeneralInverse A) b ∧
  ∀ {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ),SchurDescendant (Aᵀ*A) B→
    SchurStageHeight B (efficientInverse (inverseSchur B)) b

theorem InverseWorkHeights.mono {d b c : ℕ} {A : Matrix (Fin d) (Fin d) ℚ}
    (h : InverseWorkHeights A b) (hbc : b≤c) : InverseWorkHeights A c := by
  exact ⟨h.1.mono hbc,h.2.1.mono hbc,h.2.2.1.mono hbc,h.2.2.2.1.mono hbc,
    fun B hB=>(h.2.2.2.2 B hB).mono hbc⟩

theorem inverse_work_heights {d b : ℕ} (A : Matrix (Fin d) (Fin d) ℚ)
    (hu : IsUnit A) (hh : MatrixHeight A b) : InverseWorkHeights A (inverseWorkHeight d b) := by
  have ho := efficientGeneralInverse_outer_height A hu hh
  have hc := countedGeneralInverse_certificate A hu hh
  refine ⟨hh.mono ?_,ho.1.mono ?_,ho.2.1.mono ?_,ho.2.2.mono ?_,?_⟩
  · dsimp [inverseWorkHeight]; omega
  · dsimp [inverseWorkHeight]; omega
  · dsimp [inverseWorkHeight]; omega
  · dsimp [inverseWorkHeight]; omega
  · intro n B hB
    exact (hc.2.2.2 B hB).mono (by dsimp [inverseWorkHeight]; omega)

def newtonWorkHeight (d a L s inputHeight : ℕ) :=
  inverseWorkHeight d (newtonStateHeight a L s)+newtonStateHeight a L s+
    inverseHeight d (newtonStateHeight a L s)+inputHeight+d+4

def NewtonWorkHeights {d : ℕ} (a L s : ℕ) (A : Matrix (Fin d) (Fin d) ℚ)
    (b : ℕ) : Prop :=
  let X := fun k=>efficientNewton (matrixSqrtPrecision a L s) A ((2:ℚ)^L • 1) k
  MatrixHeight A b ∧ (∀ k≤matrixSqrtIterations a L s,MatrixHeight (X k) b) ∧
  ∀ k<matrixSqrtIterations a L s,
    InverseWorkHeights (X k) b ∧
    MatrixHeight (efficientGeneralInverse (X k)*A) b ∧
    MatrixHeight (X k+efficientGeneralInverse (X k)*A) b ∧
    MatrixHeight ((1/2:ℚ) • (X k+efficientGeneralInverse (X k)*A)) b

theorem NewtonWorkHeights.mono {d a L s b c : ℕ} {A : Matrix (Fin d) (Fin d) ℚ}
    (h : NewtonWorkHeights a L s A b) (hbc : b≤c) : NewtonWorkHeights a L s A c := by
  refine ⟨h.1.mono hbc,fun k hk=>(h.2.1 k hk).mono hbc,?_⟩
  intro k hk
  have hh := h.2.2 k hk
  exact ⟨hh.1.mono hbc,hh.2.1.mono hbc,hh.2.2.1.mono hbc,hh.2.2.2.mono hbc⟩

theorem certified_newton_work_heights {d b : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (A : Matrix (Fin d) (Fin d) ℚ) (hheight : MatrixHeight A b)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (v : Coordinates d)
    (hv : ∀ j,0<v j) (hA : realMatrix A=rotatedPrecision U v)
    (hlo : ∀ j,((2:ℝ)^L)⁻¹≤Real.sqrt (v j))
    (hhi : ∀ j,Real.sqrt (v j)≤(2:ℝ)^L) :
    NewtonWorkHeights a L s A (newtonWorkHeight d a L s b) := by
  have hh := efficientNewton_prefix_height hd a L s hdim A U v hv hA hlo hhi
  have hu := certifiedMatrixSqrt_units hd a L s hdim A U v hv hA hlo hhi
  refine ⟨hheight.mono (by dsimp [newtonWorkHeight]; omega),?_,?_⟩
  · intro k hk
    exact (hh k hk).mono (by dsimp [newtonWorkHeight]; omega)
  · intro k hk
    let X := efficientNewton (matrixSqrtPrecision a L s) A ((2:ℚ)^L • 1) k
    have hX : MatrixHeight X (newtonStateHeight a L s) := hh k hk.le
    have hXu : IsUnit X := by
      dsimp [X]
      rw [efficientNewton_eq _ _ _ _ (fun j hj=>hu j (by omega))]
      exact realMatrix_unit_reflect _ (hu k hk.le)
    have hwork := inverse_work_heights X hXu hX
    have hinv : MatrixHeight (efficientGeneralInverse X) (inverseHeight d (newtonStateHeight a L s)) := by
      rw [efficientGeneralInverse_correct X hXu]
      exact hX.inv hXu
    have hprod := hinv.mul hheight
    have hsum := hX.add hprod
    have hhalf := MatrixHeight.smul rational_half_height hsum
    refine ⟨hwork.mono ?_,hprod.mono ?_,hsum.mono ?_,hhalf.mono ?_⟩
    all_goals dsimp [newtonWorkHeight]; omega

def sqrtInputHeight (d matrixHeight scalarHeight : ℕ) := 2*matrixHeight+2*scalarHeight+d+3
def positivePartWorkHeight (d a L s matrixHeight scalarHeight : ℕ) :=
  newtonWorkHeight d a L s (sqrtInputHeight d matrixHeight scalarHeight)+
    2*matrixHeight+2*scalarHeight+2*newtonStateHeight a L s+d+L+10

def PositivePartWorkHeights {d : ℕ} (a L s : ℕ) (eps : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) (b : ℕ) : Prop :=
  let R := efficientCertifiedMatrixSqrt a L s (rationalSqrtInput eps M)
  MatrixHeight M b ∧ MatrixHeight (M*M) b ∧
  MatrixHeight (eps^2 • (1:Matrix (Fin d) (Fin d) ℚ)) b ∧
  NewtonWorkHeights a L s (rationalSqrtInput eps M) b ∧
  MatrixHeight (R+Rᵀ) b ∧ MatrixHeight (rationalSymmetrize R) b ∧
  MatrixHeight (M+rationalSymmetrize R) b ∧ MatrixHeight (efficientPositivePart a L s eps M) b

theorem PositivePartWorkHeights.mono {d a L s b c : ℕ} {eps : ℚ}
    {M : Matrix (Fin d) (Fin d) ℚ} (h : PositivePartWorkHeights a L s eps M b)
    (hbc : b≤c) : PositivePartWorkHeights a L s eps M c := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  exact ⟨h1.mono hbc,h2.mono hbc,h3.mono hbc,h4.mono hbc,
    h5.mono hbc,h6.mono hbc,h7.mono hbc,h8.mono hbc⟩

theorem positive_part_work_heights {d m b : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (eps : ℚ) (heps : 0<(eps:ℝ))
    (heheight : RationalHeight eps b) (M : Matrix (Fin d) (Fin d) ℚ) (hheight : MatrixHeight M m)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (c : Coordinates d) (hM : realMatrix M=rotatedPrecision U c)
    (hlo : ((2:ℝ)^L)⁻¹≤(eps:ℝ)) (hhi : ∀ j,|c j|+(eps:ℝ)≤(2:ℝ)^L) :
    PositivePartWorkHeights a L s eps M (positivePartWorkHeight d a L s m b) := by
  let v : Coordinates d := fun j=>c j^2+(eps:ℝ)^2
  have hv : ∀ j,0<v j := by intro j; dsimp [v]; nlinarith [sq_nonneg (c j)]
  have hslo : ∀ j,((2:ℝ)^L)⁻¹≤Real.sqrt (v j) := by
    intro j
    have hh := Real.sq_sqrt (hv j).le
    have hn := Real.sqrt_nonneg (v j)
    have he : (eps:ℝ)≤Real.sqrt (v j) := by dsimp [v] at hh; nlinarith [sq_nonneg (c j)]
    exact hlo.trans he
  have hshi : ∀ j,Real.sqrt (v j)≤(2:ℝ)^L := by
    intro j
    have hh := Real.sq_sqrt (hv j).le
    have he : Real.sqrt (v j)≤|c j|+(eps:ℝ) := by
      dsimp [v] at hh
      nlinarith [sq_abs (c j),abs_nonneg (c j),mul_nonneg (abs_nonneg (c j)) heps.le]
    exact he.trans (hhi j)
  have hprod := hheight.mul hheight
  have hshift := MatrixHeight.smul (heheight.pow 2) (MatrixHeight.identity d)
  have hinput : MatrixHeight (rationalSqrtInput eps M) (sqrtInputHeight d m b) := by
    exact (hprod.add hshift).mono (by dsimp [sqrtInputHeight]; omega)
  have hwork := certified_newton_work_heights hd a L s hdim _ hinput U v hv
    (rationalSqrtInput_spectral eps M U c hM) hslo hshi
  have hroot : MatrixHeight (efficientCertifiedMatrixSqrt a L s (rationalSqrtInput eps M))
      (newtonStateHeight a L s) :=
    efficientNewton_prefix_height hd a L s hdim _ U v hv
      (rationalSqrtInput_spectral eps M U c hM) hslo hshi _ le_rfl
  have hsymSum := hroot.add hroot.transpose
  have hsym := MatrixHeight.smul rational_half_height hsymSum
  have hsum := hheight.add hsym
  have hpos : MatrixHeight (efficientPositivePart a L s eps M)
      (1+(m+(1+(newtonStateHeight a L s+newtonStateHeight a L s+1))+1)) := by
    have hh := MatrixHeight.smul rational_half_height hsum
    unfold efficientPositivePart efficientPositivePartRows
    rw [matrix_of_cached_rows,matrix_of_cached_rows]
    exact hh
  refine ⟨hheight.mono ?_,hprod.mono ?_,hshift.mono ?_,hwork.mono ?_,
    hsymSum.mono ?_,hsym.mono ?_,hsum.mono ?_,hpos.mono ?_⟩
  all_goals dsimp [positivePartWorkHeight]; omega

def spectralWorkHeight (d a L s m b : ℕ) :=
  b+2*positivePartWorkHeight d a L s (m+b+1) b+m+10

def SpectralWorkHeights {d : ℕ} (a L s : ℕ) (eps l u : ℚ)
    (M : Matrix (Fin d) (Fin d) ℚ) (b : ℕ) : Prop :=
  MatrixHeight (l • (1:Matrix (Fin d) (Fin d) ℚ)) b ∧
  MatrixHeight (u • (1:Matrix (Fin d) (Fin d) ℚ)) b ∧
  MatrixHeight (M-l • 1) b ∧ MatrixHeight (M-u • 1) b ∧
  PositivePartWorkHeights a L s eps (M-l • 1) b ∧
  PositivePartWorkHeights a L s eps (M-u • 1) b ∧
  MatrixHeight (l • 1+efficientPositivePart a L s eps (M-l • 1)) b ∧
  MatrixHeight (efficientSpectralClip a L s eps l u M) b

theorem SpectralWorkHeights.mono {d a L s b c : ℕ} {eps l u : ℚ}
    {M : Matrix (Fin d) (Fin d) ℚ} (h : SpectralWorkHeights a L s eps l u M b)
    (hbc : b≤c) : SpectralWorkHeights a L s eps l u M c := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  exact ⟨h1.mono hbc,h2.mono hbc,h3.mono hbc,h4.mono hbc,
    h5.mono hbc,h6.mono hbc,h7.mono hbc,h8.mono hbc⟩

theorem spectral_work_heights {d m b : ℕ} (hd : 0<d) (a L s : ℕ)
    (hdim : (d:ℝ)≤(2:ℝ)^a) (eps l u : ℚ) (heps : 0<(eps:ℝ))
    (heheight : RationalHeight eps b) (hlheight : RationalHeight l b) (huheight : RationalHeight u b)
    (M : Matrix (Fin d) (Fin d) ℚ) (hheight : MatrixHeight M m)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (c : Coordinates d) (hM : realMatrix M=rotatedPrecision U c)
    (hsmall : ((2:ℝ)^L)⁻¹≤(eps:ℝ))
    (hl : ∀ j,|c j-(l:ℝ)|+(eps:ℝ)≤(2:ℝ)^L)
    (hu : ∀ j,|c j-(u:ℝ)|+(eps:ℝ)≤(2:ℝ)^L) :
    SpectralWorkHeights a L s eps l u M (spectralWorkHeight d a L s m b) := by
  have hLI := MatrixHeight.smul hlheight (MatrixHeight.identity d)
  have hUI := MatrixHeight.smul huheight (MatrixHeight.identity d)
  have hleft : MatrixHeight (M-l • 1) (m+b+1) := by simpa using hheight.sub hLI
  have hright : MatrixHeight (M-u • 1) (m+b+1) := by simpa using hheight.sub hUI
  have hpl := positive_part_work_heights hd a L s hdim eps heps heheight _ hleft U
    (fun j=>c j-(l:ℝ)) (realMatrix_shift_spectral M U c hM l) hsmall hl
  have hpu := positive_part_work_heights hd a L s hdim eps heps heheight _ hright U
    (fun j=>c j-(u:ℝ)) (realMatrix_shift_spectral M U c hM u) hsmall hu
  have hplout := hpl.2.2.2.2.2.2.2
  have hpuout := hpu.2.2.2.2.2.2.2
  have hsum := hLI.add hplout
  have hout : MatrixHeight (efficientSpectralClip a L s eps l u M)
      (b+0+positivePartWorkHeight d a L s (m+b+1) b+1+
        positivePartWorkHeight d a L s (m+b+1) b+1) := by
    have hh := hsum.sub hpuout
    unfold efficientSpectralClip efficientSpectralClipRows
    rw [matrix_of_cached_rows,matrix_of_cached_rows,matrix_of_cached_rows]
    exact hh
  refine ⟨hLI.mono ?_,hUI.mono ?_,hleft.mono ?_,hright.mono ?_,
    hpl.mono ?_,hpu.mono ?_,hsum.mono ?_,hout.mono ?_⟩
  all_goals dsimp [spectralWorkHeight]; omega

end Paper254
#print axioms Paper254.positive_part_work_heights
