import LowRank.KernelProjectorGram
import LowRank.GramSpectrum
import LowRank.MatrixNetBound
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact compression of the projector onto the transformed Wishart kernel.
The projector identity is derived from the actual rectangular matrix kernel,
without assuming the manuscript's compression formula. -/

namespace GradientHessian.MatrixProjectorCompression
open Matrix LowRank
open scoped Matrix BigOperators
noncomputable section

variable {d n : ℕ}

def dilation (P : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) := 1+(s-1) • P

theorem dilation_symmetric {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (s : ℝ) : (dilation P s)ᵀ = dilation P s := by
  simp only [dilation, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hP.symmetric]

theorem dilation_mul {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (s t : ℝ) : dilation P s * dilation P t = dilation P (s*t) := by
  simp only [dilation, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP.idempotent]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem dilation_one (P : Matrix (Fin d) (Fin d) ℝ) : dilation P 1 = 1 := by
  simp [dilation]

theorem dilation_mul_inverse {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {s : ℝ} (hs : s ≠ 0) : dilation P s * dilation P s⁻¹ = 1 := by
  rw [dilation_mul hP, mul_inv_cancel₀ hs, dilation_one]

theorem dilation_injective {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {s : ℝ} (hs : s ≠ 0) : Function.Injective (dilation P s).mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (dilation_mul_inverse hP hs))

theorem leftKernelProjector_mul_of_annihilated (X : Matrix (Fin d) (Fin n) ℝ)
    (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Xᵀ*Y = 0) : leftKernelProjector X*Y = Y := by
  simp only [leftKernelProjector, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    hY, Matrix.mul_zero, sub_zero]

theorem transformed_kernel_relations (X : Matrix (Fin d) (Fin n) ℝ)
    (hX : Function.Injective X.mulVec) {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {s : ℝ} (hs : s ≠ 0) :
    leftKernelProjector X*dilation P s*leftKernelProjector (dilation P s*X) =
      dilation P s*leftKernelProjector (dilation P s*X) ∧
    leftKernelProjector (dilation P s*X)*dilation P s⁻¹*leftKernelProjector X =
      dilation P s⁻¹*leftKernelProjector X := by
  have hDX : Function.Injective (dilation P s*X).mulVec := by
    intro x y hxy
    apply hX
    apply dilation_injective hP hs
    simpa only [Matrix.mulVec_mulVec] using hxy
  constructor
  · rw [Matrix.mul_assoc]
    apply leftKernelProjector_mul_of_annihilated
    have h := transpose_mul_leftKernelProjector (dilation P s*X) hDX
    simpa only [Matrix.transpose_mul, dilation_symmetric hP, Matrix.mul_assoc] using h
  · rw [Matrix.mul_assoc]
    apply leftKernelProjector_mul_of_annihilated
    simp only [Matrix.transpose_mul, dilation_symmetric hP]
    calc
      _ = Xᵀ*(dilation P s*dilation P s⁻¹)*leftKernelProjector X := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [dilation_mul_inverse hP hs, Matrix.mul_one, transpose_mul_leftKernelProjector X hX]

theorem compression_equation {P K Q : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hK : IsOrthogonalProjector K) (hQ : IsOrthogonalProjector Q)
    {s : ℝ} (hs : s ≠ 0) (h₁ : K*dilation P s*Q = dilation P s*Q)
    (h₂ : Q*dilation P s⁻¹*K = dilation P s⁻¹*K) :
    (P*Q*P)*(s^2 • 1+(1-s^2) • (P*K*P)) = P*K*P := by
  have h₁t := congrArg Matrix.transpose h₁
  simp only [Matrix.transpose_mul, hP.symmetric, hK.symmetric, hQ.symmetric,
    dilation_symmetric hP] at h₁t
  have ha := congrArg (fun M => P*M*P) h₁t
  have hb := congrArg (fun M => P*M*P) h₂
  have hPP (M : Matrix (Fin d) (Fin d) ℝ) : P*(P*M) = P*M := by
    rw [← Matrix.mul_assoc, hP.idempotent]
  simp only [dilation, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hP.idempotent, hPP] at ha hb ⊢
  ext i j
  have ha' := congrFun (congrFun ha i) j
  have hb' := congrFun (congrFun hb i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at ha' hb' ⊢
  field_simp [hs] at hb'
  have haS := congrArg (fun v : ℝ => s*v) ha'
  dsimp only at haS
  linear_combination hb' - haS

theorem scalar_identity_posDef (a : ℝ) (ha : 0 < a) :
    (a • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef := by
  rw [← real_diagonal_const]
  exact Matrix.PosDef.diagonal (fun _ => ha)

theorem compressed_projector_posSemidef {P K : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hK : IsOrthogonalProjector K) : (P*K*P).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial, hP.symmetric] using
    hK.posSemidef.conjTranspose_mul_mul_same P

theorem resolvent_posDef {P K : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hK : IsOrthogonalProjector K)
    {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) :
    (η • 1+(1-η) • (P*K*P)).PosDef :=
  (scalar_identity_posDef η hη).add_posSemidef
    (psd_smul (compressed_projector_posSemidef hP hK) (sub_nonneg.mpr hη₁))

/-- The exact displayed compression identity, in full ambient coordinates.
Its restriction to `range P` is the formula stated in the manuscript. -/
theorem transformed_kernel_compression (X : Matrix (Fin d) (Fin n) ℝ)
    (hX : Function.Injective X.mulVec) {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) :
    P*leftKernelProjector (dilation P (Real.sqrt η)*X)*P =
      (P*leftKernelProjector X*P)*
        (η • 1+(1-η) • (P*leftKernelProjector X*P))⁻¹ := by
  have hs : Real.sqrt η ≠ 0 := (Real.sqrt_pos.mpr hη).ne'
  obtain ⟨ha, hb⟩ := transformed_kernel_relations X hX hP hs
  have he := compression_equation hP (leftKernelProjector_isProjector X)
    (leftKernelProjector_isProjector (dilation P (Real.sqrt η)*X)) hs ha hb
  rw [Real.sq_sqrt hη.le] at he
  have hd := (resolvent_posDef hP (leftKernelProjector_isProjector X) hη hη₁).isUnit
  have hi := Matrix.mul_nonsing_inv (η • 1+(1-η) • (P*leftKernelProjector X*P))
    ((Matrix.isUnit_iff_isUnit_det _).mp hd)
  calc
    _ = (P*leftKernelProjector (dilation P (Real.sqrt η)*X)*P)*
        ((η • 1+(1-η) • (P*leftKernelProjector X*P))*
          (η • 1+(1-η) • (P*leftKernelProjector X*P))⁻¹) := by rw [hi, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, he]

/-- The transformed projector is the projector onto the literal preimage
of the Wishart kernel under the invertible source dilation. -/
theorem transformed_kernel_range (X : Matrix (Fin d) (Fin n) ℝ)
    (hX : Function.Injective X.mulVec) {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {s : ℝ} (hs : s ≠ 0) :
    LinearMap.range (leftKernelProjector (dilation P s*X)).mulVecLin =
      (LinearMap.ker (wishart X).mulVecLin).comap (dilation P s).mulVecLin := by
  have hDX : Function.Injective (dilation P s*X).mulVec := by
    intro x y hxy
    apply hX
    apply dilation_injective hP hs
    simpa only [Matrix.mulVec_mulVec] using hxy
  rw [leftKernelProjector_range _ hDX]
  ext z
  change (dilation P s*X)ᵀ*ᵥ z = 0 ↔ wishart X*ᵥ (dilation P s*ᵥ z) = 0
  rw [wishart, gram_kernel_iff]
  simp only [Matrix.transpose_mul, dilation_symmetric hP, Matrix.mulVec_mulVec]

end
end GradientHessian.MatrixProjectorCompression
