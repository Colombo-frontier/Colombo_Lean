import LowRank.PositiveSpectralSupport
import LowRank.KrylovGaussianGapTail

/-! If the Gaussian block is wide enough for the nonzero Gram spectrum,
one Krylov block already captures the matrix exactly, almost surely. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem spectral_support_fixed_of_startingBlock_rightInverse {a b r s : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (f : Fin r → Fin b) (hf : Function.Injective f) (hp : ∀ j, 0 < sp.value (f j))
    (hcover : ∀ i : Fin b, 0 < sp.value i → ∃ j, f j = i)
    (U : Matrix (Fin a) (Fin s) ℝ) (R : Matrix (Fin s) (Fin r) ℝ)
    (hR : ((positiveSpectralLeftColumns A sp f)ᵀ * U) * R = 1)
    {P : Matrix (Fin b) (Fin b) ℝ} (hfix : P * (Aᵀ * U) = Aᵀ * U) :
    P * Aᵀ = Aᵀ := by
  let V := sp.basis.submatrix id f
  let c := fun j : Fin r => Real.sqrt (sp.value (f j))
  let D := diagonal (fun j => (c j)⁻¹)
  have hinv : diagonal c * D = 1 := diagonal_mul_reciprocal c
    (fun j => ne_of_gt (Real.sqrt_pos.mpr (hp j)))
  have hrec : Aᵀ = V * (A * V)ᵀ := spectral_support_reconstruct A sp f hf hcover
  have hcoords := spectral_startingBlock_factor A sp f hp U
  rw [spectral_startingBlock_rows] at hcoords
  have hblock : Aᵀ * U = (V * diagonal c) * ((positiveSpectralLeftColumns A sp f)ᵀ * U) := by
    calc
      _ = (V * (A * V)ᵀ) * U := congrArg (fun M => M * U) hrec
      _ = _ := by rw [Matrix.mul_assoc, hcoords]; simp only [c, Matrix.mul_assoc]
  have hfactor : (Aᵀ * U) * R * D = V := by
    rw [hblock]
    calc
      _ = V * (diagonal c * (((positiveSpectralLeftColumns A sp f)ᵀ * U) * R) * D) := by
        simp only [Matrix.mul_assoc]
      _ = V := by rw [hR, Matrix.mul_one, hinv, Matrix.mul_one]
  have hV : P * V = V := by
    calc
      _ = P * ((Aᵀ * U) * R * D) := by rw [hfactor]
      _ = (P * (Aᵀ * U)) * R * D := by simp only [Matrix.mul_assoc]
      _ = V := by rw [hfix, hfactor]
  calc
    _ = P * (V * (A * V)ᵀ) := congrArg (fun M => P * M) hrec
    _ = V * (A * V)ᵀ := by rw [← Matrix.mul_assoc, hV]
    _ = Aᵀ := hrec.symm

theorem krylov_exact_of_support_rightInverse {a b r s n : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (f : Fin r → Fin b) (hf : Function.Injective f) (hp : ∀ j, 0 < sp.value (f j))
    (hcover : ∀ i : Fin b, 0 < sp.value i → ∃ j, f j = i)
    (U : Matrix (Fin a) (Fin s) ℝ) (R : Matrix (Fin s) (Fin r) ℝ)
    (hR : ((positiveSpectralLeftColumns A sp f)ᵀ * U) * R = 1) (hn : 0 < n) :
    A * columnRangeProjector (krylovRightBlocks (krylovBlockData A n U)) = A := by
  have hfix : columnRangeProjector (krylovRightBlocks (krylovBlockData A n U)) * (Aᵀ * U) =
      Aᵀ * U := by
    simpa only [pow_zero, Matrix.one_mul] using krylovProjector_fixes_power A U (⟨0, hn⟩ : Fin n)
  have h := spectral_support_fixed_of_startingBlock_rightInverse A sp f hf hp hcover U R hR hfix
  have ht := congrArg Matrix.transpose h
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
    (columnRangeProjector_isProjector _).symmetric] using ht

theorem krylov_gaussian_exact_of_positiveSpectrumSize_le {a b s n : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hs : positiveSpectrumSize sp ≤ s) (hn : 0 < n) :
    ∀ᵐ U ∂iidMatrixLaw a s 1,
      A * columnRangeProjector (krylovRightBlocks (krylovBlockData A n U)) = A := by
  let f := positiveSpectrumIndex sp
  let V := positiveSpectralLeftColumns A sp f
  have hV : Vᵀ * V = 1 := positiveSpectralLeftColumns_orthogonal A sp f
    (positiveSpectrumIndex_injective sp) (positiveSpectrumIndex_positive sp)
  filter_upwards [iidMatrixLaw_compressed_rightInverse_ae V hV hs
    (by norm_num : (1 : NNReal) ≠ 0)] with U hU
  exact krylov_exact_of_support_rightInverse A sp f (positiveSpectrumIndex_injective sp)
    (positiveSpectrumIndex_positive sp) (positiveSpectrumIndex_covers sp) U _ hU hn

theorem krylov_gaussian_exact_of_zero_tail {a m k s n : ℕ}
    (A : Matrix (Fin a) (Fin (m + k)) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A))
    (hz : ∀ i : Fin m, sp.value (i.castAdd k) = 0) (hs : k ≤ s) (hn : 0 < n) :
    ∀ᵐ U ∂iidMatrixLaw a s 1,
      A * columnRangeProjector (krylovRightBlocks (krylovBlockData A n U)) = A :=
  krylov_gaussian_exact_of_positiveSpectrumSize_le A sp
    ((positiveSpectrumSize_le_of_zero_tail A sp hz).trans hs) hn

end
end LowRank
