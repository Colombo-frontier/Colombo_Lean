import GradientHessian.MatrixGoodSpectrum
import GradientHessian.MatrixCompressionInterval

/-! The complete source `lem:good`: the actual conditioned-source event has
probability at least `.99`, and implies every deterministic matrix assertion.
All matrix and kernel objects retain the literal Gaussian source definitions. -/

namespace GradientHessian.MatrixGoodAnalytic
open Matrix LowRank MatrixGoodSpectrum MatrixKernelConcentration
  MatrixProjectorCompression MatrixCompressionInterval
open scoped Matrix
noncomputable section

variable {d n : ℕ}

/-- The deterministic assertions of source equation `analytic-matrix`, together
with exact identification of the kernel and the displayed compression formula. -/
structure GoodAnalytic (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ)
    (X : Matrix (Fin d) (Fin n) ℝ) : Prop where
  matrix_lower : LoewnerLE 1 (sourceMatrix P J X)
  matrix_upper : LoewnerLE (sourceMatrix P J X) ((1+4096*(J:ℝ)^2) • 1)
  matrix_gap : LoewnerLE (sourceKernel P J X+(5:ℝ) • (1-sourceKernel P J X)) (sourceMatrix P J X)
  kernel_projector : IsOrthogonalProjector (sourceKernel P J X)
  kernel_action : sourceMatrix P J X*sourceKernel P J X = sourceKernel P J X
  kernel_preimage : LinearMap.range (sourceKernel P J X).mulVecLin =
    (LinearMap.ker (wishart X).mulVecLin).comap
      (dilation P (Real.sqrt (1/(J:ℝ)))).mulVecLin
  compression_identity : P*sourceKernel P J X*P =
    (P*leftKernelProjector X*P)*
      ((1/(J:ℝ)) • 1+(1-1/(J:ℝ)) • (P*leftKernelProjector X*P))⁻¹
  compression_lower : LoewnerLE ((1/3:ℝ) • P) (P*sourceKernel P J X*P)
  compression_upper : LoewnerLE (P*sourceKernel P J X*P) ((2/3:ℝ) • P)

/-- No spectral or projector identity is an extra assumption: all conclusions
are derived from membership in the three-test source event. -/
theorem sourceGoodEvent_analytic {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 4 ≤ J)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ sourceGoodEvent P J) : GoodAnalytic P J X := by
  have hJ₀ : 0 < J := by omega
  have hJR : (4:ℝ) ≤ J := by exact_mod_cast hJ
  have hη : 0 < 1/(J:ℝ) := by positivity
  have hη₁ : 1/(J:ℝ) ≤ 1/4 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4) hJR
  have hη₂ : 1/(J:ℝ) ≤ 1 := by linarith
  have hXi := sourceGoodEvent_injective P hJ₀ hX
  obtain ⟨hl, hu, hg, hk⟩ := sourceGoodEvent_spectral hP hJ₀ hX
  obtain ⟨hcl, hcu⟩ := transformed_kernel_interval X hXi hP hη hη₁ hX.2.2
  exact {
    matrix_lower := hl
    matrix_upper := hu
    matrix_gap := hg
    kernel_projector := sourceKernel_isProjector P J X
    kernel_action := hk
    kernel_preimage := transformed_kernel_range X hXi hP (Real.sqrt_pos.mpr hη).ne'
    compression_identity := transformed_kernel_compression X hXi hP hη hη₂
    compression_lower := hcl
    compression_upper := hcu }

/-- The claimed spectrum of the restriction, in any orthonormal coordinates
for `range P`. The bounds apply to every eigenvalue, including multiplicities. -/
theorem sourceGoodEvent_compressed_spectrum {r : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 4 ≤ J)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ sourceGoodEvent P J)
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ*B = 1) (hPB : P*B = B)
    (sp : OrderedMatrixSpectrum (Bᵀ*sourceKernel P J X*B)) (i : Fin r) :
    sp.value i ∈ Set.Icc (1/3) (2/3) := by
  have h := sourceGoodEvent_analytic hP hJ hX
  exact compressed_range_spectrum hP ⟨h.compression_lower, h.compression_upper⟩ B hB hPB sp i

/-- Complete verified form of `lem:good`, with explicit sufficient absolute
constants `J₀ = 4` and `κ₀ = 18874368`. -/
theorem positive_probability_source_and_compressed_kernel {J r κ k D : ℕ}
    (hJ : 4 ≤ J) (hr : 1+4096*J^2 ≤ r) (hκ : 18874368 ≤ κ)
    (hk : k = κ*r) (hD : D = k*J)
    (P : Matrix (Fin D) (Fin D) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank = r) :
    99/100 ≤ (gaussianMatrixLaw D (D-k)).real (sourceGoodEvent P J) ∧
      ∀ X ∈ sourceGoodEvent P J, GoodAnalytic P J (X : Matrix (Fin D) (Fin (D-k)) ℝ) :=
  ⟨manuscript_sourceGoodEvent_probability hJ hr hκ hk hD P hP hrank,
    fun _ hX => sourceGoodEvent_analytic hP hJ hX⟩

end
end GradientHessian.MatrixGoodAnalytic
