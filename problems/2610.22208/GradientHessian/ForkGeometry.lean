import GradientHessian.ForkTrace
import GradientHessian.ReadoutCertificate

/-!
# Concrete kernel vectors in the chronological fork

The vectors use the source dilation and source kernel projector.  Their
normalizers are the actual ideal readout norms.  The geometry is deterministic
on the already-proved source event; no adaptive or probabilistic claim is
assumed here.
-/

namespace GradientHessian.ForkGeometry

open Matrix Polynomial LowRank
open GradientHessian.MatrixGoodSpectrum GradientHessian.MatrixProjectorCompression
open GradientHessian.MatrixAnalyticNorms GradientHessian.ReadoutSpectral
open GradientHessian.ReadoutNormalization GradientHessian.ReadoutCertificate
open GradientHessian.ForkTrace
open scoped Matrix InnerProductSpace
noncomputable section

def idealResidual {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  matrixEuclideanMap ((1-P)*Q) w

def idealReadout {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℝ)
    (w : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  direction (idealResidual P Q w)

def kernelVector {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ)
    (X : Matrix (Fin d) (Fin n) ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  ‖idealResidual P (sourceKernel P J X) w‖⁻¹ •
    matrixEuclideanMap (dilation P (Real.sqrt (1/(J:ℝ)))*sourceKernel P J X) w

theorem source_ideal_bounds {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 4 ≤ J)
    {X : Matrix (Fin d) (Fin n) ℝ}
    (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (hPw : P *ᵥ ⇑w = ⇑w) :
    Real.sqrt 2/3 ≤ ‖idealResidual P (sourceKernel P J X) w‖ ∧
      ‖idealResidual P (sourceKernel P J X) w‖ ≤ 1/2 := by
  have h := MatrixGoodAnalytic.sourceGoodEvent_analytic hP hJ hX
  have hb := cross_projection_norm_bounds hP h.kernel_projector
    h.compression_lower h.compression_upper w hw hPw
  have he : matrixEuclideanMap ((1-P)*sourceKernel P J X*P) w =
      idealResidual P (sourceKernel P J X) w := by
    ext i
    change (((1-P)*sourceKernel P J X*P)*ᵥ ⇑w) i =
      (((1-P)*sourceKernel P J X)*ᵥ ⇑w) i
    rw [← Matrix.mulVec_mulVec,hPw]
  rwa [he] at hb

theorem dilation_complement {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (s : ℝ) : (1-P)*dilation P s = 1-P := by
  have hz : (1-P)*P = 0 := by rw [sub_mul,one_mul,hP.idempotent,sub_self]
  rw [dilation,mul_add,mul_one,Matrix.mul_smul,hz,smul_zero,add_zero]

theorem symmetric_map_inner {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : Aᵀ = A) (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪matrixEuclideanMap A x,y⟫_ℝ = ⟪x,matrixEuclideanMap A y⟫_ℝ := by
  rw [← ContinuousLinearMap.adjoint_inner_right,
    ← MatrixGoodUpper.matrixEuclideanMap_transpose,hA]

/-- The source fork vectors are genuine vectors of `ker W`. -/
theorem kernelVector_annihilated {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 0 < J)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : Function.Injective X.mulVec)
    (w : EuclideanSpace ℝ (Fin d)) : wishart X *ᵥ ⇑(kernelVector P J X w) = 0 := by
  have hr := sourceKernel_range X hX hP hJ
  have hmem : sourceKernel P J X *ᵥ ⇑w ∈ LinearMap.range (sourceKernel P J X).mulVecLin :=
    LinearMap.mem_range_self _ ⇑w
  rw [hr] at hmem
  change wishart X *ᵥ (dilation P (Real.sqrt (1/(J:ℝ))) *ᵥ
    (sourceKernel P J X *ᵥ ⇑w)) = 0 at hmem
  change wishart X *ᵥ (‖idealResidual P (sourceKernel P J X) w‖⁻¹ •
    ((dilation P (Real.sqrt (1/(J:ℝ)))*sourceKernel P J X)*ᵥ ⇑w)) = 0
  rw [Matrix.mulVec_smul,← Matrix.mulVec_mulVec,hmem,smul_zero]

theorem kernelVector_fixed {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 0 < J)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : Function.Injective X.mulVec)
    (w : EuclideanSpace ℝ (Fin d)) :
    leftKernelProjector X *ᵥ ⇑(kernelVector P J X w) = ⇑(kernelVector P J X w) := by
  have hJR : (0:ℝ)<J := by exact_mod_cast hJ
  have hk := (transformed_kernel_relations X hX hP
    (Real.sqrt_pos.mpr (by positivity : 0 < 1/(J:ℝ))).ne').1
  have hk' : leftKernelProjector X*(dilation P (Real.sqrt (1/(J:ℝ)))*sourceKernel P J X) =
      dilation P (Real.sqrt (1/(J:ℝ)))*sourceKernel P J X := by
    simpa only [sourceKernel,← Matrix.mul_assoc] using hk
  change leftKernelProjector X *ᵥ (‖idealResidual P (sourceKernel P J X) w‖⁻¹ •
    ((dilation P (Real.sqrt (1/(J:ℝ)))*sourceKernel P J X)*ᵥ ⇑w)) = _
  rw [Matrix.mulVec_smul,Matrix.mulVec_mulVec]
  change ‖idealResidual P (sourceKernel P J X) w‖⁻¹ •
    ((leftKernelProjector X*(dilation P (Real.sqrt (1/(J:ℝ)))*sourceKernel P J X))*ᵥ ⇑w) = _
  rw [hk']
  rfl

/-- The exact identity linking projected tests to the ideal readout. -/
theorem kernelVector_inner {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (J : ℕ) (X : Matrix (Fin d) (Fin n) ℝ)
    (w y : EuclideanSpace ℝ (Fin d)) :
    ⟪kernelVector P J X w,matrixEuclideanMap (1-P) y⟫_ℝ =
      ⟪idealReadout P (sourceKernel P J X) w,y⟫_ℝ := by
  unfold kernelVector idealReadout direction idealResidual
  rw [real_inner_smul_left,real_inner_smul_left]
  congr 1
  rw [← symmetric_map_inner hP.complement.symmetric]
  simp only [← ContinuousLinearMap.comp_apply,← matrixEuclideanMap_mul]
  rw [← Matrix.mul_assoc,dilation_complement hP]

/-- The literal normalized readout is within `5 delta` of the ideal one. -/
theorem source_readout_perturbation {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 4 ≤ J)
    {X : Matrix (Fin d) (Fin n) ℝ}
    (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (fallback : Fin d → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (hw : ‖w‖ = 1) (hPw : P *ᵥ ⇑w = ⇑w) :
    ‖(WithLp.equiv 2 (Fin d → ℝ)).symm
      (ReadoutOracle.readout (ReadoutFilter.matrixUpper J) P (sourceMatrix P J X) fallback ⇑w) -
      idealReadout P (sourceKernel P J X) w‖ ≤ 5*ReadoutFilter.delta := by
  let A := sourceMatrix P J X
  let Q := sourceKernel P J X
  let F := aeval A (ReadoutFilter.filterPolynomial (ReadoutFilter.matrixUpper J) ReadoutFilter.delta)
  let u := matrixEuclideanMap (1-P) (matrixEuclideanMap F w)
  let v := idealResidual P Q w
  have h := MatrixGoodAnalytic.sourceGoodEvent_analytic hP hJ hX
  have hv := source_ideal_bounds hP hJ hX w hw hPw
  have hM : 16 ≤ ReadoutFilter.matrixUpper J := by
    have hJR : (4:ℝ)≤J := by exact_mod_cast hJ
    unfold ReadoutFilter.matrixUpper
    nlinarith
  have herr : ‖matrixEuclideanMap (F-Q)‖ ≤ ReadoutFilter.delta :=
    filter_error (sourceMatrix_posDef X hP J).isHermitian h.kernel_projector
      h.kernel_action h.matrix_gap hM h.matrix_upper
  have he : ‖u-v‖ ≤ ReadoutFilter.delta := by
    have hid : u-v = matrixEuclideanMap (1-P) (matrixEuclideanMap (F-Q) w) := by
      ext i
      change ((1-P)*ᵥ (F*ᵥ ⇑w)) i - (((1-P)*Q)*ᵥ ⇑w) i =
        ((1-P)*ᵥ ((F-Q)*ᵥ ⇑w)) i
      rw [← Matrix.mulVec_mulVec]
      simp only [Matrix.sub_mulVec,Matrix.mulVec_sub,Pi.sub_apply]
    rw [hid]
    calc
      _ ≤ ‖matrixEuclideanMap (F-Q) w‖ := by
        simpa only [one_mul] using (matrixEuclideanMap (1-P)).le_of_opNorm_le
          (projector_norm_le hP.complement) (matrixEuclideanMap (F-Q) w)
      _ ≤ ReadoutFilter.delta := by
        simpa only [hw,mul_one] using (matrixEuclideanMap (F-Q)).le_of_opNorm_le herr w
  obtain ⟨hul,_,_,_,hdiff⟩ := stable_readout_geometry hv.1 hv.2 he
  have hupos : 0 < ‖u‖ := by linarith
  rw [readout_lift_eq_direction _ P A fallback w hupos]
  exact hdiff

theorem hit_implies_projected_norm {d : ℕ} {P R : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hR : IsOrthogonalProjector R)
    (a a₀ c y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 1)
    (hfix : matrixEuclideanMap R (matrixEuclideanMap (1-P) y) = matrixEuclideanMap (1-P) y)
    (hideal : ⟪c,matrixEuclideanMap (1-P) y⟫_ℝ = ⟪a₀,y⟫_ℝ)
    (herr : ‖a-a₀‖ ≤ 5*ReadoutFilter.delta) {γ : ℝ}
    (hδ : 5*ReadoutFilter.delta ≤ γ/4) (hhit : γ < |⟪a,y⟫_ℝ|) :
    3*γ/4 < ‖matrixEuclideanMap R c‖ := by
  have he := abs_real_inner_le_norm (a-a₀) y
  have he' : |⟪a-a₀,y⟫_ℝ| ≤ 5*ReadoutFilter.delta :=
    he.trans ((mul_le_mul herr hy (norm_nonneg _)
      (mul_nonneg (by norm_num) ReadoutFilter.delta_pos.le)).trans_eq (mul_one _))
  have htri : |⟪a,y⟫_ℝ| ≤ |⟪a₀,y⟫_ℝ| + |⟪a-a₀,y⟫_ℝ| := by
    have heq : ⟪a,y⟫_ℝ = ⟪a₀,y⟫_ℝ + ⟪a-a₀,y⟫_ℝ := by rw [inner_sub_left]; ring
    rw [heq]
    exact abs_add _ _
  have hp : ‖matrixEuclideanMap (1-P) y‖ ≤ 1 :=
    ((matrixEuclideanMap (1-P)).le_of_opNorm_le (projector_norm_le hP.complement) y).trans
      (by simpa only [one_mul] using hy)
  have hi : ⟪a₀,y⟫_ℝ = ⟪matrixEuclideanMap R c,matrixEuclideanMap (1-P) y⟫_ℝ := by
    rw [symmetric_map_inner hR.symmetric,hfix,hideal]
  have hb : |⟪a₀,y⟫_ℝ| ≤ ‖matrixEuclideanMap R c‖ := by
    rw [hi]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _))
  linarith

end
end GradientHessian.ForkGeometry
