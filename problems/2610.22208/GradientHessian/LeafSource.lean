import GradientHessian.LeafLemma
import GradientHessian.SourceOperator

/-! Instantiation with the actual Gaussian source matrix and actual polynomial
readout. The inverse certificates and operator bounds are derived from the
source good event, not imposed as extra analytic premises. -/

noncomputable section
namespace GradientHessian.Leaf
open Matrix LowRank MatrixGoodSpectrum SourceOperator
open scoped InnerProductSpace

theorem source_matrix_norm {d n : ℕ} {J : ℕ} (hJ : 4 ≤ J)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J) :
    ‖matrixEuclideanMap (sourceMatrix P J X)‖ ≤ (4096*J^2:ℕ)+1 := by
  have hM : 0 ≤ 1+4096*(J:ℝ)^2 := by positivity
  have hI : (1 : Matrix (Fin d) (Fin d) ℝ).PosSemidef := by
    simpa only [one_smul] using
      (MatrixProjectorCompression.scalar_identity_posDef (d := d) 1 (by norm_num)).posSemidef
  have hl : LoewnerLE ((-(1+4096*(J:ℝ)^2)) • 1) (sourceMatrix P J X) := by
    have h := (sourceMatrix_posDef X hP J).posSemidef.add (psd_smul hI hM)
    simpa only [LoewnerLE, neg_smul, sub_neg_eq_add] using h
  have h := ReadoutSpectral.loewner_opNorm_le (sourceMatrix_posDef X hP J).isHermitian hM hl
    (sourceGoodEvent_spectral hP (by omega : 0 < J) hX).2.1
  convert h using 1
  push_cast
  ring

/-- Exact source task count M=1+4096 J², genuine common Euclidean leaf
coordinates, synthesized readout marks, and the full analytic leaf result. -/
theorem source_leaf_lemma {d n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {J : ℕ} (hJ : 4 ≤ J) {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (fallback : Fin d → ℝ) (w : Fin (4096*J^2+1) → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (hPw : ∀ i, P *ᵥ ⇑(w i) = ⇑(w i))
    (v : Fin (4096*J^2+1) → Fin (Inner.absoluteDepth+2) → E) (hv : ∀ i j, ‖v i j‖ = 1) :
    Bounds (matrixEuclideanMap (sourceMatrix P J X))
      (fun i => InverseGate.H₀ • w i) (fun i => readoutVector J P X fallback (w i)) v ∧
    objective (matrixEuclideanMap (sourceMatrix P J X))
      (fun i => InverseGate.H₀ • w i) (fun i => readoutVector J P X fallback (w i)) v
      (0 : Space (EuclideanSpace ℝ (Fin d)) E (4096*J^2+1)) = -10*InverseGate.H₀^2 ∧
    ∀ l, 0 ≤ l → ∀ Z, ‖gradient (driven (matrixEuclideanMap (sourceMatrix P J X))
      (fun i => InverseGate.H₀ • w i) (fun i => readoutVector J P X fallback (w i)) v l) Z‖ ≤ 1 →
        outgoing v Z = 1 := by
  apply leaf_lemma _ (source_lowerBound hP J X) (source_matrix_norm hJ hP hX)
    (matrixMap_symmetric (sourceMatrix_posDef X hP J).isHermitian)
    (fun i => InverseGate.H₀ • w i) (fun i => readoutVector J P X fallback (w i)) v
  · exact fun i => (source_inner_inputs hJ hP hX fallback (w i) (hw i) (hPw i)).1
  · exact fun i => (source_inner_inputs hJ hP hX fallback (w i) (hw i) (hPw i)).2.1
  · exact fun i => (source_inner_inputs hJ hP hX fallback (w i) (hw i) (hPw i)).2.2
  · exact hv

end GradientHessian.Leaf
