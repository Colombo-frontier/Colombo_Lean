import GradientHessian.ReadoutCertificate
import GradientHessian.InnerLemma

/-! Transfer the literal Gaussian matrix and readout certificate to the
continuous-linear inverse and numerical inputs used by the actual inner scalar. -/

namespace GradientHessian.SourceOperator
open Matrix LowRank ReadoutOracle MatrixGoodSpectrum
open scoped InnerProductSpace
noncomputable section

theorem lowerBound_of_loewner {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : LoewnerLE 1 A) : InverseGate.LowerBound (matrixEuclideanMap A) := by
  intro x
  have h := hA.2 (⇑x)
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    euclidean_dot_self] at h
  rw [real_inner_comm, matrixEuclideanMap_inner]
  linarith

theorem matrixMap_symmetric {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪matrixEuclideanMap A x, y⟫_ℝ = ⟪x, matrixEuclideanMap A y⟫_ℝ := by
  exact (Matrix.isHermitian_iff_isSymmetric.mp hA) x y

theorem inverse_eq_matrix {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : InverseGate.LowerBound (matrixEuclideanMap A)) (hinv : A⁻¹ * A = 1) :
    InverseGate.inverse (matrixEuclideanMap A) hA = matrixEuclideanMap A⁻¹ := by
  have hleft (z : EuclideanSpace ℝ (Fin d)) :
      matrixEuclideanMap A⁻¹ (matrixEuclideanMap A z) = z := by
    ext i
    change (A⁻¹ *ᵥ (A *ᵥ ⇑z)) i = z i
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rfl
  ext x i
  have h := hleft (InverseGate.inverse (matrixEuclideanMap A) hA x)
  rw [InverseGate.apply_inverse] at h
  exact congrArg (fun z : EuclideanSpace ℝ (Fin d) => z i) h.symm

theorem source_lowerBound {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (J : ℕ) (X : Matrix (Fin d) (Fin n) ℝ) :
    InverseGate.LowerBound (matrixEuclideanMap (sourceMatrix P J X)) :=
  lowerBound_of_loewner (sourceMatrix_lower X hP J)

theorem source_inverse_eq {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (J : ℕ) (X : Matrix (Fin d) (Fin n) ℝ) :
    InverseGate.inverse (matrixEuclideanMap (sourceMatrix P J X)) (source_lowerBound hP J X) =
      matrixEuclideanMap (sourceMatrix P J X)⁻¹ := by
  apply inverse_eq_matrix
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (sourceMatrix_posDef X hP J).det_pos.ne')

def readoutVector {d n : ℕ} (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin n) ℝ) (fallback : Fin d → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm
    (readout (ReadoutFilter.matrixUpper J) P (sourceMatrix P J X) fallback ⇑w)

theorem source_inner_inputs {d n : ℕ} {J : ℕ} (hJ : 4 ≤ J)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (fallback : Fin d → ℝ) (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1)
    (hPw : P *ᵥ ⇑w = ⇑w) :
    ‖InverseGate.H₀ • w‖ = InverseGate.H₀ ∧ ‖readoutVector J P X fallback w‖ = 1 ∧
      InverseGate.H₀ / 4 ≤ ⟪readoutVector J P X fallback w,
        InverseGate.inverse (matrixEuclideanMap (sourceMatrix P J X))
          (source_lowerBound hP J X) (InverseGate.H₀ • w)⟫_ℝ := by
  have h := ReadoutCertificate.source_readout_certificate hP hJ hX fallback w hw hPw
  refine ⟨?_, h.2.1, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos InverseGate.H₀_pos, hw, mul_one]
  · rw [source_inverse_eq hP J X, matrixEuclideanMap_inner]
    exact h.2.2.2

/-- Complete inner activation for the actual source matrix and synthesized
marks, with no inverse-certificate hypothesis supplied by the caller. -/
theorem source_inner_activation {d n m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {J : ℕ} (hJ : 4 ≤ J) {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (fallback : Fin d → ℝ) (w : Fin (m + 1) → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (hPw : ∀ i, P *ᵥ ⇑(w i) = ⇑(w i))
    (v : Fin (m + 1) → Fin (Inner.absoluteDepth + 2) → E) (hv : ∀ i j, ‖v i j‖ = 1)
    {l : ℝ} (hl : 0 ≤ l)
    (Z : InnerCoordinates.Space (EuclideanSpace ℝ (Fin d)) E (m + 1) (Inner.absoluteDepth + 2))
    (hg : ‖gradient (Inner.driven (matrixEuclideanMap (sourceMatrix P J X))
      (fun i => InverseGate.H₀ • w i) (fun i => readoutVector J P X fallback (w i)) v l) Z‖ ≤ 1) :
    (∀ i, Inner.ports v Z i = 1) ∧
      ‖matrixEuclideanMap (sourceMatrix P J X)
        (InnerCoordinates.numerical _ _ (m + 1) (Inner.absoluteDepth + 2) Z)‖ ≤ 1 := by
  apply Inner.absolute_activation _ (source_lowerBound hP J X)
    (matrixMap_symmetric (sourceMatrix_posDef X hP J).isHermitian)
    (fun i => InverseGate.H₀ • w i) (fun i => readoutVector J P X fallback (w i)) v
  · exact fun i => (source_inner_inputs hJ hP hX fallback (w i) (hw i) (hPw i)).1
  · exact fun i => (source_inner_inputs hJ hP hX fallback (w i) (hw i) (hPw i)).2.1
  · exact fun i => (source_inner_inputs hJ hP hX fallback (w i) (hw i) (hPw i)).2.2
  · exact hv
  · exact hl
  · exact hg

theorem source_inner_bounds {d n m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hm : 1 ≤ m) {J : ℕ} (hJ : 4 ≤ J)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (fallback : Fin d → ℝ) (w : Fin m → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (hPw : ∀ i, P *ᵥ ⇑(w i) = ⇑(w i))
    (v : Fin m → Fin (Inner.absoluteDepth + 2) → E) (hv : ∀ i j, ‖v i j‖ = 1) :
    Inner.ResidualBounds (fun i => InverseGate.H₀ • w i)
      (fun i => readoutVector J P X fallback (w i)) v :=
  Inner.inner_bounds hm _ _ v
    (fun i => (source_inner_inputs hJ hP hX fallback (w i) (hw i) (hPw i)).1)
    (fun i => (source_inner_inputs hJ hP hX fallback (w i) (hw i) (hPw i)).2.1) hv

end
end GradientHessian.SourceOperator
