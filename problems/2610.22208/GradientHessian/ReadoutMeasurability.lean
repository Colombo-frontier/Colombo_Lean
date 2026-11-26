import GradientHessian.ReadoutCertificate

/-! Joint measurability of the exact readout in the source matrix and mark.
The finite policy gives this on all inputs, including the zero denominator. -/

namespace GradientHessian.ReadoutMeasurability
open Matrix Polynomial MeasureTheory LowRank ReadoutOracle
noncomputable section

theorem readout_joint_measurable {d : ℕ} (M : ℝ)
    (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ) :
    Measurable (fun t : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) =>
      readout M P t.1 fallback t.2) := by
  have h := measurable_runBoundedTwoSided d (ReadoutFilter.degree M ReadoutFilter.delta)
    (readoutPolicy M P fallback)
  convert h using 1
  funext t
  exact (readoutPolicy_exact M P t.1 fallback t.2).1.symm

theorem sourceMatrix_measurable {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ) :
    Measurable (MatrixGoodSpectrum.sourceMatrix (n := n) P J) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [MatrixGoodSpectrum.sourceMatrix, wishart, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem measurable_readout_comp {T : Type*} [MeasurableSpace T] {d : ℕ}
    (M : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ)
    (A : T → Matrix (Fin d) (Fin d) ℝ) (w : T → Fin d → ℝ)
    (hA : Measurable A) (hw : Measurable w) :
    Measurable (fun t => readout M P (A t) fallback (w t)) := by
  apply Measurable.comp
    (f := fun t : T => (A t, w t))
    (g := fun t : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => readout M P t.1 fallback t.2)
  · exact readout_joint_measurable M P fallback
  · exact hA.prodMk hw

theorem source_readout_joint_measurable {d n : ℕ} (J : ℕ)
    (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ) :
    Measurable (fun t : Matrix (Fin d) (Fin n) ℝ × (Fin d → ℝ) =>
      readout (ReadoutFilter.matrixUpper J) P
        (MatrixGoodSpectrum.sourceMatrix P J t.1) fallback t.2) := by
  apply measurable_readout_comp (ReadoutFilter.matrixUpper J) P fallback
    (fun t : Matrix (Fin d) (Fin n) ℝ × (Fin d → ℝ) => MatrixGoodSpectrum.sourceMatrix P J t.1)
    Prod.snd
  · exact (sourceMatrix_measurable (n := n) P J).comp measurable_fst
  · exact measurable_snd

/-- The omitted initial projection is exactly redundant for every admissible
mark. This equality also holds away from the good source event. -/
theorem readout_eq_literal {d : ℕ} (M : ℝ)
    (P A : Matrix (Fin d) (Fin d) ℝ) (fallback w : Fin d → ℝ)
    (hw : P *ᵥ w = w) :
    readout M P A fallback w = ReadoutOracle.normalize fallback
      (((1 - P) * aeval A (ReadoutFilter.filterPolynomial M ReadoutFilter.delta) * P) *ᵥ w) := by
  simp only [readout, ← Matrix.mulVec_mulVec, hw]

end
end GradientHessian.ReadoutMeasurability
