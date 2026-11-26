import GradientHessian.ReadoutMarks
import GradientHessian.ReadoutMeasurability
import GradientHessian.FreshMarkTests
import GradientHessian.SharpSphereTail
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-! Fresh spherical tests for the actual synthesized readout. Earlier data
may determine the test vector; the new mark is a separate product coordinate. -/

namespace GradientHessian.UnmarkedReadout
open MeasureTheory Matrix LowRank ReadoutMarks ReadoutOracle
open scoped InnerProductSpace
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem normalized_linear_tail (L : E →L[ℝ] F)
    (hl : ∀ z, ‖z‖ = 1 → 2 / 5 ≤ ‖L z‖) (hL : ‖L‖ ≤ 3 / 5)
    (y : F) (hy : ‖y‖ ≤ 1) {γ : ℝ} (hγ : 0 < γ) :
    (SphereGaussian.sphereLaw E).real
      {z | γ < |⟪ReadoutNormalization.direction (L z), y⟫_ℝ|} ≤
        2 * Real.exp (-(1 / 8) * γ ^ 2 * (Module.finrank ℝ E : ℝ)) := by
  let μ := SphereGaussian.sphereLaw E
  let v := ContinuousLinearMap.adjoint L y
  have hv : ‖v‖ ≤ 3 / 5 := adjoint_test_norm L hL y hy
  have he : {z | γ < |⟪ReadoutNormalization.direction (L z), y⟫_ℝ|} =ᵐ[μ]
      {z | ‖z‖ = 1 ∧ γ < |⟪ReadoutNormalization.direction (L z), y⟫_ℝ|} := by
    filter_upwards [SphereGaussian.sphereLaw_unit (E := E)] with z hz
    change (γ < |⟪ReadoutNormalization.direction (L z), y⟫_ℝ|) =
      (‖z‖ = 1 ∧ γ < |⟪ReadoutNormalization.direction (L z), y⟫_ℝ|)
    simp only [hz, true_and]
  rw [measureReal_congr he]
  have hsub : {z | ‖z‖ = 1 ∧ γ < |⟪ReadoutNormalization.direction (L z), y⟫_ℝ|} ⊆
      {z | (2 / 5) * γ ≤ |⟪v, z⟫_ℝ|} := by
    intro z hz
    exact (direction_hit_linear L z y hγ.le (hl z hz.1) hz.2).le
  apply (measureReal_mono hsub).trans
  by_cases hv0 : v = 0
  · have hpos : 0 < (2 / 5 : ℝ) * γ := by positivity
    simp only [hv0, inner_zero_left, abs_zero, not_le.mpr hpos, Set.setOf_false,
      measureReal_empty]
    positivity
  · apply (SharpSphereTail.sphereLaw_sharp_tail v hv0 (by positivity : 0 ≤ (2 / 5 : ℝ) * γ)).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    have hden : 0 < 2 * ‖v‖ ^ 2 := by positivity
    have hsq : ‖v‖ ^ 2 ≤ (3 / 5 : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hv
    have hp := mul_le_mul_of_nonneg_left hsq
      (by positivity : 0 ≤ (Module.finrank ℝ E : ℝ) * γ ^ 2)
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg (Nat.cast_nonneg (Module.finrank ℝ E)) (sq_nonneg γ)]

def sourceOutput {d r n : ℕ} (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin n) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (z : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm
    (readout (ReadoutFilter.matrixUpper J) P (MatrixGoodSpectrum.sourceMatrix P J X)
      fallback ⇑(matrixEuclideanMap B z))

theorem sourceOutput_measurable_comp {T : Type*} [MeasurableSpace T] {d r n : ℕ}
    (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (X : T → Matrix (Fin d) (Fin n) ℝ)
    (z : T → EuclideanSpace ℝ (Fin r)) (hX : Measurable X) (hz : Measurable z) :
    Measurable (fun t => sourceOutput J P (X t) B fallback (z t)) := by
  unfold sourceOutput
  apply Measurable.comp
    (g := (WithLp.equiv 2 (Fin d → ℝ)).symm)
    (f := fun t => readout (ReadoutFilter.matrixUpper J) P
      (MatrixGoodSpectrum.sourceMatrix P J (X t)) fallback ⇑(matrixEuclideanMap B (z t)))
  · exact (PiLp.continuous_equiv_symm 2 (fun _ : Fin d => ℝ)).measurable
  · apply ReadoutMeasurability.measurable_readout_comp
      (ReadoutFilter.matrixUpper J) P fallback
      (fun t => MatrixGoodSpectrum.sourceMatrix P J (X t))
      (fun t => ⇑(matrixEuclideanMap B (z t)))
    · exact (ReadoutMeasurability.sourceMatrix_measurable P J).comp hX
    · exact (PiLp.continuous_equiv 2 (fun _ : Fin d => ℝ)).measurable.comp
        ((matrixEuclideanMap B).continuous.measurable.comp hz)

/-- The literal unmarked test estimate, with the explicit absolute constant
`c = 1/8`, in orthonormal coordinates for the marked subspace. -/
theorem source_unmarked_test {d r n : ℕ} [NeZero r] {J : ℕ} (hJ : 4 ≤ J)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    {X : Matrix (Fin d) (Fin n) ℝ} (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ * B = 1) (hPB : P * B = B)
    (fallback : Fin d → ℝ) (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 1)
    {γ : ℝ} (hγ : 0 < γ) :
    (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).real
      {z | γ < |⟪sourceOutput J P X B fallback z, y⟫_ℝ|} ≤
        2 * Real.exp (-(1 / 8) * γ ^ 2 * (r : ℝ)) := by
  have he : {z | γ < |⟪sourceOutput J P X B fallback z, y⟫_ℝ|} =ᵐ[
      SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))]
      {z | γ < |⟪ReadoutNormalization.direction (markReadoutMap J P X B z), y⟫_ℝ|} := by
    filter_upwards [SphereGaussian.sphereLaw_unit (E := EuclideanSpace ℝ (Fin r))] with z hz
    change (γ < |⟪sourceOutput J P X B fallback z, y⟫_ℝ|) =
      (γ < |⟪ReadoutNormalization.direction (markReadoutMap J P X B z), y⟫_ℝ|)
    rw [sourceOutput, source_readout_eq_direction hJ hP hX B hB hPB fallback z hz]
  rw [measureReal_congr he]
  have h := normalized_linear_tail (markReadoutMap J P X B)
    (fun z hz => (markReadoutMap_bounds hJ hP hX B hB hPB z hz).1)
    (markReadoutMap_opNorm hJ hP hX B hB hPB) y hy hγ
  simpa using h

/-- The same estimate after all earlier data are fixed. The test and matrix
may depend arbitrarily and measurably on that data; the new mark is independent.
This supplies the chronological qualification in source `lem:unmarked`. -/
theorem source_unmarked_test_of_earlier_data {H : Type*} [MeasurableSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] {d r n : ℕ} [NeZero r]
    {J : ℕ} (hJ : 4 ≤ J) {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ * B = 1) (hPB : P * B = B)
    (fallback : Fin d → ℝ) (X : H → Matrix (Fin d) (Fin n) ℝ) (hXm : Measurable X)
    (hX : ∀ᵐ h ∂μ, X h ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (y : H → EuclideanSpace ℝ (Fin d)) (hym : Measurable y) (hy : ∀ᵐ h ∂μ, ‖y h‖ ≤ 1)
    {γ : ℝ} (hγ : 0 < γ) :
    (μ.prod (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r)))).real
      {t | γ < |⟪sourceOutput J P (X t.1) B fallback t.2, y t.1⟫_ℝ|} ≤
        2 * Real.exp (-(1 / 8) * γ ^ 2 * (r : ℝ)) := by
  apply FreshMarkTests.independent_hit_bound μ _
    (fun h z => γ < |⟪sourceOutput J P (X h) B fallback z, y h⟫_ℝ|)
  · apply measurableSet_lt measurable_const
    exact ((sourceOutput_measurable_comp J P B fallback
      (fun t : H × EuclideanSpace ℝ (Fin r) => X t.1) Prod.snd
      (hXm.comp measurable_fst) measurable_snd).inner (hym.comp measurable_fst)).abs
  · positivity
  · filter_upwards [hX, hy] with h hgood hunit
    exact source_unmarked_test hJ hP hgood B hB hPB fallback (y h) hunit hγ

end
end GradientHessian.UnmarkedReadout
