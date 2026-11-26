import GradientHessian.ReadoutOracle
import GradientHessian.ReadoutInverse
import GradientHessian.ReadoutProjection
import GradientHessian.ReadoutNormalization
import GradientHessian.InverseGateFunctions
import GradientHessian.MatrixGoodAnalytic

/-! The actual readout certificate on the manuscript's source event. The
polynomial, normalization, inverse, projection and numerical constants are
the ones defined and checked in the construction modules. -/

namespace GradientHessian.ReadoutCertificate

open Matrix Polynomial LowRank ReadoutSpectral ReadoutNormalization
  ReadoutOracle MatrixAnalyticNorms
open scoped InnerProductSpace
noncomputable section

theorem readout_lift_eq_direction {d : ℕ} (M : ℝ)
    (P A : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ)
    (w : EuclideanSpace ℝ (Fin d))
    (hu : 0 < ‖matrixEuclideanMap (1 - P)
      (matrixEuclideanMap (aeval A (ReadoutFilter.filterPolynomial M ReadoutFilter.delta)) w)‖) :
    (WithLp.equiv 2 (Fin d → ℝ)).symm (readout M P A fallback ⇑w) =
      direction (matrixEuclideanMap (1 - P)
        (matrixEuclideanMap (aeval A (ReadoutFilter.filterPolynomial M ReadoutFilter.delta)) w)) := by
  unfold readout ReadoutOracle.normalize
  rw [if_neg]
  · rfl
  · exact hu.ne'

theorem projector_inner_identity {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (z : EuclideanSpace ℝ (Fin d)) :
    ⟪matrixEuclideanMap P z, z⟫_ℝ = ‖matrixEuclideanMap P z‖ ^ 2 := by
  rw [real_inner_comm, matrixEuclideanMap_inner, map_norm_sq_gram,
    hP.symmetric, hP.idempotent]

theorem analytic_readout_certificate {d : ℕ} {P Q A : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hA : A.IsHermitian)
    (hQ : IsOrthogonalProjector Q) (hAQ : A * Q = Q)
    (hgap : LoewnerLE (Q + (5 : ℝ) • (1 - Q)) A) {M : ℝ} (hM : 16 ≤ M)
    (hupp : LoewnerLE A (M • 1))
    (hcl : LoewnerLE ((1 / 3 : ℝ) • P) (P * Q * P))
    (hcu : LoewnerLE (P * Q * P) ((2 / 3 : ℝ) • P))
    (fallback : Fin d → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (hPw : P *ᵥ ⇑w = ⇑w) :
    let F := aeval A (ReadoutFilter.filterPolynomial M ReadoutFilter.delta)
    let L := (1 - P) * F * P
    let a := readout M P A fallback ⇑w
    (2 / 5 ≤ ‖matrixEuclideanMap L w‖ ∧ ‖matrixEuclideanMap L w‖ ≤ 3 / 5) ∧
      euclideanNorm a = 1 ∧ P *ᵥ a = 0 ∧
      InverseGate.H₀ / 4 ≤ a ⬝ᵥ (A⁻¹ *ᵥ (InverseGate.H₀ • ⇑w)) := by
  let F := aeval A (ReadoutFilter.filterPolynomial M ReadoutFilter.delta)
  let u := matrixEuclideanMap (1 - P) (matrixEuclideanMap F w)
  let q := matrixEuclideanMap Q w
  let v := matrixEuclideanMap (1 - P) q
  let g := matrixEuclideanMap A⁻¹ w
  have hL (B : Matrix (Fin d) (Fin d) ℝ) :
      matrixEuclideanMap ((1 - P) * B * P) w =
        matrixEuclideanMap (1 - P) (matrixEuclideanMap B w) := by
    ext i
    change (((1 - P) * B * P) *ᵥ ⇑w) i = ((1 - P) *ᵥ (B *ᵥ ⇑w)) i
    rw [← Matrix.mulVec_mulVec, hPw, Matrix.mulVec_mulVec]
  have hv : Real.sqrt 2 / 3 ≤ ‖v‖ ∧ ‖v‖ ≤ 1 / 2 := by
    have h := cross_projection_norm_bounds hP hQ hcl hcu w hw hPw
    rw [hL Q] at h
    exact h
  have he : ‖u - v‖ ≤ ReadoutFilter.delta := by
    have heq : u - v = matrixEuclideanMap (1 - P) (matrixEuclideanMap (F - Q) w) := by
      ext i
      change ((1 - P) *ᵥ (F *ᵥ ⇑w)) i - ((1 - P) *ᵥ (Q *ᵥ ⇑w)) i =
        ((1 - P) *ᵥ ((F - Q) *ᵥ ⇑w)) i
      simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Pi.sub_apply]
    rw [heq]
    calc
      _ ≤ ‖matrixEuclideanMap (F - Q) w‖ := by
        simpa only [one_mul] using (matrixEuclideanMap (1 - P)).le_of_opNorm_le
          (projector_norm_le hP.complement) (matrixEuclideanMap (F - Q) w)
      _ ≤ ReadoutFilter.delta := by
        simpa only [hw, mul_one] using (matrixEuclideanMap (F - Q)).le_of_opNorm_le
          (filter_error hA hQ hAQ hgap hM hupp) w
  obtain ⟨_, hiq, hinv, hrest⟩ := inverse_bounds hA hQ hAQ hgap hupp
  have hg : ‖g‖ ≤ 1 := by
    simpa only [hw, mul_one] using (matrixEuclideanMap A⁻¹).le_of_opNorm_le hinv w
  have hcomp : ‖g - q‖ ≤ 1 / 5 := by
    have heq : g - q = matrixEuclideanMap (A⁻¹ * (1 - Q)) w := by
      ext i
      change ((A⁻¹ *ᵥ ⇑w) - (Q *ᵥ ⇑w)) i = ((A⁻¹ * (1 - Q)) *ᵥ ⇑w) i
      rw [mul_sub, mul_one, hiq, Matrix.sub_mulVec]
    rw [heq]
    simpa only [hw, mul_one] using
      (matrixEuclideanMap (A⁻¹ * (1 - Q))).le_of_opNorm_le hrest w
  have hvpos : 0 < ‖v‖ := by
    have hs := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    linarith [hv.1]
  have hideal : ⟪direction v, q⟫_ℝ = ‖v‖ := by
    have hi : ⟪v, q⟫_ℝ = ‖v‖ ^ 2 := projector_inner_identity hP.complement q
    rw [direction, real_inner_smul_left, hi]
    field_simp
    ring
  have hc := stable_inverse_certificate hv.1 hv.2 he hg hcomp hideal
  obtain ⟨hul, huh, _, _, _⟩ := stable_readout_geometry hv.1 hv.2 he
  have hupos : 0 < ‖u‖ := by linarith
  have ha := readout_lift_eq_direction M P A fallback w hupos
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL F]
    exact ⟨hul, huh⟩
  · change ‖(WithLp.equiv 2 (Fin d → ℝ)).symm (readout M P A fallback ⇑w)‖ = 1
    rw [ha]
    exact direction_norm hupos
  · unfold readout ReadoutOracle.normalize
    rw [if_neg (show euclideanNorm ((1 - P) *ᵥ (F *ᵥ ⇑w)) ≠ 0 from hupos.ne'),
      Matrix.mulVec_smul]
    have hzero : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP.idempotent, sub_self]
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hzero,
      Matrix.zero_mul, Matrix.zero_mulVec, smul_zero]
  · have hscaled := mul_le_mul_of_nonneg_left hc InverseGate.H₀_pos.le
    rw [← ha, matrixEuclideanMap_inner] at hscaled
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    convert hscaled using 1; ring

theorem source_readout_certificate {d n : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) {J : ℕ} (hJ : 4 ≤ J)
    {X : Matrix (Fin d) (Fin n) ℝ}
    (hX : X ∈ MatrixKernelConcentration.sourceGoodEvent P J)
    (fallback : Fin d → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (hPw : P *ᵥ ⇑w = ⇑w) :
    let A := MatrixGoodSpectrum.sourceMatrix P J X
    let F := aeval A (ReadoutFilter.filterPolynomial (ReadoutFilter.matrixUpper J) ReadoutFilter.delta)
    let a := readout (ReadoutFilter.matrixUpper J) P A fallback ⇑w
    (2 / 5 ≤ ‖matrixEuclideanMap ((1 - P) * F * P) w‖ ∧
      ‖matrixEuclideanMap ((1 - P) * F * P) w‖ ≤ 3 / 5) ∧
      euclideanNorm a = 1 ∧ P *ᵥ a = 0 ∧
      InverseGate.H₀ / 4 ≤ a ⬝ᵥ (A⁻¹ *ᵥ (InverseGate.H₀ • ⇑w)) := by
  have h := MatrixGoodAnalytic.sourceGoodEvent_analytic hP hJ hX
  have hM : 16 ≤ ReadoutFilter.matrixUpper J := by
    have hJr : (4 : ℝ) ≤ J := by exact_mod_cast hJ
    unfold ReadoutFilter.matrixUpper
    nlinarith
  exact analytic_readout_certificate hP (MatrixGoodSpectrum.sourceMatrix_posDef X hP J).isHermitian
    h.kernel_projector h.kernel_action h.matrix_gap hM h.matrix_upper
    h.compression_lower h.compression_upper fallback w hw hPw

/-- Instantiation of the finite exact simulation for the literal source matrix.
No good-event assumption is needed for the algorithm or its hard cap. -/
theorem source_readout_synthesis {d n : ℕ} (J : ℕ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (X : Matrix (Fin d) (Fin n) ℝ) (fallback w : Fin d → ℝ) :
    let M := ReadoutFilter.matrixUpper J
    let D := MatrixProjectorCompression.dilation P (Real.sqrt (1 / (J : ℝ)))
    let program := (readoutPolicy M P fallback).toProgram d
      (ReadoutFilter.degree M ReadoutFilter.delta) w
    let simulated := program.simulate (MatrixSandwichOracle.encode D)
      (MatrixSandwichOracle.decode (256 * (J : ℝ) ^ 2) D)
    simulated.eval (fun z => wishart X *ᵥ z) =
        readout M P (MatrixGoodSpectrum.sourceMatrix P J X) fallback w ∧
      simulated.calls (fun z => wishart X *ᵥ z) = ReadoutFilter.degree M ReadoutFilter.delta ∧
      simulated.HasBudget (ReadoutFilter.degree M ReadoutFilter.delta) :=
  readout_from_W (ReadoutFilter.matrixUpper J) (256 * (J : ℝ) ^ 2) P
    (MatrixProjectorCompression.dilation P (Real.sqrt (1 / (J : ℝ)))) (wishart X)
    (MatrixProjectorCompression.dilation_symmetric hP _) (wishart_symmetric X) fallback w

end
end GradientHessian.ReadoutCertificate
