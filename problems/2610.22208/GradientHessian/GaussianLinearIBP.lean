import GradientHessian.GaussianConcentrationHilbertIBP
import GradientHessian.GaussianConcentrationIntegrability
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Gaussian integration by parts after arbitrary linear maps.  The
right-hand side is the actual Hessian trace, with all integrability
conditions derived from Lipschitz and bounded-Hessian hypotheses. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory GaussianHilbert
open scoped InnerProductSpace BigOperators NNReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem gaussian_linear_coordinate_ibp {f : F → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (A : E →L[ℝ] F) (c v : F) (i : Fin (Module.finrank ℝ E)) :
    (∫ z, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ * fderiv ℝ f (c + A z) v
      ∂euclideanGaussianLaw E) =
      ∫ z, fderiv ℝ (fderiv ℝ f) (c + A z) (A (stdOrthonormalBasis ℝ E i)) v
        ∂euclideanGaussianLaw E := by
  let g : E → ℝ := fun z => fderiv ℝ f (c + A z) v
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have hd (z : E) : HasFDerivAt g
      (((fderiv ℝ (fderiv ℝ f) (c + A z)).flip v).comp A) z := by
    have hp := (hdf (c + A z)).hasFDerivAt.clm_apply (hasFDerivAt_const v (c + A z))
    simp only [ContinuousLinearMap.comp_zero, zero_add] at hp
    exact hp.comp z (A.hasFDerivAt.const_add c)
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun z => (hd z).continuousAt)
  have hb (z : E) : ‖g z‖ ≤ (B : ℝ) * ‖v‖ :=
    ((fderiv ℝ f (c + A z)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg v))
  have hgi : Integrable g (euclideanGaussianLaw E) :=
    (integrable_const _).mono' hg.aestronglyMeasurable (ae_of_all _ hb)
  have hhcont : Continuous (fun z : E =>
      fderiv ℝ (fderiv ℝ f) (c + A z) (A (stdOrthonormalBasis ℝ E i)) v) :=
    (((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv
      (by norm_num)).comp (continuous_const.add A.continuous)).clm_apply
        continuous_const |>.clm_apply continuous_const
  have hhi : Integrable (fun z : E =>
      fderiv ℝ (fderiv ℝ f) (c + A z) (A (stdOrthonormalBasis ℝ E i)) v)
      (euclideanGaussianLaw E) := by
    refine (integrable_const ((C : ℝ) * ‖A (stdOrthonormalBasis ℝ E i)‖ * ‖v‖)).mono'
      hhcont.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    exact ((fderiv ℝ (fderiv ℝ f) (c + A z) _).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right
        (((fderiv ℝ (fderiv ℝ f) (c + A z)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hH _) (norm_nonneg _))) (norm_nonneg v))
  have hdi : Integrable (fun z => fderiv ℝ g z (stdOrthonormalBasis ℝ E i))
      (euclideanGaussianLaw E) := by
    simpa only [(hd _).fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] using hhi
  have hxi : Integrable (fun z => ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ * g z)
      (euclideanGaussianLaw E) := by
    refine ((norm_integrable E).mul_const ((B : ℝ) * ‖v‖)).mono'
      ((continuous_const.inner (𝕜 := ℝ) continuous_id).mul hg).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [norm_mul]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (stdOrthonormalBasis ℝ E i) z
    rw [(stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i, one_mul] at hi
    exact mul_le_mul hi (hb z) (norm_nonneg _) (norm_nonneg _)
  have h := hilbert_gaussian_integration_by_parts E i
    (fun z => (hd z).differentiableAt) hgi hdi hxi
  simpa only [(hd _).fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] using h

theorem gaussian_linear_ibp {f : F → ℝ} {B C : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hLip : LipschitzWith B f)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (C : ℝ))
    (A L : E →L[ℝ] F) (c : F) :
    (∫ z, fderiv ℝ f (c + A z) (L z) ∂euclideanGaussianLaw E) =
      ∫ z, ∑ i, fderiv ℝ (fderiv ℝ f) (c + A z)
        (A (stdOrthonormalBasis ℝ E i)) (L (stdOrthonormalBasis ℝ E i))
        ∂euclideanGaussianLaw E := by
  have he (z : E) : fderiv ℝ f (c + A z) (L z) =
      ∑ i, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ *
        fderiv ℝ f (c + A z) (L (stdOrthonormalBasis ℝ E i)) := by
    nth_rw 2 [← (stdOrthonormalBasis ℝ E).sum_repr' z]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hg (i : Fin (Module.finrank ℝ E)) : Integrable
      (fun z => ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ *
        fderiv ℝ f (c + A z) (L (stdOrthonormalBasis ℝ E i))) (euclideanGaussianLaw E) := by
    refine ((norm_integrable E).mul_const ((B : ℝ) * ‖L (stdOrthonormalBasis ℝ E i)‖)).mono'
      (by apply Continuous.aestronglyMeasurable
          exact (continuous_const.inner (𝕜 := ℝ) continuous_id).mul
            (((hf.continuous_fderiv (by norm_num)).comp (continuous_const.add A.continuous)).clm_apply
              continuous_const)) (ae_of_all _ fun z => ?_)
    rw [norm_mul]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (stdOrthonormalBasis ℝ E i) z
    rw [(stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i, one_mul] at hi
    exact mul_le_mul hi (((fderiv ℝ f _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)))
      (norm_nonneg _) (norm_nonneg _)
  have hh (i : Fin (Module.finrank ℝ E)) : Integrable
      (fun z => fderiv ℝ (fderiv ℝ f) (c + A z)
        (A (stdOrthonormalBasis ℝ E i)) (L (stdOrthonormalBasis ℝ E i)))
      (euclideanGaussianLaw E) := by
    refine (integrable_const ((C : ℝ) * ‖A (stdOrthonormalBasis ℝ E i)‖ *
      ‖L (stdOrthonormalBasis ℝ E i)‖)).mono' (by
        apply Continuous.aestronglyMeasurable
        exact (((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv
          (by norm_num)).comp (continuous_const.add A.continuous)).clm_apply
            continuous_const |>.clm_apply continuous_const) (ae_of_all _ fun z => ?_)
    exact ((fderiv ℝ (fderiv ℝ f) _ _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hH _) (norm_nonneg _))) (norm_nonneg _))
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ => hg i), integral_finset_sum _ (fun i _ => hh i)]
  exact Finset.sum_congr rfl (fun i _ => gaussian_linear_coordinate_ibp E hf hLip hH A c _ i)

end GradientHessian.GaussianConcentration
