import Nonsmooth.GaussianEnergy
import Nonsmooth.GaussianFourth
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Metric Filter Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem standardGaussian_square_memLp : MemLp (fun z : ℝ => z ^ 2) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (continuous_id.pow 2).measurable.aestronglyMeasurable).mpr
  simpa only [Pi.pow_apply, id_eq, ← pow_mul, show 2 * 2 = 4 from rfl] using standardGaussian_power_integrable 4

theorem standardGaussian_square_variance : variance (fun z : ℝ => z ^ 2) (gaussianReal 0 1) = 2 := by
  rw [variance_eq_sub standardGaussian_square_memLp]
  simp only [Pi.pow_apply, ← pow_mul, show 2 * 2 = 4 from rfl,
    standardGaussian_fourth_moment, standardGaussian_second_moment]
  norm_num

theorem standardGaussianCoordinates_square_identDistrib {d : ℕ} (i : Fin d) :
    IdentDistrib (fun v : Fin d → ℝ => (v i) ^ 2) (fun z : ℝ => z ^ 2)
      (standardGaussianCoordinates d) (gaussianReal 0 1) := by
  have hp := finite_product_coordinate (gaussianReal 0 1) i
  have hi : IdentDistrib (fun v : Fin d → ℝ => v i) id (standardGaussianCoordinates d) (gaussianReal 0 1) :=
    ⟨hp.measurable.aemeasurable, measurable_id.aemeasurable, by simpa only [Measure.map_id, standardGaussianCoordinates] using hp.map_eq⟩
  exact hi.comp (measurable_id.pow_const 2)

theorem standardGaussianCoordinates_sum_memLp (d : ℕ) :
    MemLp (fun v : Fin d → ℝ => ∑ i, (v i) ^ 2) 2 (standardGaussianCoordinates d) := by
  have h := memLp_finsetSum' (Finset.univ : Finset (Fin d)) (fun i _ =>
    (standardGaussianCoordinates_square_identDistrib i).memLp_iff.mpr standardGaussian_square_memLp)
  simpa only [Finset.sum_fn] using h

theorem standardGaussianCoordinates_sum_variance (d : ℕ) :
    variance (fun v : Fin d → ℝ => ∑ i, (v i) ^ 2) (standardGaussianCoordinates d) = 2 * (d : ℝ) := by
  have hLp (i : Fin d) : MemLp (fun v : Fin d → ℝ => (v i) ^ 2) 2 (standardGaussianCoordinates d) :=
    (standardGaussianCoordinates_square_identDistrib i).memLp_iff.mpr standardGaussian_square_memLp
  have hvar (i : Fin d) : variance (fun v : Fin d → ℝ => (v i) ^ 2) (standardGaussianCoordinates d) = 2 :=
    (standardGaussianCoordinates_square_identDistrib i).variance_eq.trans standardGaussian_square_variance
  have hind : iIndepFun (fun i (v : Fin d → ℝ) => (v i) ^ 2) (standardGaussianCoordinates d) :=
    (finite_product_independent (gaussianReal 0 1) d).comp (fun _ z => z ^ 2) (fun _ => measurable_id.pow_const 2)
  have h := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hLp i)
    (fun i _ j _ hij => hind.indepFun hij)
  simpa only [Finset.sum_fn, hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_comm] using h

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianSynthesis_norm_square (v : Fin (Module.finrank ℝ E) → ℝ) :
    ‖gaussianSynthesis E v‖ ^ 2 = ∑ i, (v i) ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs, gaussianSynthesis_coordinate] using
    ((stdOrthonormalBasis ℝ E).sum_sq_norm_inner_right (gaussianSynthesis E v)).symm

theorem euclideanGaussian_norm_square_identDistrib :
    IdentDistrib (fun v : Fin (Module.finrank ℝ E) → ℝ => ∑ i, (v i) ^ 2)
      (fun z : E => ‖z‖ ^ 2) (standardGaussianCoordinates (Module.finrank ℝ E)) (euclideanGaussianLaw E) := by
  have hi : IdentDistrib (gaussianSynthesis E) id
      (standardGaussianCoordinates (Module.finrank ℝ E)) (euclideanGaussianLaw E) :=
    ⟨gaussianSynthesis_continuous.measurable.aemeasurable, measurable_id.aemeasurable,
      by rw [Measure.map_id]; rfl⟩
  have h := hi.comp (continuous_norm.pow 2).measurable
  simpa only [Function.comp_def, id_eq, Pi.pow_apply, gaussianSynthesis_norm_square] using h

theorem euclideanGaussian_norm_square_memLp : MemLp (fun z : E => ‖z‖ ^ 2) 2 (euclideanGaussianLaw E) :=
  euclideanGaussian_norm_square_identDistrib.memLp_iff.mp (standardGaussianCoordinates_sum_memLp _)

theorem euclideanGaussian_norm_square_variance :
    variance (fun z : E => ‖z‖ ^ 2) (euclideanGaussianLaw E) = 2 * (Module.finrank ℝ E : ℝ) :=
  euclideanGaussian_norm_square_identDistrib.variance_eq.symm.trans (standardGaussianCoordinates_sum_variance _)

theorem euclideanGaussian_norm_centered_square :
    (∫ z : E, (‖z‖ ^ 2 - (Module.finrank ℝ E : ℝ)) ^ 2 ∂euclideanGaussianLaw E) =
      2 * (Module.finrank ℝ E : ℝ) := by
  have h := variance_eq_integral (X := fun z : E => ‖z‖ ^ 2)
    (μ := euclideanGaussianLaw E) (by fun_prop)
  rw [euclideanGaussian_norm_square_variance, euclideanGaussian_norm_second_moment] at h
  exact h.symm

theorem euclideanGaussian_norm_square_lower_tail :
    (euclideanGaussianLaw E).real {z : E | ‖z‖ ^ 2 < (Module.finrank ℝ E : ℝ) / 2} ≤
      8 / (Module.finrank ℝ E : ℝ) := by
  let d := Module.finrank ℝ E
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hi : Integrable (fun z : E => (‖z‖ ^ 2 - (d : ℝ)) ^ 2) (euclideanGaussianLaw E) :=
    (euclideanGaussian_norm_square_memLp.sub (memLp_const (d : ℝ))).integrable_sq
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := euclideanGaussianLaw E)
    (f := fun z : E => (‖z‖ ^ 2 - (d : ℝ)) ^ 2) (Eventually.of_forall (fun z => sq_nonneg _)) hi
    (((d : ℝ) / 2) ^ 2)
  rw [euclideanGaussian_norm_centered_square] at hm
  have hs : (euclideanGaussianLaw E).real {z : E | ‖z‖ ^ 2 < (d : ℝ) / 2} ≤
      (euclideanGaussianLaw E).real {z : E | ((d : ℝ) / 2) ^ 2 ≤ (‖z‖ ^ 2 - (d : ℝ)) ^ 2} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro z hz
    change ((d : ℝ) / 2) ^ 2 ≤ (‖z‖ ^ 2 - (d : ℝ)) ^ 2
    nlinarith [show ‖z‖ ^ 2 < (d : ℝ) / 2 from hz]
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg ((d : ℝ) / 2))
  change (euclideanGaussianLaw E).real {z : E | ‖z‖ ^ 2 < (d : ℝ) / 2} ≤ 8 / (d : ℝ)
  apply (le_div_iff₀ hd).mpr
  nlinarith

end
end Nonsmooth
