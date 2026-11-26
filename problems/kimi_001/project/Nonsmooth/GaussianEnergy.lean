import Nonsmooth.GaussianPrior
import Nonsmooth.GaussianRealMoments

open MeasureTheory ProbabilityTheory Metric Filter Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_coordinate_measurePreserving (i : Fin (Module.finrank ℝ E)) :
    MeasurePreserving (fun z : E => ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ)
      (euclideanGaussianLaw E) (gaussianReal 0 1) :=
  ⟨(continuous_const.inner continuous_id).measurable, euclideanGaussianLaw_coordinate i⟩

theorem euclideanGaussian_coordinate_square_integrable (i : Fin (Module.finrank ℝ E)) :
    Integrable (fun z : E => ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ ^ 2) (euclideanGaussianLaw E) :=
  ((euclideanGaussian_coordinate_measurePreserving i).integrable_comp
    (continuous_id.pow 2).measurable.aestronglyMeasurable).mpr (standardGaussian_power_integrable 2)

theorem euclideanGaussian_coordinate_second_moment (i : Fin (Module.finrank ℝ E)) :
    (∫ z : E, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ ^ 2 ∂euclideanGaussianLaw E) = 1 := by
  have h := integral_map_of_stronglyMeasurable (μ := euclideanGaussianLaw E)
    (euclideanGaussian_coordinate_measurePreserving i).measurable (continuous_id.pow 2).stronglyMeasurable
  rw [euclideanGaussianLaw_coordinate i] at h
  exact h.symm.trans standardGaussian_second_moment

theorem euclideanGaussian_norm_square_integrable :
    Integrable (fun z : E => ‖z‖ ^ 2) (euclideanGaussianLaw E) := by
  have he (z : E) : (∑ i, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ ^ 2) = ‖z‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (stdOrthonormalBasis ℝ E).sum_sq_norm_inner_right z
  have hi := integrable_finset_sum Finset.univ
    (fun i _ => euclideanGaussian_coordinate_square_integrable (E := E) i)
  simpa only [he] using hi

theorem euclideanGaussian_norm_second_moment :
    (∫ z : E, ‖z‖ ^ 2 ∂euclideanGaussianLaw E) = (Module.finrank ℝ E : ℝ) := by
  have he (z : E) : ‖z‖ ^ 2 = ∑ i, ⟪stdOrthonormalBasis ℝ E i, z⟫_ℝ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using ((stdOrthonormalBasis ℝ E).sum_sq_norm_inner_right z).symm
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ => euclideanGaussian_coordinate_square_integrable i)]
  simp only [euclideanGaussian_coordinate_second_moment, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The source's truncation event has probability at least three quarters, from the
actual Gaussian second moment and Markov's inequality. -/
theorem euclideanGaussian_truncation_probability :
    3 / 4 ≤ (euclideanGaussianLaw E).real (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))) := by
  let d := Module.finrank ℝ E
  let B := closedBall (0 : E) (2 * Real.sqrt d)
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hsqrt : (Real.sqrt (d : ℝ)) ^ 2 = d := Real.sq_sqrt hd.le
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ := euclideanGaussianLaw E)
    (f := fun z : E => ‖z‖ ^ 2) (Eventually.of_forall (fun z => sq_nonneg _))
    euclideanGaussian_norm_square_integrable (4 * (d : ℝ))
  rw [euclideanGaussian_norm_second_moment] at hMarkov
  have hbad : (euclideanGaussianLaw E).real Bᶜ ≤
      (euclideanGaussianLaw E).real {z : E | 4 * (d : ℝ) ≤ ‖z‖ ^ 2} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro z hz
    have hz' : 2 * Real.sqrt (d : ℝ) < ‖z‖ := by
      simpa only [B, Set.mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz
    change 4 * (d : ℝ) ≤ ‖z‖ ^ 2
    nlinarith [norm_nonneg z, Real.sqrt_nonneg (d : ℝ)]
  have hbad' : (euclideanGaussianLaw E).real Bᶜ ≤ 1 / 4 := by
    have hm := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ 4 * (d : ℝ))
    nlinarith
  have hsum := measureReal_add_measureReal_compl (μ := euclideanGaussianLaw E)
    (show MeasurableSet B from measurableSet_closedBall)
  rw [measureReal_univ_eq_one] at hsum
  change 3 / 4 ≤ (euclideanGaussianLaw E).real B
  linarith

end
end Nonsmooth
