import Nonsmooth.GaussianConcentration
import Nonsmooth.GaussianPriorIdentity

open MeasureTheory ProbabilityTheory Metric Filter Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem truncatedGaussianLaw_real (s : Set E) :
    (truncatedGaussianLaw E).real s =
      (euclideanGaussianLaw E).real (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E)) ∩ s) /
        (euclideanGaussianLaw E).real (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))) := by
  simp only [measureReal_def, truncatedGaussianLaw_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

theorem truncatedGaussianLaw_amplification (s : Set E) :
    (truncatedGaussianLaw E).real s ≤ (4 / 3) * (euclideanGaussianLaw E).real s := by
  rw [truncatedGaussianLaw_real]
  have hB := euclideanGaussian_truncation_probability (E := E)
  have hp : 0 < (euclideanGaussianLaw E).real
      (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))) := by linarith
  apply (div_le_iff₀ hp).mpr
  have hs := measureReal_mono (μ := euclideanGaussianLaw E)
    (Set.inter_subset_right : closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E)) ∩ s ⊆ s)
    (measure_ne_top _ _)
  have hm := mul_le_mul_of_nonneg_right hB (measureReal_nonneg (μ := euclideanGaussianLaw E) (s := s))
  nlinarith

theorem truncatedGaussianLaw_norm_square_lower_tail :
    (truncatedGaussianLaw E).real {z : E | ‖z‖ ^ 2 < (Module.finrank ℝ E : ℝ) / 2} ≤
      32 / (3 * (Module.finrank ℝ E : ℝ)) := by
  have h := (truncatedGaussianLaw_amplification (E := E)
    {z : E | ‖z‖ ^ 2 < (Module.finrank ℝ E : ℝ) / 2}).trans
    (mul_le_mul_of_nonneg_left euclideanGaussian_norm_square_lower_tail (by norm_num : (0 : ℝ) ≤ 4 / 3))
  convert h using 1 <;> first | rfl | ring

theorem truncatedGaussianVectorLaw_map :
    Measure.map (Subtype.val : Feasible E (2 * Real.sqrt (Module.finrank ℝ E)) → E)
      (truncatedGaussianVectorLaw E) = truncatedGaussianLaw E := by
  rw [truncatedGaussianVectorLaw]
  erw [map_comap_subtype_coe (isClosed_le continuous_norm continuous_const).measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem truncatedGaussianLaw_supported

theorem gaussianSupportRowLaw_map :
    Measure.map (Subtype.val : Feasible E 2 → E) (gaussianSupportRowLaw E) =
      Measure.map (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) (truncatedGaussianLaw E) := by
  rw [gaussianSupportRowLaw, Measure.map_map measurable_subtype_coe gaussianScaleRow_measurable]
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  rw [← truncatedGaussianVectorLaw_map, Measure.map_map hm measurable_subtype_coe]
  rfl

theorem gaussianSupportRowLaw_norm_small :
    (gaussianSupportRowLaw E).real {a : Feasible E 2 | ‖a.val‖ < 1 / 2} ≤
      32 / (3 * (Module.finrank ℝ E : ℝ)) := by
  have hs : MeasurableSet {a : E | ‖a‖ < 1 / 2} := isOpen_lt continuous_norm continuous_const |>.measurableSet
  have hmap := congrArg (fun μ : Measure E => μ.real {a : E | ‖a‖ < 1 / 2})
    (gaussianSupportRowLaw_map (E := E))
  have hm : Measurable (fun z : E => (Real.sqrt (Module.finrank ℝ E))⁻¹ • z) :=
    measurable_const.smul measurable_id
  rw [map_measureReal_apply measurable_subtype_coe hs,
    map_measureReal_apply hm hs] at hmap
  simp only [Set.preimage_setOf_eq] at hmap
  rw [hmap]
  apply le_trans (measureReal_mono (μ := truncatedGaussianLaw E) _ (measure_ne_top _ _))
    truncatedGaussianLaw_norm_square_lower_tail
  intro z hz
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hp : 0 < Real.sqrt (Module.finrank ℝ E : ℝ) := Real.sqrt_pos.mpr hd
  have hz' : ‖z‖ / Real.sqrt (Module.finrank ℝ E : ℝ) < 1 / 2 := by
    simpa only [Set.mem_preimage, Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hp, div_eq_inv_mul] using hz
  have hz'' := (div_lt_iff₀ hp).mp hz'
  change ‖z‖ ^ 2 < (Module.finrank ℝ E : ℝ) / 2
  nlinarith [norm_nonneg z, Real.sq_sqrt hd.le]

theorem gaussianSupportRowLaw_norm_large (hd : 86 ≤ Module.finrank ℝ E) :
    7 / 8 ≤ (gaussianSupportRowLaw E).real {a : Feasible E 2 | 1 / 2 ≤ ‖a.val‖} := by
  have hd' : (86 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hd
  have hp : 0 < 3 * (Module.finrank ℝ E : ℝ) := by positivity
  have hb : (gaussianSupportRowLaw E).real {a : Feasible E 2 | ‖a.val‖ < 1 / 2} ≤ 1 / 8 :=
    gaussianSupportRowLaw_norm_small.trans ((div_le_iff₀ hp).mpr (by linarith))
  have hs := measureReal_add_measureReal_compl (μ := gaussianSupportRowLaw E)
    (show MeasurableSet {a : Feasible E 2 | ‖a.val‖ < 1 / 2} from
      (isOpen_lt continuous_subtype_val.norm continuous_const).measurableSet)
  rw [probReal_univ] at hs
  have he : {a : Feasible E 2 | ‖a.val‖ < 1 / 2}ᶜ = {a : Feasible E 2 | 1 / 2 ≤ ‖a.val‖} := by
    ext a; simp
  rw [he] at hs
  linarith

end
end Nonsmooth
