import Nonsmooth.AdaptiveResponse

open MeasureTheory Function Filter
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def appendOutputQuery (q : ℕ → E → E) (W : E → E) (T : ℕ) (n : ℕ) : E → E :=
  if n < T then q n else W

theorem appendOutputQuery_information (q : ℕ → E → E) (W : E → E) (T : ℕ) :
    ∀ n ≤ T, adaptiveLinearInformation (appendOutputQuery q W T) n = adaptiveLinearInformation q n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n < T := by omega
    simp only [adaptiveLinearInformation, ih (by omega), appendOutputQuery, if_pos hn']

theorem spherical_adaptive_output_square (q : ℕ → E → E) (W : E → E) (T : ℕ)
    (hT : T + 1 ≤ Module.finrank ℝ E)
    (hq : ∀ n < T, @Measurable E E (adaptiveLinearInformation q n) mE (q n))
    (hW : @Measurable E E (adaptiveLinearInformation q T) mE W)
    (hWb : ∀ᵐ x ∂sphericalLaw E, ‖W x‖ ≤ 1) :
    (∫ x : E, ⟪W x, x⟫_ℝ ^ 2 ∂sphericalLaw E) ≤
      ((T : ℝ) + 1) / (Module.finrank ℝ E : ℝ) := by
  have hqa : ∀ n < T + 1, @Measurable E E
      (adaptiveLinearInformation (appendOutputQuery q W T) n) mE (appendOutputQuery q W T n) := by
    intro n hn
    rw [appendOutputQuery_information q W T n (by omega)]
    by_cases hnt : n < T
    · simpa only [appendOutputQuery, if_pos hnt] using hq n hnt
    · have hnT : n = T := by omega
      subst n
      simpa only [appendOutputQuery, lt_self_iff_false, if_false] using hW
  have hb : ∀ᵐ x ∂sphericalLaw E, ‖appendOutputQuery q W T T x‖ ≤ 1 := by
    simpa only [appendOutputQuery, lt_self_iff_false, if_false] using hWb
  simpa only [appendOutputQuery, lt_self_iff_false, if_false, Nat.cast_add, Nat.cast_one] using
    spherical_adaptive_response_square (appendOutputQuery q W T) (T + 1) hT hqa (Nat.lt_succ_self T) hb

theorem spherical_adaptive_output_negative_tail (q : ℕ → E → E) (W : E → E) (T : ℕ)
    (hT : T + 1 ≤ Module.finrank ℝ E)
    (hq : ∀ n < T, @Measurable E E (adaptiveLinearInformation q n) mE (q n))
    (hW : @Measurable E E (adaptiveLinearInformation q T) mE W)
    (hWb : ∀ᵐ x ∂sphericalLaw E, ‖W x‖ ≤ 1) :
    (sphericalLaw E).real {x : E | ⟪W x, x⟫_ℝ < -1 / 2} ≤
      4 * ((T : ℝ) + 1) / (Module.finrank ℝ E : ℝ) := by
  have hm := hW.mono (adaptiveLinearInformation_le q T hq) le_rfl
  have hi : Integrable (fun x : E => ⟪W x, x⟫_ℝ ^ 2) (sphericalLaw E) := by
    apply (MemLp.of_bound ((continuous_fst.inner continuous_snd).measurable.comp
      (hm.prodMk measurable_id)).aestronglyMeasurable 1 _).integrable_sq
    filter_upwards [hWb, sphericalLaw_unit (E := E)] with x hx hu
    change ‖⟪W x, x⟫_ℝ‖ ≤ 1
    exact (norm_inner_le_norm _ _).trans (by simpa only [hu, mul_one] using hx)
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := sphericalLaw E)
    (f := fun x : E => ⟪W x, x⟫_ℝ ^ 2) (Eventually.of_forall (fun x => sq_nonneg _)) hi (1 / 4)
  have hsub : (sphericalLaw E).real {x : E | ⟪W x, x⟫_ℝ < -1 / 2} ≤
      (sphericalLaw E).real {x : E | 1 / 4 ≤ ⟪W x, x⟫_ℝ ^ 2} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro x hx
    change 1 / 4 ≤ ⟪W x, x⟫_ℝ ^ 2
    nlinarith [show ⟪W x, x⟫_ℝ < -1 / 2 from hx]
  have he := spherical_adaptive_output_square q W T hT hq hW hWb
  have hmul := mul_le_mul_of_nonneg_left hsub (by norm_num : (0 : ℝ) ≤ 1 / 4)
  calc
    _ ≤ 4 * (((T : ℝ) + 1) / (Module.finrank ℝ E : ℝ)) := by linarith
    _ = _ := by ring

end
end Nonsmooth
