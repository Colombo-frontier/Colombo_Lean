import Nonsmooth.StrongPotentialTilts

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α : Type} [MeasurableSpace α]

def weightedDensityLaw (μ : Measure α) (w : α → ℝ) : Measure α :=
  (μ.withDensity (fun x => ENNReal.ofReal (w x)))[|univ]

instance weightedDensityLaw_finite (μ : Measure α) (w : α → ℝ) :
    IsFiniteMeasure (weightedDensityLaw μ w) := by
  unfold weightedDensityLaw
  infer_instance

theorem weightedDensityMeasure_mass (μ : Measure α) (w : α → ℝ)
    (hw : Integrable w μ) (hw0 : ∀ x, 0 ≤ w x) :
    (μ.withDensity (fun x => ENNReal.ofReal (w x))) univ = ENNReal.ofReal (∫ x, w x ∂μ) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall hw0)]

theorem weightedDensityLaw_probability (μ : Measure α) (w : α → ℝ)
    (hw : Integrable w μ) (hw0 : ∀ x, 0 ≤ w x) (hZ : 0 < ∫ x, w x ∂μ) :
    IsProbabilityMeasure (weightedDensityLaw μ w) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [weightedDensityMeasure_mass μ w hw hw0]
    exact (ENNReal.ofReal_pos.mpr hZ).ne'
  · rw [weightedDensityMeasure_mass μ w hw hw0]
    exact ENNReal.ofReal_ne_top

theorem weightedDensityLaw_integral {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure α) (w : α → ℝ) (hwm : Measurable w)
    (hw : Integrable w μ) (hw0 : ∀ x, 0 ≤ w x) (f : α → F) :
    (∫ x, f x ∂weightedDensityLaw μ w) = (∫ x, w x ∂μ)⁻¹ • ∫ x, w x • f x ∂μ := by
  rw [weightedDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ, integral_smul_measure,
    weightedDensityMeasure_mass μ w hw hw0, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (integral_nonneg hw0),
    integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw0 _)]

theorem weightedDensityLaw_indicator (μ : Measure α) (A : Set α) (hA : MeasurableSet A) :
    weightedDensityLaw μ (A.indicator (fun _ => (1 : ℝ))) = μ[|A] := by
  have hw : (fun x => ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) x)) =
      A.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [weightedDensityLaw, hw]
  change (μ.withDensity (A.indicator (1 : α → ℝ≥0∞)))[|univ] = _
  rw [withDensity_indicator_one hA]
  simp only [ProbabilityTheory.cond, Measure.restrict_apply_univ, Measure.restrict_univ]

theorem weightedDensityLaw_absolutelyContinuous (μ : Measure α) (w : α → ℝ) :
    weightedDensityLaw μ w ≪ μ :=
  cond_absolutelyContinuous.trans (withDensity_absolutelyContinuous μ _)

theorem absolutelyContinuous_weightedDensityLaw (μ : Measure α) (w : α → ℝ)
    (hwm : Measurable w) (hw : Integrable w μ) (hw0 : ∀ x, 0 ≤ w x)
    (hp : ∀ᵐ x ∂μ, 0 < w x) : μ ≪ weightedDensityLaw μ w := by
  letI : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (w x))) :=
    ⟨by rw [weightedDensityMeasure_mass μ w hw hw0]; exact ENNReal.ofReal_lt_top⟩
  exact (withDensity_absolutelyContinuous' hwm.ennreal_ofReal.aemeasurable
    (hp.mono (fun x hx => (ENNReal.ofReal_pos.mpr hx).ne'))).trans (absolutelyContinuous_cond_univ)

theorem unit_weight_integrable (μ : Measure α) [IsFiniteMeasure μ] (w : α → ℝ)
    (hwm : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) : Integrable w μ :=
  (integrable_const (1 : ℝ)).mono' hwm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_of_nonneg (hw x).1] using (hw x).2))

theorem weightedDensityLaw_probability_of_positive (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ) (hwm : Measurable w) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (hp : ∀ᵐ x ∂μ, 0 < w x) : IsProbabilityMeasure (weightedDensityLaw μ w) := by
  have hi := unit_weight_integrable μ w hwm hw
  apply weightedDensityLaw_probability μ w hi (fun x => (hw x).1)
  have hz : (∫ x, w x ∂μ) ≠ 0 := by
    intro hz
    have he := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun x => (hw x).1)) hi).mp hz
    obtain ⟨x, hx, hxpos⟩ := (he.and hp).exists
    simp only [Pi.zero_apply] at hx
    linarith
  exact lt_of_le_of_ne (integral_nonneg (fun x => (hw x).1)) hz.symm

end
end Nonsmooth
