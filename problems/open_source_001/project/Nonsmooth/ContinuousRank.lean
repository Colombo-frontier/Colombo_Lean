import Nonsmooth.GaussianWinnerMean
import Mathlib.Probability.CDF

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem continuous_cdf_of_atomless (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf μ).rightLim_eq]
  have h := (cdf μ).measure_singleton x
  rw [measure_cdf, hμ x] at h
  have hle := ENNReal.ofReal_eq_zero.mp h.symm
  have hleft : Function.leftLim (cdf μ) x ≤ cdf μ x := (cdf μ).mono.leftLim_le le_rfl
  linarith

theorem continuous_cdf_range (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ x : ℝ, cdf μ x = t := by
  apply mem_range_of_exists_le_of_exists_ge hc
  · exact ((tendsto_cdf_atBot μ).eventually_le_const ht0).exists
  · exact ((tendsto_cdf_atTop μ).eventually_const_le ht1).exists

theorem continuous_cdf_rank_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    μ.real {x : ℝ | cdf μ x ≤ t} = t := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    by_cases hlarge : 1 ≤ t + ε
    · exact measureReal_le_one.trans hlarge
    · obtain ⟨x, hx⟩ := continuous_cdf_range μ hc (by linarith : 0 < t + ε) (lt_of_not_ge hlarge)
      have hsub : {z : ℝ | cdf μ z ≤ t} ⊆ Iic x := by
        intro z hz
        change z ≤ x
        apply le_of_not_gt
        intro hlt
        have hm := (monotone_cdf μ) hlt.le
        change cdf μ z ≤ t at hz
        rw [hx] at hm
        linarith
      have h := measureReal_mono (μ := μ) hsub
      rw [← cdf_eq_real, hx] at h
      exact h
  · by_cases hz : t = 0
    · rw [hz]
      exact measureReal_nonneg
    · by_cases ho : t = 1
      · have hs : {x : ℝ | cdf μ x ≤ t} = Set.univ := by
          ext x
          simp only [mem_setOf_eq, mem_univ, iff_true, ho]
          exact cdf_le_one μ x
        rw [hs]
        simp only [measureReal_def, measure_univ, ENNReal.toReal_one, ho, le_refl]
      · obtain ⟨x, hx⟩ := continuous_cdf_range μ hc (lt_of_le_of_ne ht0 (Ne.symm hz))
          (lt_of_le_of_ne ht1 ho)
        have hsub : Iic x ⊆ {z : ℝ | cdf μ z ≤ t} := by
          intro z hz
          exact ((monotone_cdf μ) hz).trans_eq hx
        have h := measureReal_mono (μ := μ) hsub
        rw [← cdf_eq_real, hx] at h
        exact h

/-- Probability integral transform for every atomless real probability law, including laws
whose CDF has flat intervals. The resulting measure is the actual unit-interval Lebesgue law. -/
theorem atomless_cdf_map_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) :
    μ.map (cdf μ) = (volume : Measure ℝ).restrict (Ioc 0 1) := by
  have hc := continuous_cdf_of_atomless μ hμ
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  have hν : ν Set.univ = 1 := by simp [ν, Real.volume_Ioc]
  letI : IsProbabilityMeasure ν := ⟨hν⟩
  change μ.map (cdf μ) = ν
  apply Measure.ext_of_Iic _ _
  intro t
  rw [Measure.map_apply hc.measurable measurableSet_Iic]
  by_cases ht0 : t < 0
  · have he : (cdf μ) ⁻¹' Iic t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_le_of_gt ht0) ((cdf_nonneg μ x).trans hx)
    have hi : Iic t ∩ Ioc (0 : ℝ) 1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hx0, hx1⟩
      exact (not_lt_of_ge hx) (ht0.trans hx0)
    rw [he, measure_empty]
    simp only [ν, Measure.restrict_apply measurableSet_Iic, hi, measure_empty]
  · by_cases ht1 : t ≤ 1
    · have he : Iic t ∩ Ioc (0 : ℝ) 1 = Ioc 0 t := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨hx, hx0, hx1⟩
          exact ⟨hx0, hx⟩
        · rintro ⟨hx0, hx⟩
          exact ⟨hx, hx0, hx.trans ht1⟩
      have h := continuous_cdf_rank_probability μ hc (le_of_not_gt ht0) ht1
      change (μ ((cdf μ) ⁻¹' Iic t)).toReal = t at h
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), h]
      simp only [ν, Measure.restrict_apply measurableSet_Iic, he, Real.volume_Ioc, sub_zero]
    · have he : (cdf μ) ⁻¹' Iic t = Set.univ := by
        ext x
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (cdf_le_one μ x).trans (le_of_lt (lt_of_not_ge ht1))
      have hi : Iic t ∩ Ioc (0 : ℝ) 1 = Ioc 0 1 := by
        apply inter_eq_right.mpr
        intro x hx
        exact hx.2.trans (le_of_lt (lt_of_not_ge ht1))
      rw [he, measure_univ]
      simp only [ν, Measure.restrict_apply measurableSet_Iic, hi, Real.volume_Ioc]
      norm_num

theorem map_withDensity_composed {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (F : α → β) (hF : Measurable F) (w : β → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (fun x => w (F x))).map F = (μ.map F).withDensity w := by
  ext A hA
  rw [Measure.map_apply hF hA, withDensity_apply _ (hF hA), withDensity_apply _ hA,
    Measure.restrict_map hF hA, lintegral_map hw hF]

theorem atomless_cdf_weighted_map (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ {x} = 0) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (fun x => w (cdf μ x))).map (cdf μ) =
      ((volume : Measure ℝ).restrict (Ioc 0 1)).withDensity w := by
  rw [map_withDensity_composed μ _ (continuous_cdf_of_atomless μ hμ).measurable w hw,
    atomless_cdf_map_uniform μ hμ]

end
end Nonsmooth
