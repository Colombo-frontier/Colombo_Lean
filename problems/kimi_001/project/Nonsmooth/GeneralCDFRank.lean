import Nonsmooth.ContinuousRank

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A CDF evaluated at its own random variable has a lower tail bounded by
the uniform law, without an atomlessness hypothesis. -/
theorem cdf_rank_probability_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) : μ.real {x : ℝ | cdf μ x ≤ t} ≤ t := by
  by_cases ht1 : 1 ≤ t
  · exact measureReal_le_one.trans ht1
  have ht1' : t < 1 := lt_of_not_ge ht1
  let A := {x : ℝ | cdf μ x ≤ t}
  by_cases hA : A.Nonempty
  · obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt ht1').exists
    have hB : BddAbove A := by
      refine ⟨b, ?_⟩
      intro z hz
      by_contra h
      have hm := (monotone_cdf μ) (le_of_lt (lt_of_not_ge h))
      change cdf μ z ≤ t at hz
      linarith
    let a := sSup A
    by_cases ha : a ∈ A
    · have hs : A ⊆ Iic a := fun z hz => le_csSup hB hz
      exact (measureReal_mono hs).trans ((cdf_eq_real μ a).symm.trans_le ha)
    · have hs : A ⊆ Iio a := by
        intro z hz
        apply lt_of_le_of_ne (le_csSup hB hz)
        intro he
        apply ha
        change sSup A ∈ A
        exact he ▸ hz
      have hl : Function.leftLim (cdf μ) a ≤ t := by
        rw [(monotone_cdf μ).leftLim_eq_sSup]
        apply csSup_le (Set.Nonempty.image _ (show (Iio a).Nonempty from ⟨a - 1, by simp⟩))
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨z, hz, hxz⟩ := exists_lt_of_lt_csSup hA hx
        exact ((monotone_cdf μ) hxz.le).trans hz
      have hl0 : 0 ≤ Function.leftLim (cdf μ) a :=
        (cdf_nonneg μ (a - 1)).trans ((monotone_cdf μ).le_leftLim (by linarith : a - 1 < a))
      have hm : μ.real (Iio a) = Function.leftLim (cdf μ) a := by
        have hm' : μ (Iio a) = ENNReal.ofReal (Function.leftLim (cdf μ) a) := by
          simpa only [measure_cdf, sub_zero] using (cdf μ).measure_Iio (tendsto_cdf_atBot μ) a
        rw [measureReal_def, hm', ENNReal.toReal_ofReal hl0]
      exact (measureReal_mono hs).trans (hm.trans_le hl)
  · have he : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    change μ.real A ≤ t
    rw [he]
    simpa using ht

theorem cdf_positive_ae (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ᵐ y ∂μ, 0 < cdf μ y := by
  have h := cdf_rank_probability_le μ (le_refl (0 : ℝ))
  have hz : μ {y : ℝ | cdf μ y ≤ 0} = 0 := by
    have hr : (μ {y : ℝ | cdf μ y ≤ 0}).toReal = 0 := le_antisymm h ENNReal.toReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff _).mp hr).resolve_right (measure_ne_top _ _)
  rw [ae_iff]
  simpa only [not_lt] using hz

end
end Nonsmooth
