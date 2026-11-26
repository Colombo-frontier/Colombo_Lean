import LowRank.SchattenSuccessEvent

/-! A product-distribution success bound yields a fixed input on which the
randomized algorithm has low success probability. -/

namespace LowRank
open MeasureTheory
noncomputable section

theorem exists_small_section_of_prod_bound {S X : Type*}
    [MeasurableSpace S] [MeasurableSpace X]
    (ν : Measure S) (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {E : Set (S × X)} (hE : MeasurableSet E) {a b : ℝ}
    (hb : 0 ≤ b) (hab : a < b) (hbound : (ν.prod μ).real E ≤ a) :
    ∃ x : X, ν.real {s | (s, x) ∈ E} < b := by
  classical
  by_contra! hn
  have hsection (x : X) : ENNReal.ofReal b ≤ ν {s | (s, x) ∈ E} := by
    have h := ENNReal.ofReal_le_ofReal (hn x)
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  have hprod : ENNReal.ofReal b ≤ (ν.prod μ) E := by
    rw [Measure.prod_apply_symm hE]
    calc
      _ = ∫⁻ _ : X, ENNReal.ofReal b ∂μ := by simp
      _ ≤ _ := lintegral_mono (fun x => hsection x)
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hprod
  rw [ENNReal.toReal_ofReal hb] at hreal
  exact (not_le_of_gt hab) (hreal.trans hbound)

end
end LowRank
