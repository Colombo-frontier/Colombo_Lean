import SecondOrder.ContinuousBatch

open MeasureTheory

namespace SecondOrder
noncomputable section

/-- Insert a sample before an entire recursive sample history. -/
def prependDraw {Ω : Type*} : (N : ℕ) → Ω × Draws Ω N → Draws Ω (N+1)
  | 0, w => (w.2,w.1)
  | N+1, w => (prependDraw N (w.1,w.2.1),w.2.2)

def reverseDraws {Ω : Type*} : (N : ℕ) → Draws Ω N → Draws Ω N
  | 0, w => w
  | N+1, w => prependDraw N (w.2,reverseDraws N w.1)

theorem prependDraw_measurable {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) :
    Measurable (@prependDraw Ω N) := by
  induction N with
  | zero => exact measurable_swap
  | succ N ih =>
    exact (ih.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd

theorem reverseDraws_measurable {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) :
    Measurable (@reverseDraws Ω N) := by
  induction N with
  | zero => exact measurable_id
  | succ N ih =>
    exact (prependDraw_measurable N).comp (measurable_snd.prodMk (ih.comp measurable_fst))

theorem prependDraw_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) :
    MeasurePreserving (@prependDraw Ω N) (μ.prod (drawsLaw μ N)) (drawsLaw μ (N+1)) := by
  induction N with
  | zero => exact Measure.measurePreserving_swap
  | succ N ih =>
    have ha := (measurePreserving_prodAssoc μ (drawsLaw μ N) μ).symm
    exact (ih.prod (MeasurePreserving.id μ)).comp ha

/-- Reversing independent, identically distributed samples preserves their
full joint law, not just each sample's marginal law. -/
theorem reverseDraws_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) :
    MeasurePreserving (@reverseDraws Ω N) (drawsLaw μ N) (drawsLaw μ N) := by
  induction N with
  | zero => exact MeasurePreserving.id _
  | succ N ih =>
    exact (prependDraw_measurePreserving μ N).comp
      (Measure.measurePreserving_swap.comp (ih.prod (MeasurePreserving.id μ)))

end
end SecondOrder
