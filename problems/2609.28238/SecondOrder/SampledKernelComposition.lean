import SecondOrder.SampledResponseKernel
import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory ProbabilityTheory

namespace SecondOrder
noncomputable section

variable {A B X Y : Type} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace X] [MeasurableSpace Y]

theorem map_bind_sampledResponse (α : Measure A) (β : Measure B) [SFinite α] [SFinite β]
    (g : A → X) (hg : Measurable g) (step : X → B → Y)
    (hs : Measurable (fun w : X × B => step w.1 w.2)) :
    (Measure.map g α).bind (sampledResponseKernel β step hs)=
      Measure.map (fun w : A × B => step (g w.1) w.2) (α.prod β) := by
  let K := sampledResponseKernel β step hs
  have hm : Measurable (fun w : A × B => step (g w.1) w.2) :=
    hs.comp ((hg.comp measurable_fst).prodMk measurable_snd)
  ext e he
  rw [Measure.bind_apply he K.measurable.aemeasurable,
    lintegral_map (K.measurable_coe he) hg,Measure.map_apply hm he,
    Measure.prod_apply (hm he)]
  apply lintegral_congr
  intro a
  have ha : Measurable (step (g a)) := hs.comp (measurable_const.prodMk measurable_id)
  rw [sampledResponseKernel_apply,Measure.map_apply ha he]
  rfl

end
end SecondOrder
