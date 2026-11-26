import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory

namespace SecondOrder
noncomputable section
variable {X A Y : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Y]

/-- A jointly measurable response to randomness sampled from one fixed law
defines a genuine measurable probability kernel. -/
def sampledResponseKernel (μ : Measure A) [SFinite μ] (f : X → A → Y)
    (hf : Measurable (fun w : X × A => f w.1 w.2)) : Kernel X Y where
  toFun x := μ.map (f x)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hm (x : X) : Measurable (f x) := hf.comp measurable_prodMk_left
    simp_rw [Measure.map_apply (hm _) hs]
    exact measurable_measure_prodMk_left (hf hs)

@[simp] theorem sampledResponseKernel_apply (μ : Measure A) [SFinite μ] (f : X → A → Y)
    (hf : Measurable (fun w : X × A => f w.1 w.2)) (x : X) :
    sampledResponseKernel μ f hf x = μ.map (f x) := rfl

instance sampledResponseKernel_markov (μ : Measure A) [IsProbabilityMeasure μ] (f : X → A → Y)
    (hf : Measurable (fun w : X × A => f w.1 w.2)) :
    IsMarkovKernel (sampledResponseKernel μ f hf) where
  isProbabilityMeasure x := isProbabilityMeasure_map (hf.comp measurable_prodMk_left).aemeasurable

end
end SecondOrder
