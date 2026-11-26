import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Measure.Prod

/-! A measurable sampler driven by fresh independent noise defines an actual
Markov kernel, whose composition-product is the sampler's joint pushforward. -/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace HeavyTail
noncomputable section

variable {Ω N R : Type*} [MeasurableSpace Ω] [MeasurableSpace N] [MeasurableSpace R]

def kernelOfSampler (ν : Measure N) [SFinite ν] (F : Ω × N → R) (hF : Measurable F) :
    Kernel Ω R where
  toFun ω := ν.map (fun z ↦ F (ω, z))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have he (ω : Ω) : (ν.map (fun z ↦ F (ω, z))) s =
        ν (Prod.mk ω ⁻¹' (F ⁻¹' s)) := by
      have hslice : Measurable (fun z : N ↦ F (ω, z)) := hF.comp measurable_prodMk_left
      rw [Measure.map_apply hslice hs]
      rfl
    simp_rw [he]
    exact measurable_measure_prodMk_left (hF hs)

@[simp] theorem kernelOfSampler_apply (ν : Measure N) [SFinite ν]
    (F : Ω × N → R) (hF : Measurable F) (ω : Ω) :
    kernelOfSampler ν F hF ω = ν.map (fun z ↦ F (ω, z)) := rfl

instance kernelOfSampler_isMarkov (ν : Measure N) [IsProbabilityMeasure ν]
    (F : Ω × N → R) (hF : Measurable F) : IsMarkovKernel (kernelOfSampler ν F hF) := by
  constructor
  intro ω
  rw [kernelOfSampler_apply]
  exact isProbabilityMeasure_map (hF.comp measurable_prodMk_left).aemeasurable

theorem compProd_kernelOfSampler (P : Measure Ω) [SFinite P]
    (ν : Measure N) [IsProbabilityMeasure ν] (F : Ω × N → R) (hF : Measurable F) :
    P.compProd (kernelOfSampler ν F hF) =
      (P.prod ν).map (fun ω ↦ (ω.1, F ω)) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (measurable_fst.prodMk hF) hs,
    Measure.prod_apply ((measurable_fst.prodMk hF) hs)]
  apply lintegral_congr
  intro ω
  have hslice : Measurable (fun z : N ↦ F (ω, z)) := hF.comp measurable_prodMk_left
  rw [kernelOfSampler_apply, Measure.map_apply hslice
    (measurable_prodMk_left hs)]
  rfl

theorem kernelOfSampler_comap {Ξ : Type*} [MeasurableSpace Ξ]
    (ν : Measure N) [SFinite ν] (F : Ω × N → R) (hF : Measurable F)
    (g : Ξ → Ω) (hg : Measurable g) :
    (kernelOfSampler ν F hF).comap g hg =
      kernelOfSampler ν (fun ω : Ξ × N ↦ F (g ω.1, ω.2))
        (hF.comp ((hg.comp measurable_fst).prodMk measurable_snd)) := by
  ext ω s hs
  rfl

end
end HeavyTail
