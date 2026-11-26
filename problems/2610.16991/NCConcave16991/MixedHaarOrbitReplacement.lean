import NCConcave16991.MixedHaarCompactFactorization
import Mathlib.MeasureTheory.Measure.Prod

/-! # Actual orbit sampling followed by an independent stabilizer completion -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {G X Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableMul₂ G]
  [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulRightInvariant μ]
  (H : Subgroup G) (ν : Measure H) [IsProbabilityMeasure ν] [Measure.IsMulLeftInvariant ν]

/-- A genuine fresh source with the actual orbit-observation law may replace
the old group element in the selector factorization. The independent
stabilizer draw then restores exactly the original static Haar marginal. -/
theorem orbit_selector_replacement_preserving
    (observe : G → X) (ho : Measurable observe) (select : X → G) (hs : Measurable select)
    (hcoset : ∀ Q, Q⁻¹ * select (observe Q) ∈ H)
    (ρ : Measure Y) [IsProbabilityMeasure ρ] (sample : Y → X) (hf : Measurable sample)
    (hlaw : ρ.map sample = μ.map observe) :
    MeasurePreserving (fun p : Y × H ↦ select (sample p.1) * p.2.val) (ρ.prod ν) μ := by
  let finish : X × H → G := fun p ↦ select p.1 * p.2.val
  have hfinish : Measurable finish :=
    (hs.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hsample : Measurable (Prod.map sample (id : H → H)) := hf.prodMap measurable_id
  have hobserve : Measurable (Prod.map observe (id : H → H)) := ho.prodMap measurable_id
  have hprod : (ρ.prod ν).map (Prod.map sample (id : H → H)) =
      (μ.prod ν).map (Prod.map observe (id : H → H)) := by
    rw [← Measure.map_prod_map ρ ν hf measurable_id,
      ← Measure.map_prod_map μ ν ho measurable_id,hlaw]
  have hbase := coset_selector_completion_preserving μ H ν
    (fun Q ↦ select (observe Q)) (hs.comp ho) hcoset
  refine ⟨(hs.comp (hf.comp measurable_fst)).mul (measurable_subtype_coe.comp measurable_snd),?_⟩
  calc
    _ = ((ρ.prod ν).map (Prod.map sample (id : H → H))).map finish := by
      simpa only [Function.comp_def,Prod.map,id_eq,finish] using
        (Measure.map_map hfinish hsample).symm
    _ = ((μ.prod ν).map (Prod.map observe (id : H → H))).map finish := by rw [hprod]
    _ = (μ.prod ν).map (fun p : G × H ↦ select (observe p.1) * p.2.val) := by
      simpa only [Function.comp_def,Prod.map,id_eq,finish] using
        (Measure.map_map hfinish hobserve)
    _ = μ := hbase.map_eq

theorem orbit_selector_replacement_pushforward
    (observe : G → X) (ho : Measurable observe) (select : X → G) (hs : Measurable select)
    (hcoset : ∀ Q, Q⁻¹ * select (observe Q) ∈ H)
    (ρ : Measure Y) [IsProbabilityMeasure ρ] (sample : Y → X) (hf : Measurable sample)
    (hlaw : ρ.map sample = μ.map observe)
    {Z : Type*} [MeasurableSpace Z] (physical : G → Z) (hp : Measurable physical) :
    (ρ.prod ν).map (fun p : Y × H ↦ physical (select (sample p.1) * p.2.val)) = μ.map physical := by
  have h := orbit_selector_replacement_preserving μ H ν observe ho select hs hcoset ρ sample hf hlaw
  have hphysical : MeasurePreserving physical μ (μ.map physical) := ⟨hp,rfl⟩
  exact (hphysical.comp h).map_eq

theorem unchanged_completion_preserving (ρ : Measure Y) [IsProbabilityMeasure ρ] :
    MeasurePreserving (Prod.snd : Y × G → G) (ρ.prod μ) μ := measurePreserving_snd

end NCConcave16991.MixedHaar
