import RandomizedFO2003.CoordinateRefresh

namespace RandomizedFO2003

open MeasureTheory

variable {I X Y Z : Type*} [Fintype I] [DecidableEq I]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem pi_pair_refresh_preserving (σ : Measure X) (τ : Measure Y)
    [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] (i : I) :
    MeasurePreserving (fun p : (X × ((I → X) × (I → Y))) × Y =>
      (Function.update p.1.2.1 i p.1.1, Function.update p.1.2.2 i p.2))
      ((σ.prod ((Measure.pi (fun _ : I => σ)).prod (Measure.pi (fun _ : I => τ)))).prod τ)
      ((Measure.pi (fun _ : I => σ)).prod (Measure.pi (fun _ : I => τ))) := by
  let μx := Measure.pi (fun _ : I => σ)
  let μy := Measure.pi (fun _ : I => τ)
  have h1 := (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc σ μx μy)).prod (MeasurePreserving.id τ)
  have h2 := (measurePreserving_prodAssoc (σ.prod μx) μy τ).comp h1
  have h3 := ((MeasurePreserving.id (σ.prod μx)).prod
    (Measure.measurePreserving_swap (μ := μy) (ν := τ))).comp h2
  exact ((pi_refresh_preserving σ i).prod (pi_refresh_preserving τ i)).comp h3

/-- Refresh a sphere coordinate and its rotation independently, while
carrying the original private seed. The full original law is preserved. -/
theorem pi_pair_refresh_seed_preserving (σ : Measure X) (τ : Measure Y) (ν : Measure Z)
    [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] [IsProbabilityMeasure ν] (i : I) :
    MeasurePreserving (fun p : (X × (((I → X) × (I → Y)) × Z)) × Y =>
      ((Function.update p.1.2.1.1 i p.1.1, Function.update p.1.2.1.2 i p.2), p.1.2.2))
      ((σ.prod (((Measure.pi (fun _ : I => σ)).prod (Measure.pi (fun _ : I => τ))).prod ν)).prod τ)
      (((Measure.pi (fun _ : I => σ)).prod (Measure.pi (fun _ : I => τ))).prod ν) := by
  let μ := (Measure.pi (fun _ : I => σ)).prod (Measure.pi (fun _ : I => τ))
  have h1 := (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc σ μ ν)).prod (MeasurePreserving.id τ)
  have h2 := (measurePreserving_prodAssoc (σ.prod μ) ν τ).comp h1
  have h3 := ((MeasurePreserving.id (σ.prod μ)).prod
    (Measure.measurePreserving_swap (μ := ν) (ν := τ))).comp h2
  have h4 := (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (σ.prod μ) τ ν)).comp h3
  exact ((pi_pair_refresh_preserving σ τ i).prod (MeasurePreserving.id ν)).comp h4

end RandomizedFO2003
