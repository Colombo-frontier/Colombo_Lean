import NCBall.UpperProcess
import NCBall.InfiniteReplacement

/-! # Independent random segment and oracle sample pools for the upper algorithm -/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace NCBall

abbrev UpperRandomness (Ξ : Type*) := (ℕ → I) × (ℕ → Ξ)

def upperPoolLaw {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ] :
    Measure (UpperRandomness Ξ) :=
  (Measure.infinitePi (fun _ : ℕ => (volume : Measure I))).prod
    (Measure.infinitePi (fun _ : ℕ => μ))

instance upperPoolLaw_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (upperPoolLaw μ) := by
  unfold upperPoolLaw
  infer_instance

theorem upper_noise_refresh_preserves {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (t : ℕ) :
    MeasurePreserving (fun wz : UpperRandomness Ξ × Ξ => (wz.1.1, Function.update wz.1.2 t wz.2))
      ((upperPoolLaw μ).prod μ) (upperPoolLaw μ) :=
  infinite_replacement_with_seed _ μ t

theorem upper_segment_refresh_preserves {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (t : ℕ) :
    MeasurePreserving (fun wz : UpperRandomness Ξ × I => (Function.update wz.1.1 t wz.2, wz.1.2))
      ((upperPoolLaw μ).prod volume) (upperPoolLaw μ) := by
  let νr := Measure.infinitePi (fun _ : ℕ => (volume : Measure I))
  let νξ := Measure.infinitePi (fun _ : ℕ => μ)
  have h1 := (Measure.measurePreserving_swap (μ := νr) (ν := νξ)).prod (MeasurePreserving.id (volume : Measure I))
  have h2 := infinite_replacement_with_seed νξ (volume : Measure I) t
  have h3 := Measure.measurePreserving_swap (μ := νξ) (ν := νr)
  exact h3.comp (h2.comp h1)

end NCBall
