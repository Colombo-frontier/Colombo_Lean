import RandomizedFO2003.PaddedHistoryLaw
import RandomizedFO2003.AmbientPairHistory

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A finite simulation using exactly two fresh ambient vectors per exposure.
The auxiliary response vector is retained when projecting the second vector. -/
noncomputable def ActionProgram.paddedAmbientSample (d : ℕ) : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → ActionProgram E n H →
    (Ω → ExposureFrame (Coordinates (d + n)) E) → (Ω → H) →
      AmbientPairHistory E n Ω → PaddedHistory E d n Ω
  | 0, _, _, _, _, _, _, _ => id
  | n + 1, _, _, _, _, plan, F, history =>
    paddedAmbientSample d n plan.2 (paddedFrameNext plan.1.kind F (plan.1.vector ∘ history))
      (paddedObservedHistory plan.1 F history) ∘
        AmbientPairHistory.map E n (ambientDirectionStep plan.1.kind (fun p => F p.1))

/-- All ambient inputs have one fixed independent product law; the adaptive
coordinate changes recover the full padded exposure law. -/
theorem ActionProgram.paddedAmbientSample_preserving (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (plan : ActionProgram E n H) (F : Ω → ExposureFrame (Coordinates (d + n)) E)
    (hF : ExposureFrame.MeasurableFamily F) (history : Ω → H) (hh : Measurable history) :
    MeasurePreserving (plan.paddedAmbientSample d n F history)
      (ambientPairHistoryLaw E n μ) (paddedHistoryLaw E d n μ) := by
  induction n generalizing H Ω with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    let μa := μ.prod (Spherical.sphereLaw E)
    haveI : SFinite μa := Measure.prod.instSFinite
    haveI : SFinite (μa.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    haveI : SFinite (μa.prod (Spherical.sphereLaw (Coordinates (d + n + 1)))) := Measure.prod.instSFinite
    have hstep := ambientDirectionStep_preserving μa plan.1.kind
      (fun p : Ω × E => F p.1) (hF.comp measurable_fst)
    exact (ih (μa.prod (Spherical.sphereLaw (Coordinates (d + n + 1)))) plan.2 _
      (measurable_paddedFrameNext plan.1.kind F hF _ (plan.1.measurable_vector.comp hh))
      _ (measurable_paddedObservedHistory plan.1 F hF history hh)).comp
        (AmbientPairHistory.map_preserving n _ _ _ hstep)

noncomputable def ActionProgram.paddedAmbientTranscript (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (history : Ω → H) :
    AmbientPairHistory E n Ω → ActionHistory E n H :=
  plan.paddedHistoryMap d n F history ∘ plan.paddedAmbientSample d n F history

theorem ActionProgram.paddedAmbientTranscript_measurable (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (hF : ExposureFrame.MeasurableFamily F)
    (history : Ω → H) (hh : Measurable history) : Measurable (plan.paddedAmbientTranscript d n F history) :=
  (plan.paddedHistoryMap_measurable d n F hF history hh).comp
    (plan.paddedAmbientSample_preserving d n (0 : Measure Ω) F hF history hh).measurable

/-- The true adaptive transcript has the same law as this independent ambient
simulation, with the degenerate response branch repaired at every round. -/
theorem ActionProgram.paddedAmbientTranscript_law (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (plan : ActionProgram E n H) (F : Ω → ExposureFrame (Coordinates (d + n)) E)
    (hF : ExposureFrame.MeasurableFamily F) (history : Ω → H) (hh : Measurable history) :
    (μ.prod (haarLaw (Coordinates (d + n)))).map
      (fun p => plan.run n ((F p.1).operator p.2) (history p.1)) =
    (ambientPairHistoryLaw E n μ).map (plan.paddedAmbientTranscript d n F history) := by
  unfold ActionProgram.paddedAmbientTranscript
  rw [← Measure.map_map (plan.paddedHistoryMap_measurable d n F hF history hh)
    (plan.paddedAmbientSample_preserving d n μ F hF history hh).measurable,
    (plan.paddedAmbientSample_preserving d n μ F hF history hh).map_eq]
  exact plan.paddedHistoryMap_law d n μ F hF history hh

theorem ActionProgram.paddedAmbient_haar_transcript (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (plan : ActionProgram (Coordinates (d + n)) n Ω) :
    (μ.prod (haarLaw (Coordinates (d + n)))).map
      (fun p => plan.run n (p.2 : Coordinates (d + n) →L[ℝ] Coordinates (d + n)) p.1) =
    (ambientPairHistoryLaw (Coordinates (d + n)) n μ).map
      (plan.paddedAmbientTranscript d n (fun _ => .initial) id) := by
  have h := plan.paddedAmbientTranscript_law d n μ (fun _ => .initial)
    ExposureFrame.measurable_initial id measurable_id
  simpa only [ExposureFrame.initial_operator, id_eq] using h

end RandomizedFO2003.Rotations
