import RandomizedFO2003.ActionProgram

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Actual adaptive transcript, paired with the residual rotation extracted by
the finite exposure recursion. -/
noncomputable def ActionProgram.exposureCoordinates (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (hF : ExposureFrame.MeasurableFamily F)
    (history : Ω → H) (hh : Measurable history) (p : Ω × Rotation (Coordinates (d + n))) :
    ActionHistory E n H × Rotation (Coordinates d) :=
  (plan.run n ((F p.1).operator p.2) (history p.1), ((plan.compile d n F hF history hh).run d n F p).2)

/-- The entire true transcript is independent of the terminal Haar rotation.
Its law is exactly the pushforward of independent spherical exposure directions. -/
theorem ActionProgram.exposureCoordinates_preserving (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (plan : ActionProgram E n H) (F : Ω → ExposureFrame (Coordinates (d + n)) E)
    (hF : ExposureFrame.MeasurableFamily F) (history : Ω → H) (hh : Measurable history) :
    MeasurePreserving (plan.exposureCoordinates d n F hF history hh)
      (μ.prod (haarLaw (Coordinates (d + n))))
      (((exposureHistoryLaw d n μ).map (plan.historyMap d n F history)).prod (haarLaw (Coordinates d))) := by
  have hm : MeasurePreserving (plan.historyMap d n F history) (exposureHistoryLaw d n μ)
      ((exposureHistoryLaw d n μ).map (plan.historyMap d n F history)) :=
    ⟨plan.historyMap_measurable d n F hF history hh, rfl⟩
  have heq : plan.exposureCoordinates d n F hF history hh =
      (Prod.map (plan.historyMap d n F history) id) ∘ (plan.compile d n F hF history hh).run d n F := by
    funext p
    apply Prod.ext
    · exact plan.compile_correct d n F hF history hh p
    · rfl
  rw [heq]
  exact (hm.prod (MeasurePreserving.id (haarLaw (Coordinates d)))).comp
    ((plan.compile d n F hF history hh).run_preserving d n μ F hF)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem ExposureFrame.measurable_initial {Ω : Type u} [MeasurableSpace Ω] :
    ExposureFrame.MeasurableFamily (fun _ : Ω => (ExposureFrame.initial : ExposureFrame E E)) :=
  ⟨measurable_const, measurable_const, measurable_const⟩

/-- Starting from a genuine Haar rotation and any independent measurable seed
space, a finite full-transcript policy has a concrete spherical simulation and
a remaining independent Haar rotation. The ambient dimension is `d + n`. -/
theorem ActionProgram.haar_transcript_representation (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (plan : ActionProgram (Coordinates (d + n)) n Ω) :
    ∃ (transcript : ExposureHistory d n Ω → ActionHistory (Coordinates (d + n)) n Ω)
      (residual : Ω × Rotation (Coordinates (d + n)) → Rotation (Coordinates d)),
      Measurable transcript ∧ Measurable residual ∧
      MeasurePreserving
        (fun p => (plan.run n (p.2 : Coordinates (d + n) →L[ℝ] Coordinates (d + n)) p.1, residual p))
        (μ.prod (haarLaw (Coordinates (d + n))))
        (((exposureHistoryLaw d n μ).map transcript).prod (haarLaw (Coordinates d))) := by
  let F : Ω → ExposureFrame (Coordinates (d + n)) (Coordinates (d + n)) := fun _ => .initial
  have hF : ExposureFrame.MeasurableFamily F := ExposureFrame.measurable_initial
  let compiled := plan.compile d n F hF id measurable_id
  refine ⟨plan.historyMap d n F id, (fun p => (compiled.run d n F p).2),
    plan.historyMap_measurable d n F hF id measurable_id,
    (compiled.run_preserving d n μ F hF).measurable.snd, ?_⟩
  have hp := plan.exposureCoordinates_preserving d n μ F hF id measurable_id
  convert hp using 1
  funext p
  apply Prod.ext
  · exact congrArg (fun A => plan.run n A p.1) (ExposureFrame.initial_operator p.2).symm
  · rfl

end RandomizedFO2003.Rotations
