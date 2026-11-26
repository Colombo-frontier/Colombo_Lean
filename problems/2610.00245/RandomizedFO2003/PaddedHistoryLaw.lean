import RandomizedFO2003.PaddedHistory

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem ActionProgram.run_measurable (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (hF : ExposureFrame.MeasurableFamily F)
    (history : Ω → H) (hh : Measurable history) :
    Measurable (fun p : Ω × Rotation (Coordinates (d + n)) =>
      plan.run n ((F p.1).operator p.2) (history p.1)) :=
  (plan.exposureCoordinates_preserving d n (0 : Measure Ω) F hF history hh).measurable.fst

/-- Adding fresh auxiliary vectors at every step preserves the full law of
the true adaptive transcript, including every degenerate response branch. -/
theorem ActionProgram.paddedHistoryMap_law (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (plan : ActionProgram E n H) (F : Ω → ExposureFrame (Coordinates (d + n)) E)
    (hF : ExposureFrame.MeasurableFamily F) (history : Ω → H) (hh : Measurable history) :
    (μ.prod (haarLaw (Coordinates (d + n)))).map
      (fun p => plan.run n ((F p.1).operator p.2) (history p.1)) =
    (paddedHistoryLaw E d n μ).map (plan.paddedHistoryMap d n F history) := by
  induction n generalizing H Ω with
  | zero =>
    change (μ.prod (haarLaw (Coordinates d))).map (history ∘ Prod.fst) = μ.map history
    rw [← Measure.map_map hh measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  | succ n ih =>
    let x : Ω → E := plan.1.vector ∘ history
    have hx : Measurable x := plan.1.measurable_vector.comp hh
    let nextF := paddedFrameNext plan.1.kind F x
    let nextH := paddedObservedHistory plan.1 F history
    have hnextF : ExposureFrame.MeasurableFamily nextF := measurable_paddedFrameNext _ F hF x hx
    have hnextH : Measurable nextH := measurable_paddedObservedHistory _ F hF history hh
    let μa := μ.prod (Spherical.sphereLaw E)
    haveI : SFinite μa := Measure.prod.instSFinite
    let ν := μa.prod (Spherical.sphereLaw (Coordinates (d + n + 1)))
    haveI : SFinite ν := Measure.prod.instSFinite
    let transition := paddedTransition plan.1.kind (fun p : Ω × E => F p.1)
      (fun p => x p.1) Prod.snd
    have ht : MeasurePreserving transition (μa.prod (haarLaw (Coordinates (d + n + 1))))
        (ν.prod (haarLaw (Coordinates (d + n)))) :=
      paddedTransition_preserving μa _ _ (hF.comp measurable_fst) _ _
        (hx.comp measurable_fst) measurable_snd
    have hf : MeasurePreserving (Prod.fst : Ω × E → Ω) μa μ := ⟨measurable_fst, by simp [μa]⟩
    haveI : IsFiniteMeasure (haarLaw (Coordinates (d + n + 1))) := ⟨by simp⟩
    haveI : SigmaFinite (haarLaw (Coordinates (d + n + 1))) := IsFiniteMeasure.toSigmaFinite _
    haveI : SFinite (haarLaw (Coordinates (d + n + 1))) := inferInstance
    have hlift := hf.prod (MeasurePreserving.id (haarLaw (Coordinates (d + n + 1))))
    have htrue := plan.run_measurable d (n + 1) F hF history hh
    have hrest := plan.2.run_measurable d n nextF hnextF nextH hnextH
    have heq :
        (fun p : (Ω × E) × Rotation (Coordinates (d + n + 1)) =>
          plan.run (n + 1) ((F p.1.1).operator p.2) (history p.1.1)) =
        (fun q => plan.2.run n ((nextF q.1).operator q.2) (nextH q.1)) ∘ transition := by
      funext p
      let q := transition p
      have hA : (F p.1.1).operator p.2 = (nextF q.1).operator q.2 :=
        paddedTransition_operator plan.1.kind (fun p : Ω × E => F p.1) (fun p => x p.1) Prod.snd p
      have hq : q.1.1.1 = p.1.1 := by
        dsimp [q, transition, paddedTransition, standardTransition]
        cases plan.1.kind <;> rfl
      have hhq : (history p.1.1, plan.1.kind.action ((F p.1.1).operator p.2) (x p.1.1)) = nextH q.1 := by
        apply Prod.ext
        · change history p.1.1 = history q.1.1.1
          rw [hq]
        · change plan.1.kind.action ((F p.1.1).operator p.2) (x p.1.1) =
            (F q.1.1.1).exposedValue plan.1.kind (x q.1.1.1) q.1.2
          rw [hq]
          exact paddedTransition_value plan.1.kind (fun p : Ω × E => F p.1) (fun p => x p.1) Prod.snd p
      change plan.2.run n ((F p.1.1).operator p.2)
        (history p.1.1, plan.1.kind.action ((F p.1.1).operator p.2) (x p.1.1)) = _
      rw [hhq, hA]
      rfl
    calc
      _ = (μa.prod (haarLaw (Coordinates (d + n + 1)))).map
          (fun p => plan.run (n + 1) ((F p.1.1).operator p.2) (history p.1.1)) := by
        have hm : MeasurePreserving (fun p => plan.run (n + 1) ((F p.1).operator p.2) (history p.1))
            (μ.prod (haarLaw (Coordinates (d + (n + 1)))))
            ((μ.prod (haarLaw (Coordinates (d + (n + 1))))).map
              (fun p => plan.run (n + 1) ((F p.1).operator p.2) (history p.1))) := ⟨htrue, rfl⟩
        exact (hm.comp hlift).map_eq.symm
      _ = (μa.prod (haarLaw (Coordinates (d + n + 1)))).map
          ((fun q => plan.2.run n ((nextF q.1).operator q.2) (nextH q.1)) ∘ transition) := by rw [heq]
      _ = (ν.prod (haarLaw (Coordinates (d + n)))).map
          (fun q => plan.2.run n ((nextF q.1).operator q.2) (nextH q.1)) := by
        have hm : MeasurePreserving (fun q => plan.2.run n ((nextF q.1).operator q.2) (nextH q.1))
            (ν.prod (haarLaw (Coordinates (d + n))))
            ((ν.prod (haarLaw (Coordinates (d + n)))).map
              (fun q => plan.2.run n ((nextF q.1).operator q.2) (nextH q.1))) := ⟨hrest, rfl⟩
        exact (hm.comp ht).map_eq
      _ = _ := ih ν plan.2 nextF hnextF nextH hnextH

/-- Concrete specialization to the initial genuine Haar rotation. -/
theorem ActionProgram.padded_haar_transcript (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (plan : ActionProgram (Coordinates (d + n)) n Ω) :
    (μ.prod (haarLaw (Coordinates (d + n)))).map
      (fun p => plan.run n (p.2 : Coordinates (d + n) →L[ℝ] Coordinates (d + n)) p.1) =
    (paddedHistoryLaw (Coordinates (d + n)) d n μ).map
      (plan.paddedHistoryMap d n (fun _ => .initial) id) := by
  have h := plan.paddedHistoryMap_law d n μ (fun _ => .initial) ExposureFrame.measurable_initial id measurable_id
  simpa only [ExposureFrame.initial_operator, id_eq] using h

end RandomizedFO2003.Rotations
