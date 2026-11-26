import RandomizedFO2003.ExposureProgram

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable (E : Type) [MeasurableSpace E]

/-- The ordinary transcript: the seed followed by the actual vectors returned
by forward or inverse actions. -/
def ActionHistory : (n : ℕ) → Type u → Type u
  | 0, H => H
  | n + 1, H => ActionHistory n (H × E)

instance actionHistoryMeasurableSpace : (n : ℕ) → (H : Type u) → [MeasurableSpace H] →
    MeasurableSpace (ActionHistory E n H)
  | 0, _, m => m
  | n + 1, H, _ => actionHistoryMeasurableSpace n (H × E)

/-- A policy reads only the seed and actual preceding responses. Each requested
vector is an arbitrary measurable function of that full transcript. -/
def ActionProgram : (n : ℕ) → (H : Type u) → [MeasurableSpace H] → Type u
  | 0, _, _ => PUnit
  | n + 1, H, _ => ExposureRequest H E × ActionProgram n (H × E)

variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

noncomputable def ActionProgram.run : (n : ℕ) → {H : Type u} → [MeasurableSpace H] →
    ActionProgram E n H → (E →L[ℝ] E) → H → ActionHistory E n H
  | 0, _, _, _, _, h => h
  | n + 1, _, _, plan, A, h => run n plan.2 A (h, plan.1.kind.action A (plan.1.vector h))

noncomputable def observedHistory {Ω H : Type u} [MeasurableSpace Ω] [MeasurableSpace H] {m : ℕ}
    (request : ExposureRequest H E) (F : Ω → ExposureFrame (Coordinates (m + 1)) E)
    (history : Ω → H) (p : Ω × Coordinates (m + 1)) : H × E :=
  (history p.1, (F p.1).exposedValue request.kind (request.vector (history p.1)) p.2)

theorem measurable_observedHistory {Ω H : Type u} [MeasurableSpace Ω] [MeasurableSpace H] {m : ℕ}
    (request : ExposureRequest H E) (F : Ω → ExposureFrame (Coordinates (m + 1)) E)
    (hF : ExposureFrame.MeasurableFamily F) (history : Ω → H) (hh : Measurable history) :
    Measurable (observedHistory request F history) := by
  have hx : Measurable (fun ω => request.vector (history ω)) := request.measurable_vector.comp hh
  have hv : Measurable (fun p : Ω × Coordinates (m + 1) =>
      (F p.1).exposedValue request.kind (request.vector (history p.1)) p.2) :=
    ExposureFrame.MeasurableFamily.exposedValue (E := E) (Ω := Ω) (n := m) (F := F)
      (x := fun ω => request.vector (history ω)) hF request.kind hx
  exact (hh.comp measurable_fst).prodMk hv

/-- Compile an ordinary transcript policy into successive spherical exposures.
This uses the proved action formula to generate every next ordinary response. -/
noncomputable def ActionProgram.compile (d : ℕ) : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → ActionProgram E n H →
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) → ExposureFrame.MeasurableFamily F →
    (history : Ω → H) → Measurable history → ExposureProgram E d n Ω
  | 0, _, _, _, _, _, _, _, _, _ => PUnit.unit
  | n + 1, _, _, _, _, plan, F, hF, history, hh =>
    (⟨plan.1.kind, plan.1.vector ∘ history, plan.1.measurable_vector.comp hh⟩,
      compile d n plan.2
        (fun p => (F p.1).standardNext plan.1.kind (plan.1.vector (history p.1)) p.2)
        (ExposureFrame.MeasurableFamily.standardNext (n := d + n) (F := F)
          (x := plan.1.vector ∘ history) hF plan.1.kind (plan.1.measurable_vector.comp hh))
        (observedHistory plan.1 F history) (measurable_observedHistory plan.1 F hF history hh))

noncomputable def ActionProgram.historyMap (d : ℕ) : (n : ℕ) → {H Ω : Type u} →
    [MeasurableSpace H] → [MeasurableSpace Ω] → ActionProgram E n H →
    (Ω → ExposureFrame (Coordinates (d + n)) E) → (Ω → H) →
      ExposureHistory d n Ω → ActionHistory E n H
  | 0, _, _, _, _, _, _, history => history
  | n + 1, _, _, _, _, plan, F, history =>
    historyMap d n plan.2
      (fun p => (F p.1).standardNext plan.1.kind (plan.1.vector (history p.1)) p.2)
      (observedHistory plan.1 F history)

theorem ActionProgram.historyMap_measurable (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (hF : ExposureFrame.MeasurableFamily F)
    (history : Ω → H) (hh : Measurable history) : Measurable (plan.historyMap d n F history) := by
  induction n generalizing H Ω with
  | zero => exact hh
  | succ n ih =>
    exact ih plan.2 _ (ExposureFrame.MeasurableFamily.standardNext (n := d + n) (F := F)
        (x := plan.1.vector ∘ history) hF plan.1.kind (plan.1.measurable_vector.comp hh))
      _ (measurable_observedHistory plan.1 F hF history hh)

/-- The compiled exposure simulation returns exactly the transcript of the
original fixed operator, for every seed and every rotation. -/
theorem ActionProgram.compile_correct (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (plan : ActionProgram E n H)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (hF : ExposureFrame.MeasurableFamily F)
    (history : Ω → H) (hh : Measurable history) (p : Ω × Rotation (Coordinates (d + n))) :
    plan.run n ((F p.1).operator p.2) (history p.1) =
      plan.historyMap d n F history ((plan.compile d n F hF history hh).run d n F p).1 := by
  induction n generalizing H Ω with
  | zero => rfl
  | succ n ih =>
    let nextF := fun q : Ω × Coordinates (d + n + 1) =>
      (F q.1).standardNext plan.1.kind (plan.1.vector (history q.1)) q.2
    have hnext : ExposureFrame.MeasurableFamily nextF :=
      ExposureFrame.MeasurableFamily.standardNext (n := d + n) (F := F)
        (x := plan.1.vector ∘ history) hF plan.1.kind (plan.1.measurable_vector.comp hh)
    let q := standardTransition plan.1.kind F (plan.1.vector ∘ history) p
    have hA : (F p.1).operator p.2 = (nextF q.1).operator q.2 :=
      standardTransition_operator plan.1.kind F (plan.1.vector ∘ history) p
    have hq : q.1.1 = p.1 := by
      dsimp [q, standardTransition]
      cases plan.1.kind <;> rfl
    have hhq : (history p.1, plan.1.kind.action ((F p.1).operator p.2) (plan.1.vector (history p.1))) =
        observedHistory plan.1 F history q.1 := by
      apply Prod.ext
      · change history p.1 = history q.1.1
        rw [hq]
      · change plan.1.kind.action ((F p.1).operator p.2) (plan.1.vector (history p.1)) =
          (F q.1.1).exposedValue plan.1.kind (plan.1.vector (history q.1.1)) q.1.2
        rw [hq]
        exact standardTransition_value plan.1.kind F (plan.1.vector ∘ history) p
    change plan.2.run n ((F p.1).operator p.2)
      (history p.1, plan.1.kind.action ((F p.1).operator p.2) (plan.1.vector (history p.1))) = _
    rw [hhq, hA]
    exact ih plan.2 nextF hnext (observedHistory plan.1 F history)
      (measurable_observedHistory plan.1 F hF history hh) q

end RandomizedFO2003.Rotations
