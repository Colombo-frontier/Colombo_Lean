import RandomizedFO2003.StandardExposure

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u v

/-- Each step appends a direction in the current residual coordinate space.
The dimension decreases by one after each exposure. -/
def ExposureHistory (d : ℕ) : (n : ℕ) → Type u → Type u
  | 0, Ω => Ω
  | n + 1, Ω => ExposureHistory d n (Ω × Coordinates (d + n + 1))

instance exposureHistoryMeasurableSpace (d : ℕ) : (n : ℕ) → (Ω : Type u) →
    [MeasurableSpace Ω] → MeasurableSpace (ExposureHistory d n Ω)
  | 0, _, m => m
  | n + 1, Ω, _ => exposureHistoryMeasurableSpace d n (Ω × Coordinates (d + n + 1))

noncomputable def exposureHistoryLaw (d : ℕ) : (n : ℕ) → {Ω : Type u} →
    [MeasurableSpace Ω] → Measure Ω → Measure (ExposureHistory d n Ω)
  | 0, _, _, μ => μ
  | n + 1, _, _, μ => exposureHistoryLaw d n (μ.prod (Spherical.sphereLaw (Coordinates (d + n + 1))))

instance exposureHistoryLaw_sFinite (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] : SFinite (exposureHistoryLaw d n μ) := by
  induction n generalizing Ω with
  | zero => exact inferInstanceAs (SFinite μ)
  | succ n ih =>
    change SFinite (exposureHistoryLaw d n (μ.prod (Spherical.sphereLaw (Coordinates (d + n + 1)))))
    haveI : IsProbabilityMeasure (Spherical.sphereLaw (Coordinates (d + n + 1))) :=
      Spherical.sphereLaw_probability _
    haveI : SFinite (μ.prod (Spherical.sphereLaw (Coordinates (d + n + 1)))) := Measure.prod.instSFinite
    exact ih _

instance exposureHistoryLaw_probability (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (exposureHistoryLaw d n μ) := by
  induction n generalizing Ω with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih =>
    change IsProbabilityMeasure (exposureHistoryLaw d n (μ.prod (Spherical.sphereLaw (Coordinates (d + n + 1)))))
    haveI : IsProbabilityMeasure (Spherical.sphereLaw (Coordinates (d + n + 1))) :=
      Spherical.sphereLaw_probability _
    exact ih _

/-- One request can depend on the entire previous history through an arbitrary
measurable vector-valued function. -/
structure ExposureRequest (Ω : Type u) (E : Type v) [MeasurableSpace Ω] [MeasurableSpace E] where
  kind : ExposureKind
  vector : Ω → E
  measurable_vector : Measurable vector

variable (E : Type v) [MeasurableSpace E]

/-- A finite schedule of forward and inverse exposures. Later requests are
arbitrary measurable functions of the successively enlarged histories. -/
def ExposureProgram (d : ℕ) : (n : ℕ) → (Ω : Type u) → [MeasurableSpace Ω] → Type (max u v)
  | 0, _, _ => PUnit
  | n + 1, Ω, _ => ExposureRequest Ω E × ExposureProgram d n (Ω × Coordinates (d + n + 1))

variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

noncomputable def ExposureProgram.finalFrame (d : ℕ) : (n : ℕ) → {Ω : Type u} → [MeasurableSpace Ω] →
    ExposureProgram E d n Ω → (Ω → ExposureFrame (Coordinates (d + n)) E) →
      ExposureHistory d n Ω → ExposureFrame (Coordinates d) E
  | 0, _, _, _, F => F
  | n + 1, _, _, plan, F =>
    finalFrame d n plan.2 (fun p => (F p.1).standardNext plan.1.kind (plan.1.vector p.1) p.2)

noncomputable def ExposureProgram.run (d : ℕ) : (n : ℕ) → {Ω : Type u} → [MeasurableSpace Ω] →
    ExposureProgram E d n Ω → (Ω → ExposureFrame (Coordinates (d + n)) E) →
      Ω × Rotation (Coordinates (d + n)) → ExposureHistory d n Ω × Rotation (Coordinates d)
  | 0, _, _, _, _ => id
  | n + 1, _, _, plan, F =>
    run d n plan.2 (fun p => (F p.1).standardNext plan.1.kind (plan.1.vector p.1) p.2) ∘
      standardTransition plan.1.kind F plan.1.vector

theorem ExposureProgram.finalFrame_measurable (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (plan : ExposureProgram E d n Ω) (F : Ω → ExposureFrame (Coordinates (d + n)) E)
    (hF : ExposureFrame.MeasurableFamily F) :
    ExposureFrame.MeasurableFamily (plan.finalFrame d n F) := by
  induction n generalizing Ω with
  | zero => exact hF
  | succ n ih =>
    exact ih plan.2 _ (hF.standardNext plan.1.kind plan.1.measurable_vector)

/-- All finitely many adaptive directions have their product sphere law;
the terminal rotation retains independent Haar law on the remaining space. -/
theorem ExposureProgram.run_preserving (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (plan : ExposureProgram E d n Ω)
    (F : Ω → ExposureFrame (Coordinates (d + n)) E) (hF : ExposureFrame.MeasurableFamily F) :
    MeasurePreserving (plan.run d n F) (μ.prod (haarLaw (Coordinates (d + n))))
      ((exposureHistoryLaw d n μ).prod (haarLaw (Coordinates d))) := by
  induction n generalizing Ω with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    haveI : IsProbabilityMeasure (Spherical.sphereLaw (Coordinates (d + n + 1))) :=
      Spherical.sphereLaw_probability _
    haveI : SFinite (μ.prod (Spherical.sphereLaw (Coordinates (d + n + 1)))) := Measure.prod.instSFinite
    exact (ih (μ.prod (Spherical.sphereLaw (Coordinates (d + n + 1)))) plan.2 _
      (hF.standardNext plan.1.kind plan.1.measurable_vector)).comp
        (standardTransition_preserving μ plan.1.kind F hF plan.1.vector plan.1.measurable_vector)

omit [BorelSpace E] in
/-- Every state in the recursion represents exactly the original operator.
The statement is pointwise and includes degenerate/zero requested vectors. -/
theorem ExposureProgram.run_operator (d n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (plan : ExposureProgram E d n Ω) (F : Ω → ExposureFrame (Coordinates (d + n)) E)
    (p : Ω × Rotation (Coordinates (d + n))) :
    (F p.1).operator p.2 = (plan.finalFrame d n F (plan.run d n F p).1).operator (plan.run d n F p).2 := by
  induction n generalizing Ω with
  | zero => rfl
  | succ n ih =>
    exact (standardTransition_operator plan.1.kind F plan.1.vector p).trans
      (ih plan.2 (fun q => (F q.1).standardNext plan.1.kind (plan.1.vector q.1) q.2)
        (standardTransition plan.1.kind F plan.1.vector p))

end RandomizedFO2003.Rotations
