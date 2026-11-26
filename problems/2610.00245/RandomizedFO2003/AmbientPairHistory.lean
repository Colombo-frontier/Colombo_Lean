import RandomizedFO2003.PaddedHistory

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u v

/-- Two independent ambient vectors per exposure: an auxiliary response vector
and the vector generating the next projected direction. -/
def AmbientPairHistory (E : Type) : (n : ℕ) → Type u → Type u
  | 0, Ω => Ω
  | n + 1, Ω => AmbientPairHistory E n ((Ω × E) × E)

instance ambientPairHistoryMeasurableSpace (E : Type) [MeasurableSpace E] :
    (n : ℕ) → (Ω : Type u) → [MeasurableSpace Ω] → MeasurableSpace (AmbientPairHistory E n Ω)
  | 0, _, m => m
  | n + 1, Ω, _ => ambientPairHistoryMeasurableSpace E n ((Ω × E) × E)

def AmbientPairHistory.map (E : Type) : (n : ℕ) → {Ω : Type u} → {H : Type v} →
    (Ω → H) → AmbientPairHistory E n Ω → AmbientPairHistory E n H
  | 0, _, _, f => f
  | n + 1, _, _, f => map E n (Prod.map (Prod.map f id) id)

def AmbientPairHistory.seed (E : Type) : (n : ℕ) → {Ω : Type u} → AmbientPairHistory E n Ω → Ω
  | 0, _, p => p
  | n + 1, _, p => (seed E n p).1.1

@[simp] theorem AmbientPairHistory.seed_map (E : Type) (n : ℕ) {Ω : Type u} {H : Type v}
    (f : Ω → H) (p : AmbientPairHistory E n Ω) :
    AmbientPairHistory.seed E n (AmbientPairHistory.map E n f p) = f (AmbientPairHistory.seed E n p) := by
  induction n generalizing Ω H with
  | zero => rfl
  | succ n ih => exact congrArg (fun q => q.1.1) (ih (Prod.map (Prod.map f id) id) p)

theorem AmbientPairHistory.map_measurable {E : Type} [MeasurableSpace E] (n : ℕ)
    {Ω : Type u} {H : Type v} [MeasurableSpace Ω] [MeasurableSpace H] (f : Ω → H) (hf : Measurable f) :
    Measurable (AmbientPairHistory.map E n f) := by
  induction n generalizing Ω H with
  | zero => exact hf
  | succ n ih => exact ih _ ((hf.prodMap measurable_id).prodMap measurable_id)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def ambientPairHistoryLaw (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    (n : ℕ) → {Ω : Type u} → [MeasurableSpace Ω] → Measure Ω → Measure (AmbientPairHistory E n Ω)
  | 0, _, _, μ => μ
  | n + 1, _, _, μ => ambientPairHistoryLaw E n ((μ.prod (Spherical.sphereLaw E)).prod (Spherical.sphereLaw E))

instance ambientPairHistoryLaw_sFinite (n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] : SFinite (ambientPairHistoryLaw E n μ) := by
  induction n generalizing Ω with
  | zero => exact inferInstanceAs (SFinite μ)
  | succ n ih =>
    haveI : SFinite (μ.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    haveI : SFinite ((μ.prod (Spherical.sphereLaw E)).prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    exact ih _

instance ambientPairHistoryLaw_probability (n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (ambientPairHistoryLaw E n μ) := by
  induction n generalizing Ω with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih => exact ih _

theorem AmbientPairHistory.map_preserving (n : ℕ) {Ω : Type u} {H : Type v}
    [MeasurableSpace Ω] [MeasurableSpace H] (μ : Measure Ω) (ν : Measure H) [SFinite μ] [SFinite ν]
    (f : Ω → H) (hf : MeasurePreserving f μ ν) :
    MeasurePreserving (AmbientPairHistory.map E n f) (ambientPairHistoryLaw E n μ) (ambientPairHistoryLaw E n ν) := by
  induction n generalizing Ω H with
  | zero => exact hf
  | succ n ih =>
    haveI : SFinite (μ.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    haveI : SFinite (ν.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    haveI : SFinite ((μ.prod (Spherical.sphereLaw E)).prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    haveI : SFinite ((ν.prod (Spherical.sphereLaw E)).prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    exact ih _ _ _ ((hf.prod (MeasurePreserving.id (Spherical.sphereLaw E))).prod
      (MeasurePreserving.id (Spherical.sphereLaw E)))

theorem AmbientPairHistory.seed_preserving (n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] :
    MeasurePreserving (AmbientPairHistory.seed E n) (ambientPairHistoryLaw E n μ) μ := by
  induction n generalizing Ω with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    haveI : SFinite (μ.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    haveI : SFinite ((μ.prod (Spherical.sphereLaw E)).prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    have hfst : MeasurePreserving (Prod.fst : Ω × E → Ω) (μ.prod (Spherical.sphereLaw E)) μ :=
      ⟨measurable_fst, by simp⟩
    have hfst' : MeasurePreserving (Prod.fst : (Ω × E) × E → Ω × E)
        ((μ.prod (Spherical.sphereLaw E)).prod (Spherical.sphereLaw E)) (μ.prod (Spherical.sphereLaw E)) :=
      ⟨measurable_fst, by simp⟩
    exact (hfst.comp hfst').comp (ih _)

end RandomizedFO2003.Rotations
