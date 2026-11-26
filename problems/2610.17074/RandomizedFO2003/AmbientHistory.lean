import RandomizedFO2003.ActionProgram
import RandomizedFO2003.ProjectedSphere

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable (E : Type) [MeasurableSpace E]

/-- Relabel the seed of a finite vector history, retaining every sampled vector. -/
def ActionHistory.map : (n : ℕ) → {Ω H : Type u} → (Ω → H) → ActionHistory E n Ω → ActionHistory E n H
  | 0, _, _, f => f
  | n + 1, _, _, f => map n (Prod.map f id)

variable {E}

theorem ActionHistory.map_measurable (n : ℕ) {Ω H : Type u} [MeasurableSpace Ω] [MeasurableSpace H]
    (f : Ω → H) (hf : Measurable f) : Measurable (ActionHistory.map E n f) := by
  induction n generalizing Ω H with
  | zero => exact hf
  | succ n ih => exact ih _ (hf.prodMap measurable_id)

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

/-- A product law of fresh ambient sphere vectors, independent of the initial seed. -/
noncomputable def ambientHistoryLaw (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    (n : ℕ) → {Ω : Type u} → [MeasurableSpace Ω] → Measure Ω → Measure (ActionHistory E n Ω)
  | 0, _, _, μ => μ
  | n + 1, _, _, μ => ambientHistoryLaw E n (μ.prod (Spherical.sphereLaw E))

instance ambientHistoryLaw_sFinite (n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] : SFinite (ambientHistoryLaw E n μ) := by
  induction n generalizing Ω with
  | zero => exact inferInstanceAs (SFinite μ)
  | succ n ih =>
    haveI : SFinite (μ.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    exact ih _

instance ambientHistoryLaw_probability (n : ℕ) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (ambientHistoryLaw E n μ) := by
  induction n generalizing Ω with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih => exact ih _

/-- Relabeling a seed commutes with adjoining any finite number of independent
ambient vectors, including when the new seed contains a just-revealed direction. -/
theorem ActionHistory.map_preserving (n : ℕ) {Ω H : Type u} [MeasurableSpace Ω] [MeasurableSpace H]
    (μ : Measure Ω) (ν : Measure H) [SFinite μ] [SFinite ν] (f : Ω → H)
    (hf : MeasurePreserving f μ ν) :
    MeasurePreserving (ActionHistory.map E n f) (ambientHistoryLaw E n μ) (ambientHistoryLaw E n ν) := by
  induction n generalizing Ω H with
  | zero => exact hf
  | succ n ih =>
    haveI : SFinite (μ.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    haveI : SFinite (ν.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    exact ih _ _ _ (hf.prod (MeasurePreserving.id (Spherical.sphereLaw E)))

end RandomizedFO2003.Rotations
