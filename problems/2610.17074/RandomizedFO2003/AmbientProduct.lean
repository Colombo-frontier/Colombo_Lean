import RandomizedFO2003.AmbientStarts

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u v w

theorem AmbientPairHistory.map_comp (E : Type) (n : ℕ) {Ω : Type u} {H : Type v} {K : Type w}
    (f : Ω → H) (g : H → K) (p : AmbientPairHistory E n Ω) :
    AmbientPairHistory.map E n g (AmbientPairHistory.map E n f p) =
      AmbientPairHistory.map E n (g ∘ f) p := by
  induction n generalizing Ω H K with
  | zero => rfl
  | succ n ih => exact ih (Prod.map (Prod.map f id) id) (Prod.map (Prod.map g id) id) p

/-- Move an independent component of the initial seed outside the complete
ambient history. The remaining factor retains all sampled starts. -/
def AmbientPairHistory.separate (E : Type) : (n : ℕ) → {Ω : Type u} → {H : Type v} →
    AmbientPairHistory E n (Ω × H) → Ω × AmbientPairHistory E n H
  | 0, _, _ => id
  | n + 1, _, _ => separate E n ∘ AmbientPairHistory.map E n
      (fun p => (p.1.1.1, ((p.1.1.2, p.1.2), p.2)))

theorem AmbientPairHistory.separate_fst (E : Type) (n : ℕ) {Ω : Type u} {H : Type v}
    (p : AmbientPairHistory E n (Ω × H)) :
    (separate E n p).1 = (AmbientPairHistory.seed E n p).1 := by
  induction n generalizing Ω H with
  | zero => rfl
  | succ n ih =>
    simp only [separate, Function.comp_apply, ih, AmbientPairHistory.seed_map]
    rfl

theorem AmbientPairHistory.separate_snd (E : Type) (n : ℕ) {Ω : Type u} {H : Type v}
    (p : AmbientPairHistory E n (Ω × H)) :
    (separate E n p).2 = AmbientPairHistory.map E n Prod.snd p := by
  induction n generalizing Ω H with
  | zero => rfl
  | succ n ih =>
    simp only [separate, Function.comp_apply, ih, map_comp]
    rfl

theorem AmbientPairHistory.starts_separate (E : Type) (n : ℕ) {Ω : Type u} {H : Type v}
    (p : AmbientPairHistory E n (Ω × H)) :
    starts E n (separate E n p).2 = starts E n p := by
  rw [separate_snd, starts_map]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- In particular the full family of `2n` starts is independent of a marked
vector in the initial product seed, even if the simulated policy reads it. -/
theorem AmbientPairHistory.separate_preserving (n : ℕ) {Ω : Type u} {H : Type v}
    [MeasurableSpace Ω] [MeasurableSpace H] (μ : Measure Ω) (ν : Measure H)
    [SFinite μ] [SFinite ν] :
    MeasurePreserving (separate E n) (ambientPairHistoryLaw E n (μ.prod ν))
      (μ.prod (ambientPairHistoryLaw E n ν)) := by
  induction n generalizing Ω H with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    let σ := Spherical.sphereLaw E
    haveI : SFinite (μ.prod ν) := Measure.prod.instSFinite
    haveI : SFinite (ν.prod σ) := Measure.prod.instSFinite
    haveI : SFinite ((ν.prod σ).prod σ) := Measure.prod.instSFinite
    haveI : SFinite ((μ.prod ν).prod σ) := Measure.prod.instSFinite
    haveI : SFinite (((μ.prod ν).prod σ).prod σ) := Measure.prod.instSFinite
    haveI : SFinite (μ.prod ((ν.prod σ).prod σ)) := Measure.prod.instSFinite
    have hstep : MeasurePreserving
        (fun p : ((Ω × H) × E) × E => (p.1.1.1, ((p.1.1.2, p.1.2), p.2)))
        (((μ.prod ν).prod σ).prod σ) (μ.prod ((ν.prod σ).prod σ)) :=
      (measurePreserving_prodAssoc μ (ν.prod σ) σ).comp
        ((measurePreserving_prodAssoc μ ν σ).prod (MeasurePreserving.id σ))
    exact (ih μ ((ν.prod σ).prod σ)).comp
      (AmbientPairHistory.map_preserving n _ _ _ hstep)

end RandomizedFO2003.Rotations
