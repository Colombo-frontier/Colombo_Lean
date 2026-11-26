import RandomizedFO2003.AmbientPairHistory

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u v

/-- The original ambient pair at each exposure, before any projection or
adaptive change of coordinates. -/
def AmbientPairHistory.pairs (E : Type) : (n : ℕ) → {Ω : Type u} →
    AmbientPairHistory E n Ω → Fin n → E × E
  | 0, _, _ => Fin.elim0
  | n + 1, _, p => Fin.cons
      ((AmbientPairHistory.seed E n p).1.2, (AmbientPairHistory.seed E n p).2)
      (pairs E n p)

/-- Exactly `2 * n` original vectors, indexed as two consecutive groups of
length `n`. This family is independent of the adaptive requests. -/
def AmbientPairHistory.starts (E : Type) (n : ℕ) {Ω : Type u}
    (p : AmbientPairHistory E n Ω) : Fin (n + n) → E :=
  Fin.append (fun i => (pairs E n p i).1) (fun i => (pairs E n p i).2)

def AmbientPairHistory.AllIn (E : Type) [AddCommGroup E] [Module ℝ E]
    (N : Submodule ℝ E) : (n : ℕ) → {Ω : Type u} → AmbientPairHistory E n Ω → Prop
  | 0, _, _ => True
  | n + 1, _, p =>
      (AmbientPairHistory.seed E n p).1.2 ∈ N ∧
      (AmbientPairHistory.seed E n p).2 ∈ N ∧ AllIn E N n p

theorem AmbientPairHistory.allIn_iff_pairs (E : Type) [AddCommGroup E] [Module ℝ E]
    (N : Submodule ℝ E) (n : ℕ) {Ω : Type u} (p : AmbientPairHistory E n Ω) :
    AllIn E N n p ↔ ∀ i, (pairs E n p i).1 ∈ N ∧ (pairs E n p i).2 ∈ N := by
  induction n generalizing Ω with
  | zero => simp [AllIn]
  | succ n ih =>
    simp only [AllIn, pairs, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, ← ih]
    tauto

theorem AmbientPairHistory.allIn_iff_starts (E : Type) [AddCommGroup E] [Module ℝ E]
    (N : Submodule ℝ E) (n : ℕ) {Ω : Type u} (p : AmbientPairHistory E n Ω) :
    AllIn E N n p ↔ ∀ i, starts E n p i ∈ N := by
  rw [allIn_iff_pairs]
  constructor
  · intro h i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [starts, Fin.append_left] using (h j).1
    · simpa only [starts, Fin.append_right] using (h j).2
  · intro h i
    exact ⟨by simpa only [starts, Fin.append_left] using h (i.castAdd n),
      by simpa only [starts, Fin.append_right] using h (i.natAdd n)⟩

theorem AmbientPairHistory.pairs_map (E : Type) (n : ℕ) {Ω : Type u} {H : Type v}
    (f : Ω → H) (p : AmbientPairHistory E n Ω) :
    pairs E n (AmbientPairHistory.map E n f p) = pairs E n p := by
  induction n generalizing Ω H with
  | zero => rfl
  | succ n ih =>
    simp only [pairs, AmbientPairHistory.map, AmbientPairHistory.seed_map, Prod.map_apply,
      id_eq, ih]
    rfl

theorem AmbientPairHistory.starts_map (E : Type) (n : ℕ) {Ω : Type u} {H : Type v}
    (f : Ω → H) (p : AmbientPairHistory E n Ω) :
    starts E n (AmbientPairHistory.map E n f p) = starts E n p := by
  simp only [starts, pairs_map]

theorem AmbientPairHistory.seed_measurable {E : Type} [MeasurableSpace E] (n : ℕ)
    {Ω : Type u} [MeasurableSpace Ω] : Measurable (AmbientPairHistory.seed E n (Ω := Ω)) := by
  induction n generalizing Ω with
  | zero => exact measurable_id
  | succ n ih => exact (ih (Ω := (Ω × E) × E)).fst.fst

theorem AmbientPairHistory.pairs_measurable {E : Type} [MeasurableSpace E] (n : ℕ)
    {Ω : Type u} [MeasurableSpace Ω] (i : Fin n) :
    Measurable (fun p : AmbientPairHistory E n Ω => pairs E n p i) := by
  induction n generalizing Ω with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change Measurable (fun p : AmbientPairHistory E n ((Ω × E) × E) =>
        ((AmbientPairHistory.seed E n p).1.2, (AmbientPairHistory.seed E n p).2))
      exact (seed_measurable n).fst.snd.prodMk (seed_measurable n).snd
    · exact ih j

theorem AmbientPairHistory.starts_measurable {E : Type} [MeasurableSpace E] (n : ℕ)
    {Ω : Type u} [MeasurableSpace Ω] (i : Fin (n + n)) :
    Measurable (fun p : AmbientPairHistory E n Ω => starts E n p i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [starts, Fin.append_left] using (pairs_measurable n j (Ω := Ω)).fst
  · simpa only [starts, Fin.append_right] using (pairs_measurable n j (Ω := Ω)).snd

end RandomizedFO2003.Rotations
