import Bilevel.FreshUpdate

/-! Finite independent draw spaces and genuine measurable adaptive executions.
The nested product presentation makes the fresh seed at each call explicit. -/

noncomputable section
open MeasureTheory

namespace Bilevel.IndependentDraws

universe u

def Draws (Seed : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Draws Seed n × Seed

instance {Seed : Type u} [MeasurableSpace Seed] (n : ℕ) : MeasurableSpace (Draws Seed n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (MeasurableSpace (Draws Seed n × Seed))

variable {Seed : Type u} [MeasurableSpace Seed]

def law (ν : Measure Seed) : (n : ℕ) → Measure (Draws Seed n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => (law ν n).prod ν

instance law_probability (ν : Measure Seed) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (law ν n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (IsProbabilityMeasure ((law ν n).prod ν))

def take {m n : ℕ} (h : m ≤ n) : Draws Seed n → Draws Seed m :=
  Nat.leRecOn (C := fun k => Draws Seed k → Draws Seed m) h (fun {_k} f z => f z.1) id

omit [MeasurableSpace Seed] in
@[simp] theorem take_self (n : ℕ) : take (Seed := Seed) (le_refl n) = id := by
  unfold take
  rw [Nat.leRecOn_self]

omit [MeasurableSpace Seed] in
theorem take_succ {m n : ℕ} (h : m ≤ n) :
    take (Seed := Seed) (Nat.le_step h) = fun z => take h z.1 := by
  unfold take
  rw [Nat.leRecOn_succ h]

theorem take_measurable {m n : ℕ} (h : m ≤ n) : Measurable (take (Seed := Seed) h) := by
  induction h with
  | refl => simpa only [take_self] using measurable_id
  | @step n h ih =>
    rw [take_succ h]
    exact ih.comp measurable_fst

theorem take_preserves (ν : Measure Seed) [IsProbabilityMeasure ν]
    {m n : ℕ} (h : m ≤ n) : MeasurePreserving (take (Seed := Seed) h) (law ν n) (law ν m) := by
  induction h with
  | refl => simpa only [take_self] using MeasurePreserving.id (law ν m)
  | @step n h ih =>
    rw [take_succ h]
    exact ih.comp (FreshOracle.Oracle.fst_preserves (μ := law ν n) (ν := ν))

omit [MeasurableSpace Seed] in
theorem take_comp {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) (z : Draws Seed k) :
    take hmn (take hnk z) = take (hmn.trans hnk) z := by
  induction hnk with
  | refl => simp only [take_self, id_eq]
  | @step k h ih =>
    rw [take_succ h, take_succ (hmn.trans h)]
    exact ih z.1

variable {State Query E : Type*}

def run (query : ℕ → State → Query) (update : ℕ → State → E → State)
    (sample : Query → Seed → E) (initial : State) : (n : ℕ) → Draws Seed n → State
  | 0, _ => initial
  | n + 1, z =>
    let state := run query update sample initial n z.1
    update n state (sample (query n state) z.2)

variable [MeasurableSpace State] [MeasurableSpace Query] [MeasurableSpace E]

theorem run_measurable (query : ℕ → State → Query) (update : ℕ → State → E → State)
    (sample : Query → Seed → E) (initial : State)
    (hq : ∀ n, Measurable (query n))
    (hu : ∀ n, Measurable (fun se : State × E => update n se.1 se.2))
    (hs : Measurable (fun qs : Query × Seed => sample qs.1 qs.2)) (n : ℕ) :
    Measurable (run query update sample initial n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hstate := ih.comp (measurable_fst : Measurable (Prod.fst : Draws Seed n × Seed → Draws Seed n))
    exact (hu n).comp (hstate.prodMk (hs.comp (((hq n).comp hstate).prodMk measurable_snd)))

end Bilevel.IndependentDraws
