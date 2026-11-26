import SampleReuse.CurvatureFirstFreshness
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory
open scoped Classical

namespace SampleReuse
noncomputable section

def boundedClockTime (clock : ℕ → ℕ) (k T : ℕ) : ℕ :=
  Nat.find (show ∃ t, T+1 ≤ t ∨ k < clock (t+1) from ⟨T+1,Or.inl le_rfl⟩)

theorem boundedClockTime_le (clock : ℕ → ℕ) (k T : ℕ) : boundedClockTime clock k T ≤ T+1 :=
  Nat.find_min' _ (Or.inl le_rfl)

theorem boundedClockTime_crosses (clock : ℕ → ℕ) (k T : ℕ)
    (ht : boundedClockTime clock k T ≤ T) : k < clock (boundedClockTime clock k T+1) := by
  have hs := Nat.find_spec (show ∃ t, T+1 ≤ t ∨ k < clock (t+1) from ⟨T+1,Or.inl le_rfl⟩)
  change T+1 ≤ boundedClockTime clock k T ∨ _ at hs
  exact hs.resolve_left (by omega)

theorem boundedClockTime_clock_le (clock : ℕ → ℕ) (k T : ℕ) (hzero : clock 0 = 0) :
    clock (boundedClockTime clock k T) ≤ k := by
  cases he : boundedClockTime clock k T with
  | zero => simp [hzero]
  | succ t =>
    have hm := Nat.find_min (show ∃ t, T+1 ≤ t ∨ k < clock (t+1) from ⟨T+1,Or.inl le_rfl⟩)
      (show t < boundedClockTime clock k T by omega)
    exact le_of_not_gt (fun h => hm (Or.inr h))

theorem boundedClockTime_clock_eq (clock : ℕ → ℕ) (k T : ℕ) (hzero : clock 0 = 0)
    (hstep : ∀ t, clock (t+1) ≤ clock t+1) (ht : boundedClockTime clock k T ≤ T) :
    clock (boundedClockTime clock k T) = k := by
  have hl := boundedClockTime_clock_le clock k T hzero
  have hh := boundedClockTime_crosses clock k T ht
  have hs := hstep (boundedClockTime clock k T)
  omega

theorem boundedClockTime_congr (clock clock' : ℕ → ℕ) (k T : ℕ)
    (heq : ∀ t, clock t ≤ k ↔ clock' t ≤ k) : boundedClockTime clock k T = boundedClockTime clock' k T := by
  apply Nat.find_congr'
  intro t
  exact or_congr Iff.rfl (by simpa only [not_le] using (heq (t+1)).not)

theorem boundedClockTime_measurable {S : Type*} [MeasurableSpace S]
    (clock : S → ℕ → ℕ) (hc : ∀ t, Measurable (fun s => clock s t)) (k T : ℕ) :
    Measurable (fun s => boundedClockTime (clock s) k T) := by
  apply measurable_find
  intro t
  have hconst : MeasurableSet {s : S | T+1 ≤ t} := by
    by_cases ht : T+1 ≤ t <;> simp [ht]
  exact hconst.union (measurableSet_lt measurable_const (hc (t+1)))

theorem boundedClockTime_lt_of_crossed (clock : ℕ → ℕ) (k T : ℕ) (hzero : clock 0 = 0)
    {t : ℕ} (ht : k < clock t) : boundedClockTime clock k T < t := by
  cases t with
  | zero => simp only [hzero,Nat.not_lt_zero] at ht
  | succ t =>
    exact Nat.lt_succ_of_le (Nat.find_min' _ (Or.inr ht))

end
end SampleReuse
