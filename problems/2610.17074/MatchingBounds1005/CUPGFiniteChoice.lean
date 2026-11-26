import MatchingBounds1005.Model
import Mathlib.Tactic

/-! Finite measurable choices made only from already returned scalar values. -/
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.CUPG

def chooseLower {E : Type*} (f : E → ℝ) (x y : E) : E := if f x ≤ f y then x else y

@[simp] theorem chooseLower_value {E : Type*} (f : E → ℝ) (x y : E) :
    f (chooseLower f x y) = min (f x) (f y) := by
  unfold chooseLower
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

theorem chooseLower_mem {E : Type*} (f : E → ℝ) (x y : E) : chooseLower f x y = x ∨ chooseLower f x y = y := by
  unfold chooseLower
  split_ifs <;> simp

def bestPoint {E : Type*} (f : E → ℝ) (start : E) : List E → E
  | [] => start
  | x :: xs => chooseLower f x (bestPoint f start xs)

theorem bestPoint_le_start {E : Type*} (f : E → ℝ) (start : E) (xs : List E) :
    f (bestPoint f start xs) ≤ f start := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    change f (chooseLower f x (bestPoint f start xs)) ≤ f start
    rw [chooseLower_value f x (bestPoint f start xs)]
    exact (min_le_right _ _).trans ih

theorem bestPoint_le_mem {E : Type*} (f : E → ℝ) (start : E) (xs : List E) (x : E) (hx : x ∈ xs) :
    f (bestPoint f start xs) ≤ f x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    change f (chooseLower f y (bestPoint f start ys)) ≤ f x
    rw [chooseLower_value f y (bestPoint f start ys)]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hx)

/-- The lower-value selection is measurable in the candidate/response data;
the function itself does not appear in this oracle-side operation. -/
def chooseLowerReply {E : Type*} (x y : E × ℝ) : E × ℝ := if x.2 ≤ y.2 then x else y

theorem chooseLowerReply_measurable {E : Type*} [MeasurableSpace E] :
    Measurable (fun p : (E × ℝ) × (E × ℝ) => chooseLowerReply p.1 p.2) := by
  exact Measurable.ite (measurableSet_le measurable_fst.snd measurable_snd.snd)
    measurable_fst measurable_snd

theorem chooseLowerReply_correct {E : Type*} (f : E → ℝ) (x y : E) :
    chooseLowerReply (x, f x) (y, f y) = (chooseLower f x y, f (chooseLower f x y)) := by
  unfold chooseLowerReply chooseLower
  split_ifs <;> rfl

/-- Bounded first-success selection, using no unbounded search. -/
def firstIndex (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ
  | 0 => 0
  | n + 1 => if P (firstIndex P n) then firstIndex P n else n + 1

theorem firstIndex_le (P : ℕ → Prop) [DecidablePred P] (N : ℕ) : firstIndex P N ≤ N := by
  induction N with
  | zero => exact le_rfl
  | succ N ih => simp only [firstIndex]; split_ifs <;> omega

theorem firstIndex_spec (P : ℕ → Prop) [DecidablePred P] (N : ℕ) (hP : P N) : P (firstIndex P N) := by
  cases N with
  | zero => exact hP
  | succ N => simp only [firstIndex]; split_ifs with h <;> assumption

theorem firstIndex_found_or_last (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    P (firstIndex P N) ∨ firstIndex P N = N := by
  cases N with
  | zero => exact Or.inr rfl
  | succ N =>
    simp only [firstIndex]
    split_ifs with h
    · exact Or.inl h
    · exact Or.inr rfl

theorem firstIndex_min (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ∀ j < firstIndex P N, ¬ P j := by
  induction N with
  | zero => intro j hj; simp [firstIndex] at hj
  | succ N ih =>
    simp only [firstIndex]
    split_ifs with h
    · exact ih
    · intro j hj hpj
      have he : firstIndex P N = N := (firstIndex_found_or_last P N).resolve_left h
      by_cases hjN : j = N
      · exact h (he.symm ▸ hjN ▸ hpj)
      · exact ih j (by omega) hpj

end MatchingBounds1005.CUPG
