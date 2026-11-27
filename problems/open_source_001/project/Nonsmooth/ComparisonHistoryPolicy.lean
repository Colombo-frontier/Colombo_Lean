import Nonsmooth.HistoryPolicy
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

abbrev ResponseOrder (n : ℕ) := Fin n → Fin n → Bool

def responseOrder {X : Type} {n : ℕ} (h : History X n) : ResponseOrder n :=
  fun i j => if (h i).2 ≤ (h j).2 then true else false

def comparisonHistoryPolicy {X : Type}
    (q o : ∀ n, ResponseOrder n → X) : HistoryPolicy Unit X where
  query n _ h := q n (responseOrder h)
  output n _ h := o n (responseOrder h)

theorem responseOrder_measurable {X : Type} [MeasurableSpace X] (n : ℕ) :
    Measurable (responseOrder (X := X) (n := n)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply Measurable.ite
  · exact measurableSet_le ((measurable_pi_apply i).snd) ((measurable_pi_apply j).snd)
  · exact measurable_const
  · exact measurable_const

/-- Arbitrary geometric choices on finitely many comparison patterns give Borel queries. -/
theorem comparisonHistoryPolicy_measurable {X : Type} [MeasurableSpace X]
    (q o : ∀ n, ResponseOrder n → X) : (comparisonHistoryPolicy q o).IsMeasurable := by
  constructor
  · intro n
    exact (measurable_of_countable (q n)).comp ((responseOrder_measurable n).comp measurable_snd)
  · intro n
    exact (measurable_of_countable (o n)).comp ((responseOrder_measurable n).comp measurable_snd)

def shiftedValueHistory {X : Type} {n : ℕ} (c : ℝ) (h : History X n) : History X n :=
  fun i => ((h i).1, (h i).2 + c)

theorem responseOrder_shift {X : Type} {n : ℕ} (c : ℝ) (h : History X n) :
    responseOrder (shiftedValueHistory c h) = responseOrder h := by
  funext i j
  simp only [responseOrder, shiftedValueHistory, add_le_add_iff_right]

theorem comparisonHistoryPolicy_transcript_shift {X : Type}
    (q o : ∀ n, ResponseOrder n → X) (f : X → ℝ) (c : ℝ) (n : ℕ) :
    (comparisonHistoryPolicy q o).transcript (fun x => f x + c) () n =
      shiftedValueHistory c ((comparisonHistoryPolicy q o).transcript f () n) := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    dsimp only [comparisonHistoryPolicy] at ih
    simp only [HistoryPolicy.transcript, comparisonHistoryPolicy, ih, responseOrder_shift]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, shiftedValueHistory]
    · simp only [Fin.snoc_castSucc, shiftedValueHistory]

theorem comparisonHistoryPolicy_result_shift {X : Type}
    (q o : ∀ n, ResponseOrder n → X) (f : X → ℝ) (c : ℝ) (n : ℕ) :
    (comparisonHistoryPolicy q o).result (fun x => f x + c) () n =
      (comparisonHistoryPolicy q o).result f () n := by
  unfold HistoryPolicy.result
  rw [comparisonHistoryPolicy_transcript_shift]
  simp only [comparisonHistoryPolicy, responseOrder_shift]

theorem comparisonHistoryPolicy_legal_state {X : Type} [MeasurableSpace X]
    [StandardBorelSpace X] (q o : ∀ n, ResponseOrder n → X) (T : ℕ) (x0 : X) :
    StandardBorelSpace (HistoryStore X) ∧
      ((comparisonHistoryPolicy q o).toState T x0).IsMeasurable ∧
      ∀ f : X → ℝ, ((comparisonHistoryPolicy q o).toState T x0).result f () T =
        (comparisonHistoryPolicy q o).result f () T :=
  ⟨inferInstance, history_toState_measurable (comparisonHistoryPolicy_measurable q o) T x0,
    fun f => history_toState_result _ T x0 f ()⟩

end
end Nonsmooth
