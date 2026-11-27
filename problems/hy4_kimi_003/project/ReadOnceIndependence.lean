import ModelFull

open MeasureTheory

namespace Task006.Full
namespace OracleAlgorithm

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def queriedBefore (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (handle t : ℕ) : Prop :=
  ∃ i : Fin N, i.val < t ∧
    (A.executedAction F tape seed i).map Prod.fst = some handle

lemma queriedBefore_zero (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (handle : ℕ) :
    ¬ A.queriedBefore F tape seed handle 0 := by
  rintro ⟨i, hi, _⟩
  omega

lemma queriedBefore_succ (A : OracleAlgorithm d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (handle t : ℕ) (ht : t < N) :
    A.queriedBefore F tape seed handle (t+1) ↔
      A.queriedBefore F tape seed handle t ∨
        (A.executedAction F tape seed ⟨t,ht⟩).map Prod.fst = some handle := by
  constructor
  · rintro ⟨i,hi,hq⟩
    by_cases hit : i.val < t
    · exact Or.inl ⟨i,hit,hq⟩
    · right
      have he : i = ⟨t,ht⟩ := by apply Fin.ext; change i.val = t; omega
      simpa only [he] using hq
  · rintro (⟨i,hi,hq⟩ | hq)
    · exact ⟨i,by omega,hq⟩
    · exact ⟨⟨t,ht⟩,by simp,hq⟩

lemma scalarReply_eq_of_agree_off {F : Space d → Ω → ℝ}
    {tape tape' : ℕ → Ω} {handle : ℕ}
    (hoff : ∀ k, k ≠ handle → tape k = tape' k)
    {a : QueryAction d} (ha : a.map Prod.fst ≠ some handle) :
    scalarReply F tape a = scalarReply F tape' a := by
  cases a with
  | none => rfl
  | some q =>
    rcases q with ⟨k,x⟩
    have hk : k ≠ handle := by
      intro h
      subst k
      exact ha rfl
    simp only [scalarReply, hoff k hk]

/-- Before the first paid query to h, changing its hidden sample has no effect.
The event that h is ever queried is consequently independent of that sample.
This statement is deterministic and permits arbitrary adaptive policies. -/
theorem exploration_agrees_until_first_read (A : OracleAlgorithm d N S)
    (F : Space d → Ω → ℝ) (tape tape' : ℕ → Ω) (seed : S) (handle : ℕ)
    (hoff : ∀ k, k ≠ handle → tape k = tape' k) :
    ∀ t, t ≤ N →
      (A.queriedBefore F tape seed handle t ↔ A.queriedBefore F tape' seed handle t) ∧
      (¬ A.queriedBefore F tape seed handle t →
        A.runPrefix F tape seed t = A.runPrefix F tape' seed t) := by
  intro t
  induction t with
  | zero =>
    intro ht
    constructor
    · exact iff_of_false (queriedBefore_zero A F tape seed handle)
        (queriedBefore_zero A F tape' seed handle)
    · intro _; rfl
  | succ t ih =>
    intro htN
    have ht : t < N := by omega
    have hp := ih (by omega : t ≤ N)
    by_cases hprev : A.queriedBefore F tape seed handle t
    · have hprev' := hp.1.mp hprev
      constructor
      · rw [queriedBefore_succ A F tape seed handle t ht,
          queriedBefore_succ A F tape' seed handle t ht]
        simp only [hprev,hprev',true_or]
      · intro hn
        exact False.elim (hn ((queriedBefore_succ A F tape seed handle t ht).mpr (Or.inl hprev)))
    · have hprev' : ¬ A.queriedBefore F tape' seed handle t := by
        intro h; exact hprev (hp.1.mpr h)
      have hh := hp.2 hprev
      have hact : A.executedAction F tape seed ⟨t,ht⟩ =
          A.executedAction F tape' seed ⟨t,ht⟩ := by
        change A.action ⟨t,ht⟩ seed (A.runPrefix F tape seed t) =
          A.action ⟨t,ht⟩ seed (A.runPrefix F tape' seed t)
        rw [hh]
      constructor
      · rw [queriedBefore_succ A F tape seed handle t ht,
          queriedBefore_succ A F tape' seed handle t ht, hact]
        simp only [hprev,hprev',false_or]
      · intro hn
        have hcur : (A.executedAction F tape seed ⟨t,ht⟩).map Prod.fst ≠ some handle := by
          intro h
          exact hn ((queriedBefore_succ A F tape seed handle t ht).mpr (Or.inr h))
        have hr := scalarReply_eq_of_agree_off (F := F) hoff hcur
        simp only [runPrefix, dif_pos ht]
        change Function.update (A.runPrefix F tape seed t) ⟨t,ht⟩
            (scalarReply F tape (A.executedAction F tape seed ⟨t,ht⟩)) =
          Function.update (A.runPrefix F tape' seed t) ⟨t,ht⟩
            (scalarReply F tape' (A.executedAction F tape' seed ⟨t,ht⟩))
        rw [← hact, hr, hh]

/-- The event of ever accessing a handle is invariant under resampling only
that handle. It does not reveal its status before the first paid query. -/
theorem queriedBefore_update_iff (A : OracleAlgorithm d N S)
    (F : Space d → Ω → ℝ) (tape : ℕ → Ω) (seed : S) (handle : ℕ) (z : Ω) :
    A.queriedBefore F tape seed handle N ↔
      A.queriedBefore F (Function.update tape handle z) seed handle N := by
  exact (exploration_agrees_until_first_read A F tape (Function.update tape handle z) seed handle
    (by intro k hk; simp [Function.update_of_ne hk]) N le_rfl).1

end OracleAlgorithm
end Task006.Full
