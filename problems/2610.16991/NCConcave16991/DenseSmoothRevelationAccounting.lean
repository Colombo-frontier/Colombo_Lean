import NCConcave16991.DenseSmoothRevelationState

/-! # Actual assigned-call costs and one-stage censored continuations -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open Set MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)

theorem sum_increment (cost : Fin (T + 1) → ℕ) (j : Fin (T + 1)) :
    (∑ k, Function.update cost j (cost j + 1) k) = (∑ k, cost k) + 1 := by
  have he : Function.update cost j (cost j + 1) = fun k ↦ cost k + if k = j then 1 else 0 := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  rw [he, Finset.sum_add_distrib]
  simp

theorem paidQuery_assigned (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a : E) (complete : Bool) (direction : E) (releasedRows : Fin n → E) (init : E) :
    (paidQuery E n T hn ρ hρ s o a complete direction releasedRows init).assigned =
      if frontier E n T hn ρ hρ s < T + 1 then
        Function.update s.assigned (stageIndex E n T hn ρ hρ s)
          (s.assigned (stageIndex E n T hn ρ hρ s) + 1) else s.assigned := by
  cases complete <;> by_cases hf : frontier E n T hn ρ hρ s < T + 1 <;>
    simp only [paidQuery, hf, ite_true, ite_false, Bool.false_eq_true]

theorem paidQuery_frontier (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a : E) (complete : Bool) (direction : E) (releasedRows : Fin n → E) (init : E) :
    frontier E n T hn ρ hρ (paidQuery E n T hn ρ hρ s o a complete direction releasedRows init) =
      if frontier E n T hn ρ hρ s < T + 1 ∧ complete = true then frontier E n T hn ρ hρ s + 1
      else frontier E n T hn ρ hρ s := by
  cases complete <;> by_cases hf : frontier E n T hn ρ hρ s < T + 1 <;>
    simp only [paidQuery, hf, ite_true, ite_false, Bool.false_eq_true, and_false, and_true] <;> rfl

theorem paidQuery_frontier_bounds (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a : E) (complete : Bool) (direction : E) (releasedRows : Fin n → E) (init : E) :
    frontier E n T hn ρ hρ s ≤
      frontier E n T hn ρ hρ (paidQuery E n T hn ρ hρ s o a complete direction releasedRows init) ∧
    frontier E n T hn ρ hρ (paidQuery E n T hn ρ hρ s o a complete direction releasedRows init) ≤
      frontier E n T hn ρ hρ s + 1 := by
  rw [paidQuery_frontier]
  split_ifs <;> omega


variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

theorem step_frontier_bounds (seed : Ω) (s : State E n T hn ρ hρ) (a : E) (complete : Bool)
    (direction : E) (releasedRows : Fin n → E) (init : E) :
    frontier E n T hn ρ hρ s ≤ frontier E n T hn ρ hρ (step E n T hn ρ hρ P seed s a complete direction releasedRows init) ∧
    frontier E n T hn ρ hρ (step E n T hn ρ hρ P seed s a complete direction releasedRows init) ≤
      frontier E n T hn ρ hρ s + 1 := by
  unfold step
  cases action E n T hn ρ hρ P seed s with
  | inl x => exact ⟨le_rfl, Nat.le_succ _⟩
  | inr o => exact paidQuery_frontier_bounds E n T hn ρ hρ s o a complete direction releasedRows init

theorem run_frontier_le (seed : Ω) (A : Table E n T ρ) (t : ℕ) :
    frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t) ≤ t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
      rw [runWithTable, stepWithTable]
      exact (step_frontier_bounds E n T hn ρ hρ P seed _ _ _ _ _ _).2.trans (Nat.add_le_add_right ih 1)

theorem step_assigned_sum_le (seed : Ω) (s : State E n T hn ρ hρ) (a : E) (complete : Bool)
    (direction : E) (releasedRows : Fin n → E) (init : E) :
    (∑ j, (step E n T hn ρ hρ P seed s a complete direction releasedRows init).assigned j) ≤
      (∑ j, s.assigned j) + 1 := by
  unfold step
  cases action E n T hn ρ hρ P seed s with
  | inl x => exact Nat.le_succ _
  | inr o =>
      simp only [Sum.elim_inr]
      rw [paidQuery_assigned]
      split_ifs
      · exact (sum_increment T s.assigned _).le
      · exact Nat.le_succ _

theorem run_assigned_sum_le (seed : Ω) (A : Table E n T ρ) (t : ℕ) :
    (∑ j, (runWithTable E n T hn ρ hρ P seed A t).assigned j) ≤ t := by
  induction t with
  | zero => simp [runWithTable, initial]
  | succ t ih =>
      rw [runWithTable, stepWithTable]
      exact (step_assigned_sum_le E n T hn ρ hρ P seed _ _ _ _ _ _).trans (Nat.add_le_add_right ih 1)

theorem run_assigned_prefix_le (seed : Ω) (A : Table E n T ρ) (t : ℕ) :
    (∑ j : Fin T, (runWithTable E n T hn ρ hρ P seed A t).assigned j.castSucc) ≤ t := by
  have hh := run_assigned_sum_le E n T hn ρ hρ P seed A t
  rw [Fin.sum_univ_castSucc] at hh
  omega


theorem precompletionStep_frontier (seed : Ω) (s : State E n T hn ρ hρ) (a : E) :
    frontier E n T hn ρ hρ (precompletionStep E n T hn ρ hρ P seed s a) = frontier E n T hn ρ hρ s := by
  unfold precompletionStep step
  cases action E n T hn ρ hρ P seed s with
  | inl x => rfl
  | inr o => simp only [Sum.elim_inr]; rw [paidQuery_frontier]; simp

theorem paidQuery_noncompletion (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a direction init : E) (rows : Fin n → E) :
    paidQuery E n T hn ρ hρ s o a false direction rows init =
      paidQuery E n T hn ρ hρ s o a false 0 (fun _ ↦ 0) 0 := by
  by_cases hf : frontier E n T hn ρ hρ s < T + 1 <;>
    simp only [paidQuery, hf, ite_true, ite_false, Bool.false_eq_true]

theorem step_noncompletion (seed : Ω) (s : State E n T hn ρ hρ) (a direction init : E) (rows : Fin n → E) :
    step E n T hn ρ hρ P seed s a false direction rows init =
      precompletionStep E n T hn ρ hρ P seed s a := by
  have he : (fun o : Query E n T hn ρ hρ ↦ paidQuery E n T hn ρ hρ s o a false direction rows init) =
      (fun o ↦ paidQuery E n T hn ρ hρ s o a false 0 (fun _ ↦ 0) 0) :=
    funext (fun o ↦ paidQuery_noncompletion E n T hn ρ hρ s o a direction init rows)
  unfold precompletionStep step
  rw [he]

theorem stepWithTable_noncompletion (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (hc : completion E n T hn ρ hρ P seed A s = false) :
    stepWithTable E n T hn ρ hρ P seed A s = precompletionStep E n T hn ρ hρ P seed s
      ((request E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1)) := by
  unfold stepWithTable
  rw [hc, step_noncompletion]


def censoredRunFrom (seed : Ω) (row : Fin n → E) (s : State E n T hn ρ hρ) : ℕ → State E n T hn ρ hρ
  | 0 => s
  | t + 1 =>
      let st := censoredRunFrom seed row s t
      precompletionStep E n T hn ρ hρ P seed st
        ((request E n T hn ρ hρ P seed st).elim 0 (fun ji ↦ row ji.2))

theorem censoredRunFrom_frontier (seed : Ω) (row : Fin n → E) (s : State E n T hn ρ hρ) (t : ℕ) :
    frontier E n T hn ρ hρ (censoredRunFrom E n T hn ρ hρ P seed row s t) = frontier E n T hn ρ hρ s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [censoredRunFrom, precompletionStep_frontier, ih]

end

end NCConcave16991.DenseSmooth.Revelation
