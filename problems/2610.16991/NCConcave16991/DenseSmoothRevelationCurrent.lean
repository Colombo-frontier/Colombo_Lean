import NCConcave16991.DenseSmoothRevelationCache
import NCConcave16991.DenseSmoothRevelationFresh

/-! # Actual current-row cache truth at every initialization and query -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open Set MeasureTheory

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)

theorem paidQuery_currentCorrect (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (hs : CurrentCorrect E n T hn ρ hρ A s) (o : Query E n T hn ρ hρ) (complete : Bool) :
    CurrentCorrect E n T hn ρ hρ A
      (paidQuery E n T hn ρ hρ s o (A.row o.1 (stageIndex E n T hn ρ hρ s)) complete
        (A.direction (stageIndex E n T hn ρ hρ s)) (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s))
        (A.row o.1 (successorIndex E n T hn ρ hρ s))) := by
  intro j hj i hi
  have hj' : j.val = frontier E n T hn ρ hρ
      (paidQuery E n T hn ρ hρ s o (A.row o.1 (stageIndex E n T hn ρ hρ s)) complete
        (A.direction (stageIndex E n T hn ρ hρ s)) (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s))
        (A.row o.1 (successorIndex E n T hn ρ hρ s))) := hj
  by_cases hf : s.base.progress.1 < T + 1
  · cases complete with
    | false =>
        simp only [paidQuery, frontier, hf, ite_true, Bool.false_eq_true, ite_false] at hi ⊢
        rw [paidQuery_frontier, if_neg (by simp)] at hj'
        by_cases hie : i = o.1
        · subst i
          simpa only [paidQuery, frontier, hf, ite_true, Bool.false_eq_true, ite_false] using
            paidQuery_selected_row E n T hn ρ hρ A s o false j hj
        · have hstage : j = stageIndex E n T hn ρ hρ s := by
            apply Fin.ext
            exact hj'.trans (Nat.mod_eq_of_lt hf).symm
          subst j
          simp only [ConeReferenceCache.putRow, Function.update_self, Function.update_of_ne hie]
          exact hs _ hj' i ((Finset.mem_insert.mp hi).resolve_left hie)
    | true =>
        by_cases hnext : s.base.progress.1 + 1 < T + 1
        · have hi' : i = o.1 := by
            simpa only [paidQuery, frontier, hf, hnext, ite_true, Finset.mem_singleton] using hi
          subst i
          exact paidQuery_selected_row E n T hn ρ hρ A s o true j hj
        · simp only [paidQuery, frontier, hf, hnext, ite_true, ite_false] at hi
          simp at hi
  · simp only [paidQuery, frontier, hf, ite_false] at hj hi ⊢
    exact hs j hj i hi

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

theorem run_currentCorrect (seed : Ω) (A : Table E n T ρ) (t : ℕ) :
    CurrentCorrect E n T hn ρ hρ A (runWithTable E n T hn ρ hρ P seed A t) := by
  induction t with
  | zero => intro j hj i hi; simp [runWithTable, initial, Machine.initial, Counter.initial] at hi
  | succ t ih =>
      rw [runWithTable]
      cases ha : action E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed A t) with
      | inl x =>
          intro j hj i hi
          simp only [stepWithTable, step, ha, Sum.elim_inl] at hj hi ⊢
          exact ih j hj i hi
      | inr o =>
          rw [stepWithTable_query E n T hn ρ hρ P seed A _ o ha]
          exact paidQuery_currentCorrect E n T hn ρ hρ A _ ih o _

end

end NCConcave16991.DenseSmooth.Revelation
