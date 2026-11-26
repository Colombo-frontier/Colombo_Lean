import NCConcave16991.DenseSmoothRevelationPrefix
import NCConcave16991.DenseSmoothRevelationCosts

/-! # A stage entrance depends on its one initialization row only -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)

def entryStart (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a direction : E) (rows : Fin n → E) (init : E) : State E n T hn ρ hρ :=
  paidQuery E n T hn ρ hρ s o a true direction rows init

theorem entryStart_seen (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a direction : E) (rows : Fin n → E)
    (hf : frontier E n T hn ρ hρ s + 1 < T + 1) (init : E) :
    (entryStart E n T hn ρ hρ s o a direction rows init).base.progress.2 = {o.1} := by
  have hf' : frontier E n T hn ρ hρ s < T + 1 := by omega
  simp only [entryStart,paidQuery,hf',ite_true,hf]

theorem entryStart_frontier (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a direction : E) (rows : Fin n → E) (init : E)
    (hf : frontier E n T hn ρ hρ s < T + 1) :
    frontier E n T hn ρ hρ (entryStart E n T hn ρ hρ s o a direction rows init) =
      frontier E n T hn ρ hρ s + 1 := by
  rw [entryStart,paidQuery_frontier,if_pos ⟨hf,rfl⟩]

theorem entryStart_cost_zero (s : State E n T hn ρ hρ)
    (hs : FutureZero E n T hn ρ hρ s) (o : Query E n T hn ρ hρ)
    (a direction : E) (rows : Fin n → E)
    (hf : frontier E n T hn ρ hρ s + 1 < T + 1) (init : E) :
    (entryStart E n T hn ρ hρ s o a direction rows init).assigned
      (successorIndex E n T hn ρ hρ s) = 0 :=
  paidQuery_entry_cost_zero E n T hn ρ hρ s hs o a direction rows init hf

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension E T) Ω)

theorem stepWithTable_eq_entry (seed : Ω) (A : Table E n T ρ)
    (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (ho : action E n T hn ρ hρ P seed s = .inr o)
    (hc : completion E n T hn ρ hρ P seed A s = true) :
    stepWithTable E n T hn ρ hρ P seed A s =
      entryStart E n T hn ρ hρ s o
        (A.row o.1 (stageIndex E n T hn ρ hρ s))
        (A.direction (stageIndex E n T hn ρ hρ s))
        (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s))
        (A.row o.1 (successorIndex E n T hn ρ hρ s)) := by
  rw [stepWithTable_query E n T hn ρ hρ P seed A s o ho,hc]
  rfl

theorem run_frontier_mono (seed : Ω) (A : Table E n T ρ) :
    Monotone (fun t ↦ frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t)) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [runWithTable,stepWithTable]
  exact (step_frontier_bounds E n T hn ρ hρ P seed _ _ _ _ _ _).1

theorem run_assigned_past_stable (seed : Ω) (A : Table E n T ρ)
    (j : Fin (T + 1)) (t u : ℕ) (htu : t ≤ u)
    (hj : j.val < frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t)) :
    (runWithTable E n T hn ρ hρ P seed A u).assigned j =
      (runWithTable E n T hn ρ hρ P seed A t).assigned j := by
  induction u,htu using Nat.le_induction with
  | base => rfl
  | succ u htu ih =>
      have hju : j.val < frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A u) :=
        hj.trans_le (run_frontier_mono E n T hn ρ hρ P seed A htu)
      rw [runWithTable,stepWithTable,step_assigned_past E n T hn ρ hρ P seed _ _ _ _ _ _ j hju,ih]

end
end NCConcave16991.DenseSmooth.Revelation
