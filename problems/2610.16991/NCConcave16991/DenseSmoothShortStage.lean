import NCConcave16991.DenseSmoothFirstEntry
import NCConcave16991.DenseSmoothRevelationCensor

/-! # Actual completed-stage costs and its alignment-free precompletion path -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension E T) Ω)

theorem completion_true_frontier (seed : Ω) (A : Table E n T ρ)
    (s : State E n T hn ρ hρ) (hc : completion E n T hn ρ hρ P seed A s = true) :
    frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s) =
      frontier E n T hn ρ hρ s + 1 := by
  cases ha : action E n T hn ρ hρ P seed s with
  | inl x => simp only [completion,ha,Sum.elim_inl,Bool.false_eq_true] at hc
  | inr o =>
      have hf : frontier E n T hn ρ hρ s < T + 1 := by
        by_contra h
        simp only [completion,ha,Sum.elim_inr,h,ite_false,Bool.false_eq_true] at hc
      rw [stepWithTable_query E n T hn ρ hρ P seed A s o ha,hc,paidQuery_frontier,if_pos ⟨hf,rfl⟩]

theorem runFromTable_shift (seed : Ω) (A : Table E n T ρ) (e q : ℕ) :
    runFromTable E n T hn ρ hρ P seed A (runWithTable E n T hn ρ hρ P seed A e) q =
      runWithTable E n T hn ρ hρ P seed A (e + q) := by
  induction q with
  | zero => rfl
  | succ q ih => rw [runFromTable,ih,Nat.add_succ,runWithTable]

theorem same_stage_eq_censored (seed : Ω) (A : Table E n T ρ)
    (j : Fin (T + 1)) (e u : ℕ) (heu : e ≤ u)
    (he : frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A e) = j.val)
    (hu : frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A u) = j.val) :
    runWithTable E n T hn ρ hρ P seed A u =
      censoredRunFrom E n T hn ρ hρ P seed (fun i ↦ A.row i j)
        (runWithTable E n T hn ρ hρ P seed A e) (u - e) := by
  have hsum : e + (u - e) = u := Nat.add_sub_of_le heu
  have hno : ∀ t < u - e, completion E n T hn ρ hρ P seed A
      (runFromTable E n T hn ρ hρ P seed A (runWithTable E n T hn ρ hρ P seed A e) t) = false := by
    intro t ht
    rw [runFromTable_shift]
    have hlow := run_frontier_mono E n T hn ρ hρ P seed A (show e ≤ e + t by omega)
    have hhigh := run_frontier_mono E n T hn ρ hρ P seed A (show e + t + 1 ≤ u by omega)
    change frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A e) ≤
      frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A (e + t)) at hlow
    change frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A (e + t + 1)) ≤
      frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A u) at hhigh
    cases hc : completion E n T hn ρ hρ P seed A (runWithTable E n T hn ρ hρ P seed A (e + t)) with
    | false => rfl
    | true =>
        have hi := completion_true_frontier E n T hn ρ hρ P seed A _ hc
        change frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A (e + t + 1)) = _ at hi
        omega
  have hh := runFrom_eq_censored E n T hn ρ hρ P seed A _ j he (u - e) hno
  rwa [runFromTable_shift,hsum] at hh

theorem completed_stage_witness (seed : Ω) (A : Table E n T ρ) (j : Fin T) (N : ℕ)
    (hN : j.val < frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A N)) :
    ∃ u < N,
      frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A u) = j.val ∧
      completion E n T hn ρ hρ P seed A (runWithTable E n T hn ρ hρ P seed A u) = true ∧
      (runWithTable E n T hn ρ hρ P seed A N).assigned j.castSucc =
        (runWithTable E n T hn ρ hρ P seed A u).assigned j.castSucc + 1 := by
  obtain ⟨u,hu,hfirst⟩ := exists_firstEntry E n T hn ρ hρ P seed A j.succ (by simp) N (by simpa using hN)
  obtain ⟨hf,o,ho,hc⟩ := firstEntry_details E n T hn ρ hρ P seed A j.succ u hfirst
  have hfu : frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A u) = j.val := by
    simpa only [Fin.val_succ] using Nat.add_right_cancel hf
  have hv : frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A u) < T + 1 := by
    rw [hfu]
    omega
  have hi : stageIndex E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A u) = j.castSucc := by
    apply Fin.ext
    exact (Nat.mod_eq_of_lt hv).trans hfu
  have hpost := completion_true_frontier E n T hn ρ hρ P seed A _ hc
  change frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A (u + 1)) = _ at hpost
  have hcost : (runWithTable E n T hn ρ hρ P seed A (u + 1)).assigned j.castSucc =
      (runWithTable E n T hn ρ hρ P seed A u).assigned j.castSucc + 1 := by
    rw [runWithTable,stepWithTable_query E n T hn ρ hρ P seed A _ o ho]
    simpa only [hi] using paidQuery_assigned_current E n T hn ρ hρ _ o _ _ _ _ _ hv
  refine ⟨u,hu,hfu,hc,?_⟩
  have hjpost : j.castSucc.val < frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A (u + 1)) := by
    change j.val < _
    rw [hpost,hfu]
    omega
  rw [run_assigned_past_stable E n T hn ρ hρ P seed A j.castSucc (u + 1) N (by omega) hjpost,hcost]

end
end NCConcave16991.DenseSmooth.Revelation
