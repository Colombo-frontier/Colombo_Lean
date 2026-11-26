import NCConcave16991.DenseSmoothRevelationCache

/-! # Future-stage independence as an exact deterministic prefix identity -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open Set MeasureTheory

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

def prefixView (j : Fin (T + 1)) (s : State E n T hn ρ hρ) : Option (State E n T hn ρ hρ) :=
  if frontier E n T hn ρ hρ s < j.val then some s else none

def SamePrefix (j : Fin (T + 1)) (A B : Table E n T ρ) : Prop :=
  ∀ l : Fin (T + 1), l.val < j.val → A.direction l = B.direction l ∧ ∀ i, A.row i l = B.row i l

theorem completion_eq_of_prefix (seed : Ω) (j : Fin (T + 1)) (A B : Table E n T ρ)
    (hAB : SamePrefix E n T ρ j A B) (s : State E n T hn ρ hρ)
    (hs : frontier E n T hn ρ hρ s < j.val) :
    completion E n T hn ρ hρ P seed A s = completion E n T hn ρ hρ P seed B s := by
  have hf : frontier E n T hn ρ hρ s < T + 1 := hs.trans j.isLt
  have hidx : (stageIndex E n T hn ρ hρ s).val < j.val := (Nat.mod_eq_of_lt hf).le.trans_lt hs
  unfold completion
  cases action E n T hn ρ hρ P seed s with
  | inl x => rfl
  | inr o =>
      simp only [Sum.elim_inr, hf, ite_true]
      have he : coordinate A.direction ((primalCoordinates E T).symm o.2.1) (stageIndex E n T hn ρ hρ s) =
          coordinate B.direction ((primalCoordinates E T).symm o.2.1) (stageIndex E n T hn ρ hρ s) := by
        unfold coordinate
        rw [(hAB _ hidx).1]
      simp only [he]

theorem prefix_step_same_state (seed : Ω) (j : Fin (T + 1)) (A B : Table E n T ρ)
    (hAB : SamePrefix E n T ρ j A B) (s : State E n T hn ρ hρ)
    (hs : frontier E n T hn ρ hρ s < j.val) :
    prefixView E n T hn ρ hρ j (stepWithTable E n T hn ρ hρ P seed A s) =
      prefixView E n T hn ρ hρ j (stepWithTable E n T hn ρ hρ P seed B s) := by
  have hf : frontier E n T hn ρ hρ s < T + 1 := hs.trans j.isLt
  have hidx : (stageIndex E n T hn ρ hρ s).val < j.val := (Nat.mod_eq_of_lt hf).le.trans_lt hs
  have hc := completion_eq_of_prefix E n T hn ρ hρ P seed j A B hAB s hs
  cases ha : action E n T hn ρ hρ P seed s with
  | inl x => simp only [stepWithTable, step, ha, Sum.elim_inl]
  | inr o =>
      rw [stepWithTable_query E n T hn ρ hρ P seed A s o ha,
        stepWithTable_query E n T hn ρ hρ P seed B s o ha, hc]
      cases hd : completion E n T hn ρ hρ P seed B s with
      | false =>
          rw [(hAB _ hidx).2 o.1]
          simp only [paidQuery, hf, ite_true, Bool.false_eq_true, ite_false]
      | true =>
          by_cases hnxt : frontier E n T hn ρ hρ s + 1 < j.val
          · have hv : (successorIndex E n T hn ρ hρ s).val < j.val := by
              rw [successorIndex]
              simp only [Nat.mod_eq_of_lt (hnxt.trans j.isLt)]
              exact hnxt
            have hrows : (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s)) =
                (fun i ↦ B.row i (stageIndex E n T hn ρ hρ s)) := funext (hAB _ hidx).2
            rw [(hAB _ hidx).1, (hAB _ hidx).2 o.1, hrows, (hAB _ hv).2 o.1]
          · have hnewA : frontier E n T hn ρ hρ
                (paidQuery E n T hn ρ hρ s o (A.row o.1 (stageIndex E n T hn ρ hρ s)) true
                  (A.direction (stageIndex E n T hn ρ hρ s)) (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s))
                  (A.row o.1 (successorIndex E n T hn ρ hρ s))) = frontier E n T hn ρ hρ s + 1 := by
              rw [paidQuery_frontier, if_pos ⟨hf, rfl⟩]
            have hnewB : frontier E n T hn ρ hρ
                (paidQuery E n T hn ρ hρ s o (B.row o.1 (stageIndex E n T hn ρ hρ s)) true
                  (B.direction (stageIndex E n T hn ρ hρ s)) (fun i ↦ B.row i (stageIndex E n T hn ρ hρ s))
                  (B.row o.1 (successorIndex E n T hn ρ hρ s))) = frontier E n T hn ρ hρ s + 1 := by
              rw [paidQuery_frontier, if_pos ⟨hf, rfl⟩]
            simp only [prefixView, hnewA, hnewB, hnxt, ite_false]

theorem prefix_step_eq (seed : Ω) (j : Fin (T + 1)) (A B : Table E n T ρ)
    (hAB : SamePrefix E n T ρ j A B) (s t : State E n T hn ρ hρ)
    (hst : prefixView E n T hn ρ hρ j s = prefixView E n T hn ρ hρ j t) :
    prefixView E n T hn ρ hρ j (stepWithTable E n T hn ρ hρ P seed A s) =
      prefixView E n T hn ρ hρ j (stepWithTable E n T hn ρ hρ P seed B t) := by
  by_cases hs : frontier E n T hn ρ hρ s < j.val
  · have ht : frontier E n T hn ρ hρ t < j.val := by
      by_contra h
      simp only [prefixView, hs, h, ite_true, ite_false] at hst
      cases hst
    have he : s = t := Option.some.inj (by simpa only [prefixView, hs, ht, ite_true] using hst)
    subst t
    exact prefix_step_same_state E n T hn ρ hρ P seed j A B hAB s hs
  · have ht : ¬ frontier E n T hn ρ hρ t < j.val := by
      intro h
      simp only [prefixView, hs, h, ite_true, ite_false] at hst
      cases hst
    have hsa : frontier E n T hn ρ hρ s ≤ frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s) := by
      unfold stepWithTable
      exact (step_frontier_bounds E n T hn ρ hρ P seed s _ _ _ _ _).1
    have htb : frontier E n T hn ρ hρ t ≤ frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed B t) := by
      unfold stepWithTable
      exact (step_frontier_bounds E n T hn ρ hρ P seed t _ _ _ _ _).1
    simp only [prefixView, if_neg (by omega : ¬ frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s) < j.val),
      if_neg (by omega : ¬ frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed B t) < j.val)]

theorem run_prefix_eq (seed : Ω) (j : Fin (T + 1)) (A B : Table E n T ρ)
    (hAB : SamePrefix E n T ρ j A B) (t : ℕ) :
    prefixView E n T hn ρ hρ j (runWithTable E n T hn ρ hρ P seed A t) =
      prefixView E n T hn ρ hρ j (runWithTable E n T hn ρ hρ P seed B t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [runWithTable, runWithTable]; exact prefix_step_eq E n T hn ρ hρ P seed j A B hAB _ _ ih

end

end NCConcave16991.DenseSmooth.Revelation
