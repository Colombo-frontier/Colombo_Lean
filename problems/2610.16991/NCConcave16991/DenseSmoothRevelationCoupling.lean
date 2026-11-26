import NCConcave16991.DenseSmoothRevelationCache
import NCConcave16991.DenseSmoothMachineCoupling

/-! # Pathwise coupling under future-stage flatness, including arbitrary outputs -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open Set MeasureTheory

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 4

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

def FutureQueryGood (A : Table E n T ρ) (f : ℕ) (o : Query E n T hn ρ hρ) : Prop :=
  ∀ j : Fin T, f < j.val → coordinate A.direction ((primalCoordinates E T).symm o.2.1) j.castSucc ≤ 5 / 32

def FutureGoodBefore (seed : Ω) (A : Table E n T ρ) (N : ℕ) : Prop :=
  ∀ t < N, ∀ o : Query E n T hn ρ hρ,
    action E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed A t) = Sum.inr o →
    FutureQueryGood E n T hn ρ hρ A (frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t)) o

theorem post_frontier_flat (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (o : Query E n T hn ρ hρ) (ha : action E n T hn ρ hρ P seed s = Sum.inr o)
    (hfuture : FutureQueryGood E n T hn ρ hρ A (frontier E n T hn ρ hρ s) o) :
    ∀ j : Fin T, frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s) ≤ j.val →
      coordinate A.direction ((primalCoordinates E T).symm o.2.1) j.castSucc ≤ 5 / 32 := by
  intro j hj
  rw [stepWithTable_query E n T hn ρ hρ P seed A s o ha, paidQuery_frontier] at hj
  by_cases hf : frontier E n T hn ρ hρ s < T + 1
  · cases hc : completion E n T hn ρ hρ P seed A s with
    | true =>
        rw [if_pos ⟨hf, hc⟩] at hj
        exact hfuture j (by omega)
    | false =>
        rw [if_neg (by simp [hc])] at hj
        by_cases hjf : frontier E n T hn ρ hρ s < j.val
        · exact hfuture j hjf
        · have he : j.castSucc = stageIndex E n T hn ρ hρ s := by
            apply Fin.ext
            change j.val = frontier E n T hn ρ hρ s % (T + 1)
            rw [Nat.mod_eq_of_lt hf]
            omega
          have hnot : ¬(5 / 32 : ℝ) < coordinate A.direction ((primalCoordinates E T).symm o.2.1)
              (stageIndex E n T hn ρ hρ s) := by
            simpa only [completion, ha, Sum.elim_inr, hf, ite_true, decide_eq_false_iff_not] using hc
          rw [he]
          exact le_of_not_gt hnot
  · rw [if_neg (by tauto)] at hj
    omega

theorem step_control_eq_actual (seed : Ω) (hρ1 : ρ ≤ 1) (A : Table E n T ρ)
    (s : State E n T hn ρ hρ) (hs : PastCorrect E n T hn ρ hρ A s)
    (hfuture : ∀ o, action E n T hn ρ hρ P seed s = Sum.inr o →
      FutureQueryGood E n T hn ρ hρ A (frontier E n T hn ρ hρ s) o) :
    (stepWithTable E n T hn ρ hρ P seed A s).base.control =
      Machine.policyControlStep E n T hn ρ hρ P (oracleResponse (finiteSum hn hρ hρ1 A).toProblem) seed s.base.control := by
  cases ha : action E n T hn ρ hρ P seed s with
  | inl x =>
      have ha' : OracleSimulation.action (Domain n T hn ρ hρ) P seed s.base.control = Sum.inl x := ha
      simp only [stepWithTable, step, action, ha', Sum.elim_inl, Machine.policyControlStep]
  | inr o =>
      have hpost := paidQuery_pastCorrect E n T hn ρ hρ A s hs o
        (A.row o.1 (stageIndex E n T hn ρ hρ s)) (A.row o.1 (successorIndex E n T hn ρ hρ s))
        (completion E n T hn ρ hρ P seed A s)
      rw [← stepWithTable_query E n T hn ρ hρ P seed A s o ha] at hpost
      have hselected (j : Fin (T + 1)) (hj : j.val = frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s)) :
          (stepWithTable E n T hn ρ hρ P seed A s).base.rows j o.1 = A.row o.1 j := by
        rw [stepWithTable_query E n T hn ρ hρ P seed A s o ha] at hj ⊢
        exact paidQuery_selected_row E n T hn ρ hρ A s o _ j hj
      have hrows : ∀ j : Fin (T + 1), j.val ≤ frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s) →
          A.row o.1 j = (stepWithTable E n T hn ρ hρ P seed A s).base.rows j o.1 := by
        intro j hj
        by_cases hjlt : j.val < frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s)
        · exact ((hpost j hjlt).1 o.1).symm
        · exact (hselected j (by omega)).symm
      have horacle := oracleResponse_eq_reference hn hρ hρ1 A
        (frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s))
        (stepWithTable E n T hn ρ hρ P seed A s).base.directions
        (fun i j ↦ (stepWithTable E n T hn ρ hρ P seed A s).base.rows j i) o
        (fun j hj ↦ (hpost j hj).2.symm) hrows
        (post_frontier_flat E n T hn ρ hρ P seed A s o ha (hfuture o ha))
      have hc := paidQuery_control E n T hn ρ hρ s o (A.row o.1 (stageIndex E n T hn ρ hρ s))
        (completion E n T hn ρ hρ P seed A s) (A.direction (stageIndex E n T hn ρ hρ s))
        (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s)) (A.row o.1 (successorIndex E n T hn ρ hρ s))
      rw [← stepWithTable_query E n T hn ρ hρ P seed A s o ha] at hc
      rw [hc, ← horacle]
      change _ = (action E n T hn ρ hρ P seed s).elim Sum.inl _
      rw [ha]
      rfl

theorem policy_output_eq_reference (seed : Ω) (hρ1 : ρ ≤ 1) (A : Table E n T ρ) (N : ℕ)
    (hgood : FutureGoodBefore E n T hn ρ hρ P seed A N) :
    (OraclePolicy.run (Domain n T hn ρ hρ) P (oracleResponse (finiteSum hn hρ hρ1 A).toProblem) seed N).1 =
      output E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed A N) := by
  let oracle := oracleResponse (finiteSum hn hρ hρ1 A).toProblem
  have hsteps : ∀ t < N,
      (runWithTable E n T hn ρ hρ P seed A (t + 1)).base.control =
        Machine.policyControlStep E n T hn ρ hρ P oracle seed (runWithTable E n T hn ρ hρ P seed A t).base.control := by
    intro t ht
    rw [runWithTable]
    exact step_control_eq_actual E n T hn ρ hρ P seed hρ1 A _
      (run_pastCorrect E n T hn ρ hρ P seed A t) (hgood t ht)
  have hall : ∀ k t, t + k ≤ N →
      Machine.finishAfter E n T hn ρ hρ P oracle seed k (runWithTable E n T hn ρ hρ P seed A t).base.control =
        output E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed A (t + k)) := by
    intro k
    induction k with
    | zero => intro t ht; rfl
    | succ k ih =>
        intro t ht
        rw [Machine.finishAfter_succ, ← hsteps t (by omega)]
        have he := ih (t + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using he
  simpa only [Machine.finishAfter, runWithTable, initial, Machine.initial, Sum.elim_inr,
    OraclePolicy.run, Nat.zero_add] using hall N 0 (by omega)

theorem not_stationary_of_unfinished (seed : Ω) (hρ1 : ρ ≤ 1) (A : Table E n T ρ) (N : ℕ)
    (hgood : FutureGoodBefore E n T hn ρ hρ P seed A N)
    (hf : frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A N) < T)
    (hout : ∀ j : Fin (T + 1),
      frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A N) < j.val →
      coordinate A.direction ((primalCoordinates E T).symm
        (output E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed A N))) j ≤ 5 / 32) :
    ¬ StationaryOutput (finiteSum hn hρ hρ1 A).toProblem
      (OraclePolicy.run (Domain n T hn ρ hρ) P (oracleResponse (finiteSum hn hρ hρ1 A).toProblem) seed N).1 := by
  intro hstat
  rw [policy_output_eq_reference E n T hn ρ hρ P seed hρ1 A N hgood] at hstat
  have hlarge := stationary_all_stages hn hρ hρ1 A _ hstat (Fin.last T)
  have hsmall := hout (Fin.last T) hf
  linarith

end

end NCConcave16991.DenseSmooth.Revelation
