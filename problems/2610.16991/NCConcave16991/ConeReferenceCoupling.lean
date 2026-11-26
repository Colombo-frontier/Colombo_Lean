import NCConcave16991.ConeReferenceBoundary

/-! # Deterministic coupling to an arbitrary full-history cone-oracle policy -/

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.Haar.ConeMachine

open ConePrimitives ConeRadial ConeValue

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n M : ℕ) (R : ℝ) (hR : 0 < R)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def QueryGood (w : Fin n → Fin (M + 1) → E) (frontier : ℕ) (o : Query E n M R hR) : Prop :=
  ∀ j : Fin (M + 1), frontier ≤ j.val →
    ⟪zeta (((ConeProblem.jointCoordinates E M).symm (queryPoint o)).fst.fst j), sourceMean w j⟫_ℝ < 1 / 4 ∧
    |⟪normalizedClockProbe (((ConeProblem.jointCoordinates E M).symm (queryPoint o)).fst.snd j), sourceMean w j⟫_ℝ| < 1 / 2

theorem paidUpdate_control_eq (hn : 0 < n) (L : ℝ) (hL : 0 < L) (q : ℝ) (hq : 1 ≤ q)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j))
    (s : State E n M R hR) (hp : s.phase.val = 1) (o : Query E n M R hR)
    (hpend : s.pending = Sum.inr o) (hs : s.pendingStage = s.progress.1)
    (hf : s.progress.1 < M + 1)
    (hcache : PastCorrect E n M R hR (fun j i ↦ w i j) s)
    (hgood : QueryGood E n M R hR w s.progress.1 o) :
    (paidUpdate E n M R hR hn q s
      (requestedAnswer E n M (fun j i ↦ w i j) (request E n M R hR hn s))).control =
      appendControl E n M R hR s.control o
        (oracleResponse (ConeProblem.problem hn L hL R hR q hq w hw) o) := by
  let j : Fin (M + 1) := ⟨s.progress.1, hf⟩
  have hvalid : s.pendingStage < M + 1 := by simpa only [hs] using hf
  have hj : stageIndex E n M R hR s = j := by
    apply Fin.ext
    change s.pendingStage % (M + 1) = s.progress.1
    rw [Nat.mod_eq_of_lt hvalid, hs]
  have hreq : request E n M R hR hn s = Sum.inr (stageIndex E n M R hR s, o.1) := by
    simp only [request, requestOfSummary, hp, one_ne_zero, ite_false, ite_true,
      pendingIndex, hpend, Sum.elim_inr, Option.elim_some, hvalid]
    rfl
  have ha : requestedAnswer E n M (fun j i ↦ w i j) (request E n M R hR hn s) = w o.1 j := by
    rw [hreq, hj]
    rfl
  have hreply := ConeReferenceCache.reply_after_putRow_eq_oracle hn L hL R hR q hq w hw j s.means s.rows o
    (requestedAnswer E n M (fun j i ↦ w i j) (request E n M R hR hn s)) ha
    (fun k hk ↦ (hcache k hk).2.trans (ConeReferenceCache.rowMeanAt_eq_sourceMean _ w k (fun _ ↦ rfl)))
    (fun k hk i ↦ congrFun (hcache k hk).1 i) hgood
  simp only [paidUpdate, hpend, actionIsQuery, Sum.elim_inr, ite_true, actionQuery,
    paidQuery, hvalid]
  change appendControl E n M R hR s.control o
    (ConeReferenceCache.replyFromCache R q s.pendingStage s.means
      (ConeReferenceCache.putRow s.rows (stageIndex E n M R hR s) o.1 _) o) = _
  rw [hj, hs, hreply]

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain E M R hR) (n := n) (dx := ConeProblem.primalDimension E M) Ω)

def policyControlStep (oracle : Query E n M R hR →
    OracleAnswer (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M))
    (seed : Ω) (c : Control E n M R hR) : Control E n M R hR :=
  (OracleSimulation.action (Domain E M R hR) P seed c).elim Sum.inl
    (fun o ↦ appendControl E n M R hR c o (oracle o))

def GoodBefore (seed : Ω) (hn : 0 < n) (q : ℝ)
    (w : Fin n → Fin (M + 1) → E) (T : ℕ) : Prop :=
  ∀ t < T, ∀ o : Query E n M R hR,
    OracleSimulation.action (Domain E M R hR) P seed
      (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t).control = Sum.inr o →
    QueryGood E n M R hR w
      (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t).progress.1 o

theorem boundary_control_step (seed : Ω) (hn : 0 < n) (L : ℝ) (hL : 0 < L)
    (q : ℝ) (hq : 1 ≤ q) (w : Fin n → Fin (M + 1) → E)
    (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) (t : ℕ)
    (hf : (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t).progress.1 < M + 1)
    (hgood : ∀ o, OracleSimulation.action (Domain E M R hR) P seed
      (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t).control = Sum.inr o →
      QueryGood E n M R hR w
        (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t).progress.1 o) :
    (boundary E n M R hR P seed hn q (fun j i ↦ w i j) (t + 1)).control =
      policyControlStep E n M R hR P (oracleResponse (ConeProblem.problem hn L hL R hR q hq w hw)) seed
        (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t).control := by
  have hc := congrArg (fun d : FreeData E n M R hR ↦ d.1)
    (boundary_freeData_succ E n M R hR P seed hn q (fun j i ↦ w i j) t)
  dsimp only [freeData] at hc
  rw [hc]
  unfold policyControlStep
  cases ha : OracleSimulation.action (Domain E M R hR) P seed
    (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t).control with
  | inl x =>
      simp only [Sum.elim_inl, paidUpdate, prepare, ha, actionIsQuery, Sum.elim_inl,
        Bool.false_eq_true, ite_false, actionOutput]
      rfl
  | inr o =>
      simp only [Sum.elim_inr]
      let s := prepare E n M R hR P seed (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t)
      have hp : s.phase.val = 1 := by
        change (prepare E n M R hR P seed (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t)).phase.val = 1
        rw [← run_prepare]
        exact run_cycle_phase E n M R hR P seed hn q (fun j i ↦ w i j) t 1 (by omega)
      have hcach : PastCorrect E n M R hR (fun j i ↦ w i j) s :=
        boundary_pastCorrect E n M R hR P seed hn q (fun j i ↦ w i j) t
      exact paidUpdate_control_eq E n M R hR hn L hL q hq w hw s hp o ha rfl hf hcach (hgood o ha)

def finishAfter (oracle : Query E n M R hR →
    OracleAnswer (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M))
    (seed : Ω) (k : ℕ) (c : Control E n M R hR) : PrimalSpace (ConeProblem.primalDimension E M) :=
  c.elim id (fun h ↦ (OraclePolicy.runAux (Domain E M R hR) P oracle seed k h).1)

theorem finishAfter_succ (oracle : Query E n M R hR →
    OracleAnswer (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M))
    (seed : Ω) (k : ℕ) (c : Control E n M R hR) :
    finishAfter E n M R hR P oracle seed (k + 1) c =
      finishAfter E n M R hR P oracle seed k (policyControlStep E n M R hR P oracle seed c) := by
  cases c with
  | inl x => rfl
  | inr h =>
      cases ha : P.next seed h with
      | inl x => simp only [finishAfter, Sum.elim_inr, OraclePolicy.runAux, ha,
          policyControlStep, OracleSimulation.action, Sum.elim_inl, id_eq]
      | inr o => simp only [finishAfter, Sum.elim_inr, OraclePolicy.runAux, ha,
          policyControlStep, OracleSimulation.action, appendControl, controlIsRunning,
          Sum.elim_inr, ite_true, controlHistory, id_eq]

theorem policy_output_eq_reference (seed : Ω) (hn : 0 < n) (L : ℝ) (hL : 0 < L)
    (q : ℝ) (hq : 1 ≤ q) (w : Fin n → Fin (M + 1) → E)
    (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) (T : ℕ)
    (hbudget : (T : ℝ) < (n : ℝ) * (M + 1 : ℕ) / 4096)
    (hgood : GoodBefore E n M R hR P seed hn q w T) :
    (OraclePolicy.run (Domain E M R hR) P
      (oracleResponse (ConeProblem.problem hn L hL R hR q hq w hw)) seed T).1 =
      output E n M R hR P seed (boundary E n M R hR P seed hn q (fun j i ↦ w i j) T) := by
  let oracle := oracleResponse (ConeProblem.problem hn L hL R hR q hq w hw)
  have hsteps : ∀ t < T,
      (boundary E n M R hR P seed hn q (fun j i ↦ w i j) (t + 1)).control =
        policyControlStep E n M R hR P oracle seed
          (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t).control := by
    intro t ht
    apply boundary_control_step E n M R hR P seed hn L hL q hq w hw t
    · apply boundary_unfinished E n M R hR P seed hn q (fun j i ↦ w i j) t
      have hcast : (t : ℝ) ≤ T := by exact_mod_cast ht.le
      exact hcast.trans_lt hbudget
    · exact hgood t ht
  have hall : ∀ k t, t + k ≤ T →
      finishAfter E n M R hR P oracle seed k
        (boundary E n M R hR P seed hn q (fun j i ↦ w i j) t).control =
      output E n M R hR P seed (boundary E n M R hR P seed hn q (fun j i ↦ w i j) (t + k)) := by
    intro k
    induction k with
    | zero => intro t ht; rfl
    | succ k ih =>
        intro t ht
        rw [finishAfter_succ, ← hsteps t (by omega)]
        have he := ih (t + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using he
  simpa only [finishAfter, boundary, runWithRows, initial, Sum.elim_inr,
    OraclePolicy.run, Nat.zero_add, Nat.mul_zero] using hall T 0 (by omega)

end

end NCConcave16991.Haar.ConeMachine
