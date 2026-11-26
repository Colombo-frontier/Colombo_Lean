import NCConcave16991.DenseSmoothMachineAccounting

/-! # Exact full-history policy coupling and arbitrary-output stage recovery -/

namespace NCConcave16991.DenseSmooth.Machine

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

def policyControlStep (oracle : Query E n T hn ρ hρ → OracleAnswer (primalDimension E T) 0)
    (seed : Ω) (c : Control E n T hn ρ hρ) : Control E n T hn ρ hρ :=
  (OracleSimulation.action (Domain n T hn ρ hρ) P seed c).elim Sum.inl
    (fun o ↦ appendControl E n T hn ρ hρ c o (oracle o))

def QueryGood (A : Table E n T ρ) (frontier : ℕ) (o : Query E n T hn ρ hρ) : Prop :=
  ∀ j : Fin T, frontier ≤ j.val →
    coordinate A.direction ((primalCoordinates E T).symm o.2.1) j.castSucc ≤ 5 / 32

def GoodBefore (seed : Ω) (r : ℕ) (A : Table E n T ρ) (N : ℕ) : Prop :=
  ∀ t < N, ∀ o : Query E n T hn ρ hρ,
    OracleSimulation.action (Domain n T hn ρ hρ) P seed
      (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) t).control = Sum.inr o →
    QueryGood E n T hn ρ hρ A
      (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) t).progress.1 o

theorem step_control_eq_actual (seed : Ω) (r : ℕ) (hρ1 : ρ ≤ 1) (A : Table E n T ρ)
    (s : State E n T hn ρ hρ) (hs : PastCorrect E n T hn ρ hρ A s)
    (hf : s.progress.1 < T + 1)
    (hgood : ∀ o, OracleSimulation.action (Domain n T hn ρ hρ) P seed s.control = Sum.inr o →
      QueryGood E n T hn ρ hρ A s.progress.1 o) :
    (stepWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) s).control =
      policyControlStep E n T hn ρ hρ P (oracleResponse (finiteSum hn hρ hρ1 A).toProblem) seed s.control := by
  unfold stepWithRows step policyControlStep
  cases ha : OracleSimulation.action (Domain n T hn ρ hρ) P seed s.control with
  | inl x => rfl
  | inr o =>
      simp only [Sum.elim_inr]
      have hreq : request E n T hn ρ hρ P seed s = some (stageIndex E n T hn ρ hρ s, o.1) := by
        simp only [request, ha, Sum.elim_inr, hf, ite_true]
      have hindex : (stageIndex E n T hn ρ hρ s).val = s.progress.1 := Nat.mod_eq_of_lt hf
      have hrows : ∀ j : Fin (T + 1), j.val ≤ s.progress.1 → A.row o.1 j =
          ConeReferenceCache.putRow s.rows (stageIndex E n T hn ρ hρ s) o.1
            (A.row o.1 (stageIndex E n T hn ρ hρ s)) j o.1 := by
        intro j hj
        by_cases hje : j = stageIndex E n T hn ρ hρ s
        · subst j
          exact (ConeReferenceCache.putRow_same _ _ _ _).symm
        · have hjlt : j.val < s.progress.1 := by
            have hne : j.val ≠ s.progress.1 := fun he ↦ hje (Fin.ext (he.trans hindex.symm))
            omega
          rw [ConeReferenceCache.putRow_other_stage _ _ _ _ _ hje]
          exact (hs j hjlt).1 o.1 |>.symm
      have hreply := oracleResponse_eq_reference hn hρ hρ1 A s.progress.1 s.directions
        (fun i j ↦ ConeReferenceCache.putRow s.rows (stageIndex E n T hn ρ hρ s) o.1
          (A.row o.1 (stageIndex E n T hn ρ hρ s)) j i) o
        (fun j hj ↦ (hs j hj).2.symm) hrows (hgood o ha)
      rw [hreq]
      simp only [Option.elim_some]
      unfold paidQuery
      rw [if_pos hf]
      change appendControl E n T hn ρ hρ s.control o
        (referenceReply hn hρ s.progress.1 s.directions _ o) = _
      rw [hreply]

def finishAfter (oracle : Query E n T hn ρ hρ → OracleAnswer (primalDimension E T) 0)
    (seed : Ω) (k : ℕ) (c : Control E n T hn ρ hρ) : PrimalSpace (primalDimension E T) :=
  c.elim id (fun h ↦ (OraclePolicy.runAux (Domain n T hn ρ hρ) P oracle seed k h).1)

theorem finishAfter_succ (oracle : Query E n T hn ρ hρ → OracleAnswer (primalDimension E T) 0)
    (seed : Ω) (k : ℕ) (c : Control E n T hn ρ hρ) :
    finishAfter E n T hn ρ hρ P oracle seed (k + 1) c =
      finishAfter E n T hn ρ hρ P oracle seed k (policyControlStep E n T hn ρ hρ P oracle seed c) := by
  cases c with
  | inl x => rfl
  | inr history =>
      cases ha : P.next seed history with
      | inl x => simp only [finishAfter, Sum.elim_inr, OraclePolicy.runAux, ha,
          policyControlStep, OracleSimulation.action, Sum.elim_inl, id_eq]
      | inr o => simp only [finishAfter, Sum.elim_inr, OraclePolicy.runAux, ha,
          policyControlStep, OracleSimulation.action, appendControl, Sum.elim_inr]

theorem policy_output_eq_reference (seed : Ω) (r : ℕ) (hρ1 : ρ ≤ 1) (A : Table E n T ρ) (N : ℕ)
    (hbudget : N < (T + 1) * r) (hgood : GoodBefore E n T hn ρ hρ P seed r A N) :
    (OraclePolicy.run (Domain n T hn ρ hρ) P (oracleResponse (finiteSum hn hρ hρ1 A).toProblem) seed N).1 =
      output E n T hn ρ hρ P seed (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) N) := by
  let oracle := oracleResponse (finiteSum hn hρ hρ1 A).toProblem
  have hsteps : ∀ t < N,
      (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) (t + 1)).control =
        policyControlStep E n T hn ρ hρ P oracle seed
          (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) t).control := by
    intro t ht
    rw [runWithRows]
    exact step_control_eq_actual E n T hn ρ hρ P seed r hρ1 A _
      (run_pastCorrect E n T hn ρ hρ P seed r A t)
      (run_unfinished E n T hn ρ hρ P seed r _ t (by omega)) (hgood t ht)
  have hall : ∀ k t, t + k ≤ N →
      finishAfter E n T hn ρ hρ P oracle seed k
        (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) t).control =
      output E n T hn ρ hρ P seed (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) (t + k)) := by
    intro k
    induction k with
    | zero => intro t ht; rfl
    | succ k ih =>
        intro t ht
        rw [finishAfter_succ, ← hsteps t (by omega)]
        have he := ih (t + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 k] using he
  simpa only [finishAfter, runWithRows, initial, Sum.elim_inr, OraclePolicy.run, Nat.zero_add] using hall N 0 (by omega)

theorem not_stationary_of_good (seed : Ω) (r : ℕ) (hρ1 : ρ ≤ 1) (A : Table E n T ρ) (N : ℕ)
    (hbudget : N < (T + 1) * r) (hgood : GoodBefore E n T hn ρ hρ P seed r A N)
    (hout : ∀ j : Fin (T + 1),
      (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) N).progress.1 ≤ j.val →
      coordinate A.direction ((primalCoordinates E T).symm
        (output E n T hn ρ hρ P seed (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) N))) j ≤ 5 / 32) :
    ¬ StationaryOutput (finiteSum hn hρ hρ1 A).toProblem
      (OraclePolicy.run (Domain n T hn ρ hρ) P (oracleResponse (finiteSum hn hρ hρ1 A).toProblem) seed N).1 := by
  intro hstat
  have he := policy_output_eq_reference E n T hn ρ hρ P seed r hρ1 A N hbudget hgood
  rw [he] at hstat
  have hf := run_unfinished E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) N hbudget
  let j : Fin (T + 1) := ⟨_, hf⟩
  have hlarge := stationary_all_stages hn hρ hρ1 A _ hstat j
  have hsmall := hout j le_rfl
  linarith

end

end NCConcave16991.DenseSmooth.Machine
