import NCConcave16991.DenseSmoothMachineState

/-! # Paid-stage accounting and unconditional correctness of released caches -/

namespace NCConcave16991.DenseSmooth.Machine

noncomputable section

open Set MeasureTheory

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

theorem stepWithRows_progress (seed : Ω) (r : ℕ) (rows : Rows E n T) (s : State E n T hn ρ hρ) :
    (stepWithRows E n T hn ρ hρ P seed r rows s).progress =
      Counter.step r s.progress ((request E n T hn ρ hρ P seed s).map Prod.snd) := by
  unfold stepWithRows step request
  cases ha : OracleSimulation.action (Domain n T hn ρ hρ) P seed s.control with
  | inl x => rfl
  | inr o =>
      simp only [Sum.elim_inr]
      unfold paidQuery
      split_ifs <;> rfl

def querySequence (seed : Ω) (r : ℕ) (rows : Rows E n T) (t : ℕ) : Option (Fin n) :=
  (request E n T hn ρ hρ P seed (runWithRows E n T hn ρ hρ P seed r rows t)).map Prod.snd

theorem run_progress (seed : Ω) (r : ℕ) (rows : Rows E n T) (t : ℕ) :
    (runWithRows E n T hn ρ hρ P seed r rows t).progress =
      Counter.run r (querySequence E n T hn ρ hρ P seed r rows) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [runWithRows, stepWithRows_progress, Counter.run, ih]; rfl

theorem run_work_le (seed : Ω) (r : ℕ) (rows : Rows E n T) (t : ℕ) :
    Counter.work r (runWithRows E n T hn ρ hρ P seed r rows t).progress ≤ t := by
  rw [run_progress]
  exact Counter.work_run_le _ _ _

theorem run_learned_lt (seed : Ω) {r : ℕ} (hr : 0 < r) (rows : Rows E n T) (t : ℕ) :
    (runWithRows E n T hn ρ hρ P seed r rows t).progress.2.card < r := by
  rw [run_progress]
  exact Counter.run_learned_lt hr _ _

theorem run_unfinished (seed : Ω) (r : ℕ) (rows : Rows E n T) (t : ℕ)
    (hbudget : t < (T + 1) * r) :
    (runWithRows E n T hn ρ hρ P seed r rows t).progress.1 < T + 1 := by
  rw [run_progress]
  exact Counter.unfinished_of_budget _ _ _ _ hbudget

def PastCorrect (A : Table E n T ρ) (s : State E n T hn ρ hρ) : Prop :=
  ∀ j : Fin (T + 1), j.val < s.progress.1 →
    (∀ i, s.rows j i = A.row i j) ∧ s.directions j = A.direction j

theorem paidQuery_pastCorrect (r : ℕ) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (hs : PastCorrect E n T hn ρ hρ A s) (o : Query E n T hn ρ hρ) (a : E) :
    PastCorrect E n T hn ρ hρ A
      (paidQuery E n T hn ρ hρ r s o a (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s))) := by
  by_cases hvalid : s.progress.1 < T + 1
  · have hindex : (stageIndex E n T hn ρ hρ s).val = s.progress.1 := Nat.mod_eq_of_lt hvalid
    by_cases hrel : r ≤ (insert o.1 s.progress.2).card
    · intro j hj
      simp only [paidQuery, hvalid, ite_true, Counter.step, hrel, ite_true] at hj
      by_cases hjold : j.val < s.progress.1
      · have hjne : j ≠ stageIndex E n T hn ρ hρ s := by intro he; have := congrArg Fin.val he; omega
        simp only [paidQuery, hvalid, ite_true, shouldRelease, hrel, decide_true,
          Function.update_of_ne hjne]
        rw [ConeReferenceCache.putRow_other_stage _ _ _ _ _ hjne]
        exact hs j hjold
      · have hje : j = stageIndex E n T hn ρ hρ s := by apply Fin.ext; omega
        subst j
        simp only [paidQuery, hvalid, ite_true, shouldRelease, hrel, decide_true, Function.update_self]
        exact ⟨fun _ ↦ trivial, rowDirection_eq E n T hn ρ hρ A _⟩
    · intro j hj
      simp only [paidQuery, hvalid, ite_true, Counter.step, hrel, ite_false] at hj
      have hjne : j ≠ stageIndex E n T hn ρ hρ s := by intro he; have := congrArg Fin.val he; omega
      simp only [paidQuery, hvalid, ite_true, shouldRelease, hrel, decide_false, Bool.false_eq_true, ite_false]
      rw [ConeReferenceCache.putRow_other_stage _ _ _ _ _ hjne]
      exact hs j hj
  · intro j hj
    simp only [paidQuery, hvalid, ite_false] at hj ⊢
    exact hs j hj

theorem run_pastCorrect (seed : Ω) (r : ℕ) (A : Table E n T ρ) (t : ℕ) :
    PastCorrect E n T hn ρ hρ A
      (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) t) := by
  induction t with
  | zero => intro j hj; change j.val < 0 at hj; omega
  | succ t ih =>
      rw [runWithRows, stepWithRows, step]
      cases ha : OracleSimulation.action (Domain n T hn ρ hρ) P seed
        (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) t).control with
      | inl x => exact ih
      | inr o => exact paidQuery_pastCorrect E n T hn ρ hρ r A _ ih o _

end

end NCConcave16991.DenseSmooth.Machine
