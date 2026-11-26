import NCConcave16991.DenseSmoothMachineAccounting

/-! # Repeated component queries use the cached row and reveal no fresh cell -/

namespace NCConcave16991.DenseSmooth.Machine

noncomputable section

open Set MeasureTheory

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

def CurrentCorrect (A : Table E n T ρ) (s : State E n T hn ρ hρ) : Prop :=
  ∀ j : Fin (T + 1), j.val = s.progress.1 → ∀ i ∈ s.progress.2, s.rows j i = A.row i j

theorem stepWithRows_currentCorrect (seed : Ω) (r : ℕ) (A : Table E n T ρ)
    (s : State E n T hn ρ hρ) (hs : CurrentCorrect E n T hn ρ hρ A s) :
    CurrentCorrect E n T hn ρ hρ A (stepWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) s) := by
  unfold stepWithRows step
  cases ha : OracleSimulation.action (Domain n T hn ρ hρ) P seed s.control with
  | inl x => exact hs
  | inr o =>
      simp only [Sum.elim_inr]
      by_cases hf : s.progress.1 < T + 1
      · have hreq : request E n T hn ρ hρ P seed s = some (stageIndex E n T hn ρ hρ s, o.1) := by
          simp only [request, ha, Sum.elim_inr, hf, ite_true]
        rw [hreq]
        simp only [Option.elim_some]
        by_cases hrel : r ≤ (insert o.1 s.progress.2).card
        · intro j hj i hi
          simp only [paidQuery, hf, ite_true, Counter.step, hrel, ite_true] at hi
          simp at hi
        · intro j hj i hi
          simp only [paidQuery, hf, ite_true, Counter.step, hrel, ite_false] at hj hi
          have hje : j = stageIndex E n T hn ρ hρ s := by
            apply Fin.ext
            exact hj.trans (Nat.mod_eq_of_lt hf).symm
          subst j
          simp only [paidQuery, hf, ite_true, shouldRelease, hrel, decide_false, Bool.false_eq_true, ite_false]
          by_cases hie : i = o.1
          · subst i; exact ConeReferenceCache.putRow_same _ _ _ _
          · simp only [ConeReferenceCache.putRow, Function.update_self, Function.update_of_ne hie]
            exact hs _ (Nat.mod_eq_of_lt hf) i ((Finset.mem_insert.mp hi).resolve_left hie)
      · intro j hj i hi
        simp only [paidQuery, hf, ite_false] at hj hi ⊢
        exact hs j hj i hi

theorem run_currentCorrect (seed : Ω) (r : ℕ) (A : Table E n T ρ) (t : ℕ) :
    CurrentCorrect E n T hn ρ hρ A
      (runWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) t) := by
  induction t with
  | zero => intro j hj i hi; simpa [runWithRows, initial, Counter.initial] using hi
  | succ t ih => rw [runWithRows]; exact stepWithRows_currentCorrect E n T hn ρ hρ P seed r A _ ih

def freshRequest (seed : Ω) (s : State E n T hn ρ hρ) : Option (RowIndex n T) :=
  (request E n T hn ρ hρ P seed s).filter (fun ji ↦ ji.2 ∉ s.progress.2)

def effectiveAnswer (seed : Ω) (s : State E n T hn ρ hρ) (a : E) : E :=
  (request E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ if ji.2 ∈ s.progress.2 then s.rows ji.1 ji.2 else a)

theorem freshRequest_seen (seed : Ω) (s : State E n T hn ρ hρ) (ji : RowIndex n T)
    (hr : request E n T hn ρ hρ P seed s = some ji) (hi : ji.2 ∈ s.progress.2) :
    freshRequest E n T hn ρ hρ P seed s = none := by
  simp [freshRequest, hr, hi]

theorem request_stage (seed : Ω) (s : State E n T hn ρ hρ) (ji : RowIndex n T)
    (hr : request E n T hn ρ hρ P seed s = some ji) : ji.1.val = s.progress.1 := by
  unfold request at hr
  cases ha : OracleSimulation.action (Domain n T hn ρ hρ) P seed s.control with
  | inl x => simp [ha] at hr
  | inr o =>
      simp only [ha, Sum.elim_inr] at hr
      split_ifs at hr with hf
      injection hr with he
      subst ji
      exact Nat.mod_eq_of_lt hf

theorem effectiveAnswer_correct (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (hs : CurrentCorrect E n T hn ρ hρ A s) :
    effectiveAnswer E n T hn ρ hρ P seed s
      ((freshRequest E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1)) =
      (request E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1) := by
  cases hr : request E n T hn ρ hρ P seed s with
  | none => simp [effectiveAnswer, freshRequest, hr]
  | some ji =>
      by_cases hi : ji.2 ∈ s.progress.2
      · simp only [effectiveAnswer, hr, Option.elim_some, hi, ite_true]
        exact hs ji.1 (request_stage E n T hn ρ hρ P seed s ji hr) ji.2 hi
      · simp [effectiveAnswer, freshRequest, hr, hi, Option.filter]

theorem stepWithRows_eq_freshStep (seed : Ω) (r : ℕ) (A : Table E n T ρ)
    (s : State E n T hn ρ hρ) (hs : CurrentCorrect E n T hn ρ hρ A s) :
    stepWithRows E n T hn ρ hρ P seed r (fun j i ↦ A.row i j) s =
      step E n T hn ρ hρ P seed r s
        (effectiveAnswer E n T hn ρ hρ P seed s
          ((freshRequest E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1)))
        (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s)) := by
  rw [effectiveAnswer_correct E n T hn ρ hρ P seed A s hs]
  rfl

end

end NCConcave16991.DenseSmooth.Machine
