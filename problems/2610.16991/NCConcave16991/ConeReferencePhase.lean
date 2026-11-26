import NCConcave16991.ConditionalHaarConeMachineStep

/-! # Exact phases and paid-query accounting of the concrete cone machine -/

open Set MeasureTheory

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n M : ℕ) (R : ℝ) (hR : 0 < R)

abbrev FreeData := Control E n M R hR × ConeCounter.State n × Action E n M R hR × ℕ × Bool

def freeData (s : State E n M R hR) : FreeData E n M R hR :=
  (s.control, s.progress, s.pending, s.pendingStage, s.release)

theorem freeUpdate_freeData (hn : 0 < n) (s : State E n M R hR) (a : E) :
    freeData E n M R hR (freeUpdate E n M R hR hn s a) = freeData E n M R hR s := by
  unfold freeUpdate
  split_ifs <;> rfl

def paidChoice (s : State E n M R hR) : Option (Fin n) :=
  if s.pendingStage < M + 1 then pendingIndex E n M R hR s else none

theorem paidUpdate_progress (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E) :
    (paidUpdate E n M R hR hn q s a).progress = ConeCounter.step s.progress (paidChoice E n M R hR s) := by
  cases he : s.pending with
  | inl x =>
      simp only [paidUpdate, he, actionIsQuery, Sum.elim_inl, Bool.false_eq_true, ite_false,
        paidChoice, pendingIndex]
      split_ifs <;> rfl
  | inr o =>
      simp only [paidUpdate, he, actionIsQuery, Sum.elim_inr, ↓reduceIte,
        actionQuery, paidQuery, paidChoice, pendingIndex]
      split_ifs <;> rfl

theorem nextPhase_val (s : State E n M R hR) :
    (nextPhase E n M R hR s).val = (s.phase.val + 1) % (n + 2) := by
  simp only [nextPhase, Fin.val_add, Fin.val_one]

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain E M R hR) (n := n) (dx := ConeProblem.primalDimension E M) Ω)

theorem update_phase (seed : Ω) (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E) :
    (update E n M R hR P seed hn q s a).phase = nextPhase E n M R hR s := by
  unfold update prepare paidUpdate paidQuery freeUpdate
  split_ifs <;> rfl

theorem stepWithRows_phase (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (s : State E n M R hR) :
    (stepWithRows E n M R hR P seed hn q rows s).phase = nextPhase E n M R hR s :=
  update_phase E n M R hR P seed hn q s _

theorem runWithRows_phase (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    (runWithRows E n M R hR P seed hn q rows t).phase.val = t % (n + 2) := by
  induction t with
  | zero => simp [runWithRows, initial]
  | succ t ih =>
      rw [runWithRows, stepWithRows_phase, nextPhase_val, ih]
      simpa only [Nat.mod_eq_of_lt (by omega : 1 < n + 2)] using (Nat.add_mod t 1 (n + 2)).symm

theorem boundary_phase (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    (boundary E n M R hR P seed hn q rows t).phase = 0 := by
  apply Fin.ext
  simp only [boundary, runWithRows_phase, Fin.val_zero, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod]

theorem run_cycle_phase (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k < n + 2) :
    (runWithRows E n M R hR P seed hn q rows ((n + 2) * t + k)).phase.val = k := by
  rw [runWithRows_phase, Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, zero_add, Nat.mod_mod]
  exact Nat.mod_eq_of_lt hk

theorem run_prepare (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    runWithRows E n M R hR P seed hn q rows ((n + 2) * t + 1) =
      prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t) := by
  rw [runWithRows, stepWithRows, update]
  have hphase := boundary_phase E n M R hR P seed hn q rows t
  have hv : (runWithRows E n M R hR P seed hn q rows ((n + 2) * t)).phase.val = 0 := by
    simpa only [boundary, Fin.val_zero] using congrArg Fin.val hphase
  rw [if_pos hv]
  rfl

theorem run_paid (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    runWithRows E n M R hR P seed hn q rows ((n + 2) * t + 2) =
      paidUpdate E n M R hR hn q
        (prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t))
        (requestedAnswer E n M rows (request E n M R hR hn
          (prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t)))) := by
  rw [show (n + 2) * t + 2 = ((n + 2) * t + 1) + 1 by omega, runWithRows,
    run_prepare, stepWithRows, update]
  have hp : (prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t)).phase.val = 1 := by
    rw [← run_prepare]
    exact run_cycle_phase E n M R hR P seed hn q rows t 1 (by omega)
  rw [if_neg (by omega : (prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t)).phase.val ≠ 0), if_pos hp]

theorem run_freeData (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t k : ℕ) (hk : k ≤ n) :
    freeData E n M R hR (runWithRows E n M R hR P seed hn q rows ((n + 2) * t + 2 + k)) =
      freeData E n M R hR (runWithRows E n M R hR P seed hn q rows ((n + 2) * t + 2)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hphase := run_cycle_phase E n M R hR P seed hn q rows t (2 + k) (by omega)
      have hidx : (n + 2) * t + 2 + k = (n + 2) * t + (2 + k) := by omega
      rw [← hidx] at hphase
      rw [show (n + 2) * t + 2 + (k + 1) = ((n + 2) * t + 2 + k) + 1 by omega,
        runWithRows, stepWithRows, update,
        if_neg (by omega : (runWithRows E n M R hR P seed hn q rows ((n + 2) * t + 2 + k)).phase.val ≠ 0),
        if_neg (by omega : (runWithRows E n M R hR P seed hn q rows ((n + 2) * t + 2 + k)).phase.val ≠ 1),
        freeUpdate_freeData]
      exact ih (by omega)

theorem boundary_freeData_succ (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    freeData E n M R hR (boundary E n M R hR P seed hn q rows (t + 1)) =
      freeData E n M R hR (paidUpdate E n M R hR hn q
        (prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t))
        (requestedAnswer E n M rows (request E n M R hR hn
          (prepare E n M R hR P seed (boundary E n M R hR P seed hn q rows t))))) := by
  have hidx : (n + 2) * (t + 1) = (n + 2) * t + 2 + n := by ring
  rw [boundary, hidx, run_freeData E n M R hR P seed hn q rows t n le_rfl, run_paid]

def outerChoice (seed : Ω) (s : State E n M R hR) : Option (Fin n) :=
  paidChoice E n M R hR (prepare E n M R hR P seed s)

theorem boundary_progress_succ (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    (boundary E n M R hR P seed hn q rows (t + 1)).progress =
      ConeCounter.step (boundary E n M R hR P seed hn q rows t).progress
        (outerChoice E n M R hR P seed (boundary E n M R hR P seed hn q rows t)) := by
  have he := congrArg (fun d : FreeData E n M R hR ↦ d.2.1)
    (boundary_freeData_succ E n M R hR P seed hn q rows t)
  change _ = (paidUpdate E n M R hR hn q _ _).progress at he
  rw [paidUpdate_progress] at he
  exact he

def querySequence (seed : Ω) (hn : 0 < n) (q : ℝ) (rows : Fin (M + 1) → Fin n → E) (t : ℕ) : Option (Fin n) :=
  outerChoice E n M R hR P seed (boundary E n M R hR P seed hn q rows t)

theorem boundary_progress_eq_counter_run (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    (boundary E n M R hR P seed hn q rows t).progress =
      ConeCounter.run (querySequence E n M R hR P seed hn q rows) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [boundary_progress_succ, ConeCounter.run, ih]; rfl

theorem boundary_work_le (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    ConeCounter.work (boundary E n M R hR P seed hn q rows t).progress ≤ t := by
  rw [boundary_progress_eq_counter_run]
  exact ConeCounter.work_run_le _ _

theorem boundary_learned_lt (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) :
    (boundary E n M R hR P seed hn q rows t).progress.2.card < ConeCounter.threshold n := by
  rw [boundary_progress_eq_counter_run]
  exact ConeCounter.run_learned_lt hn _ _

theorem boundary_unfinished (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ)
    (hbudget : (t : ℝ) < (n : ℝ) * (M + 1 : ℕ) / 4096) :
    (boundary E n M R hR P seed hn q rows t).progress.1 < M + 1 := by
  rw [boundary_progress_eq_counter_run]
  exact ConeCounter.unfinished_of_budget_lt _ _ _ hbudget

end

end NCConcave16991.Haar.ConeMachine
