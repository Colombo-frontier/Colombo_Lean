import GradientHessian.TestRegister
import GradientHessian.MachineSnapshot

/-! Recording an arbitrary measurable bounded test-selection machine.
Selecting a test is an internal step. Recording preserves the original state
and query history and exposes no hidden hit feedback. -/

namespace GradientHessian.TestSelectionMachine
open Matrix MeasureTheory LowRank
noncomputable section

structure Program (d : ℕ) (State : Type*) [MeasurableSpace State] where
  mode : State → Fin 4
  think : State → State
  query : State → Fin d → ℝ
  next : State × (Fin d → ℝ) → State
  test : State → EuclideanSpace ℝ (Fin d)
  selected : State → State
  mode_measurable : Measurable mode
  think_measurable : Measurable think
  query_measurable : Measurable query
  next_measurable : Measurable next
  test_measurable : Measurable test
  selected_measurable : Measurable selected

variable {d s : ℕ} {State : Type*} [MeasurableSpace State]

def Program.step (P : Program d State) (A : Matrix (Fin d) (Fin d) ℝ) (state : State) : State :=
  if P.mode state=0 then state else if P.mode state=1 then P.think state
  else if P.mode state=2 then P.next (state,A*ᵥP.query state) else P.selected state

def Program.record (P : Program d State) (s : ℕ) :
    MachineCompiler.Program d (State × TestRegister.Register s (EuclideanSpace ℝ (Fin d)))
      (Fin s → EuclideanSpace ℝ (Fin d)) where
  mode := fun t => if P.mode t.1=0 then 0 else if P.mode t.1=2 then 2 else 1
  think := fun t => if P.mode t.1=3 then
    (P.selected t.1,TestRegister.append t.2 (P.test t.1)) else (P.think t.1,t.2)
  query := fun t => P.query t.1
  next := fun t => (P.next (t.1.1,t.2),t.1.2)
  output := fun t => TestRegister.output t.2
  fallback := 0
  mode_measurable := Measurable.ite ((P.mode_measurable.comp measurable_fst) (measurableSet_singleton 0))
    measurable_const (Measurable.ite ((P.mode_measurable.comp measurable_fst) (measurableSet_singleton 2))
      measurable_const measurable_const)
  think_measurable := Measurable.ite ((P.mode_measurable.comp measurable_fst) (measurableSet_singleton 3))
    ((P.selected_measurable.comp measurable_fst).prodMk
      (TestRegister.append_measurable.comp (measurable_snd.prodMk (P.test_measurable.comp measurable_fst))))
    ((P.think_measurable.comp measurable_fst).prodMk measurable_snd)
  query_measurable := P.query_measurable.comp measurable_fst
  next_measurable := (P.next_measurable.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd
  output_measurable := TestRegister.output_measurable.comp measurable_snd

theorem Program.record_step (P : Program d State) (s : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (state : State)
    (reg : TestRegister.Register s (EuclideanSpace ℝ (Fin d))) :
    (P.record s).step (fun v => A*ᵥv) (state,reg) =
      (P.step A state,if P.mode state=3 then TestRegister.append reg (P.test state) else reg) := by
  by_cases h0 : P.mode state=0
  · simp [Program.record,MachineCompiler.Program.step,Program.step,h0]
  · by_cases h1 : P.mode state=1
    · simp [Program.record,MachineCompiler.Program.step,Program.step,h0,h1]
    · by_cases h2 : P.mode state=2
      · simp [Program.record,MachineCompiler.Program.step,Program.step,h0,h1,h2]
      · have h3 : P.mode state=3 := by omega
        simp [Program.record,MachineCompiler.Program.step,Program.step,h0,h1,h2,h3]

theorem Program.record_retains (P : Program d State) (s : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (t : State × TestRegister.Register s (EuclideanSpace ℝ (Fin d))) (i : Fin s)
    (hi : (P.record s).output t i≠0) :
    (P.record s).output ((P.record s).step (fun v => A*ᵥv) t) i=(P.record s).output t i := by
  rw [P.record_step]
  change TestRegister.output (if P.mode t.1=3 then TestRegister.append t.2 (P.test t.1) else t.2) i = _
  split_ifs
  · exact TestRegister.append_retains t.2 (P.test t.1) i hi
  · rfl

def Program.run (P : Program d State) (A : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (state : State) : State :=
  (P.step A)^[n] state

def Program.recordRun (P : Program d State) (s : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (state : State) : State × TestRegister.Register s (EuclideanSpace ℝ (Fin d)) :=
  ((P.record s).step (fun v => A*ᵥv))^[n] (state,TestRegister.empty)

theorem Program.recordRun_succ (P : Program d State) (s : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (state : State) :
    P.recordRun s A (n+1) state =
      (P.step A (P.recordRun s A n state).1,
        if P.mode (P.recordRun s A n state).1=3
        then TestRegister.append (P.recordRun s A n state).2 (P.test (P.recordRun s A n state).1)
        else (P.recordRun s A n state).2) := by
  exact (Function.iterate_succ_apply' _ _ _).trans (P.record_step s A _ _)

theorem Program.recordRun_state (P : Program d State) (s : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (state : State) : (P.recordRun s A n state).1=P.run A n state := by
  induction n with
  | zero => rfl
  | succ n ih => rw [P.recordRun_succ]; simp only [ih,Program.run,Function.iterate_succ_apply']

def Program.selections (P : Program d State) (A : Matrix (Fin d) (Fin d) ℝ) : ℕ → State → ℕ
  | 0, _ => 0
  | n+1, state => P.selections A n state+if P.mode (P.run A n state)=3 then 1 else 0

theorem Program.selections_mono (P : Program d State) (A : Matrix (Fin d) (Fin d) ℝ) (state : State) :
    Monotone (fun n => P.selections A n state) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [Program.selections]
  omega

theorem Program.recordRun_count (P : Program d State) (s : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (state : State) (hcap : P.selections A n state≤s) :
    (P.recordRun s A n state).2.1=P.selections A n state := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hncap := (P.selections_mono A state (Nat.le_succ n)).trans hcap
      have hn := ih hncap
      rw [P.recordRun_succ,P.recordRun_state]
      by_cases hm : P.mode (P.run A n state)=3
      · have hc : P.selections A n state<s := by simpa [Program.selections,hm] using hcap
        simp [hm,TestRegister.append,hn,Program.selections,hc]
      · simp [hm,hn,Program.selections]

theorem Program.selected_recorded (P : Program d State) (s : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (state : State) (hm : P.mode (P.run A n state)=3)
    (hcap : P.selections A (n+1) state≤s) :
    ∃ j, (P.record s).output (P.recordRun s A (n+1) state) j=P.test (P.run A n state) := by
  have hncap := (P.selections_mono A state (Nat.le_succ n)).trans hcap
  have hn := P.recordRun_count s A n state hncap
  have hc : (P.recordRun s A n state).2.1<s := by
    rw [hn]
    simpa [Program.selections,hm] using hcap
  refine ⟨⟨_,hc⟩,?_⟩
  rw [P.recordRun_succ,P.recordRun_state]
  change TestRegister.output (if _ then _ else _) _ = _
  rw [if_pos hm]
  exact TestRegister.append_inserts _ _ hc

theorem Program.recorded_origin (P : Program d State) (s : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (state : State) (j : Fin s)
    (hj : (P.record s).output (P.recordRun s A n state) j≠0) :
    ∃ i<n, P.mode (P.run A i state)=3 ∧
      (P.record s).output (P.recordRun s A n state) j=P.test (P.run A i state) := by
  induction n with
  | zero => exact False.elim (hj (by simp [Program.record,Program.recordRun,TestRegister.output,TestRegister.empty]))
  | succ n ih =>
      have he : (P.record s).output (P.recordRun s A (n+1) state) j =
          if P.mode (P.run A n state)=3 ∧ j.val=(P.recordRun s A n state).2.1 ∧
              (P.recordRun s A n state).2.1<s
          then P.test (P.run A n state) else (P.record s).output (P.recordRun s A n state) j := by
        rw [P.recordRun_succ,P.recordRun_state]
        change TestRegister.output (if _ then _ else _) j = _
        by_cases h : P.mode (P.run A n state)=3
        · simp only [h,if_true,true_and]
          exact TestRegister.append_output _ _ j
        · simp only [h,if_false,false_and]
          rfl
      by_cases h : P.mode (P.run A n state)=3 ∧ j.val=(P.recordRun s A n state).2.1 ∧
          (P.recordRun s A n state).2.1<s
      · exact ⟨n,by omega,h.1,he.trans (if_pos h)⟩
      · have he' := he.trans (if_neg h)
        obtain ⟨i,hi,hm,ht⟩ := ih (by rwa [← he'])
        exact ⟨i,by omega,hm,he'.trans ht⟩

/-- Exact selected-test event equivalence for every predicate that excludes
the unused zero vector. The predicate is absent from the compiled machine. -/
theorem Program.recorded_ever_iff (P : Program d State) (s : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (state : State) (hcap : ∀ n, P.selections A n state≤s)
    (R : EuclideanSpace ℝ (Fin d) → Prop) (hzero : ¬R 0) :
    (∃ n j, R ((P.record s).output (P.recordRun s A n state) j)) ↔
      ∃ n, P.mode (P.run A n state)=3 ∧ R (P.test (P.run A n state)) := by
  constructor
  · rintro ⟨n,j,hR⟩
    have hn : (P.record s).output (P.recordRun s A n state) j≠0 := by
      intro hz
      exact hzero (hz ▸ hR)
    obtain ⟨i,_,hm,he⟩ := P.recorded_origin s A n state j hn
    exact ⟨i,hm,he ▸ hR⟩
  · rintro ⟨n,hm,hR⟩
    obtain ⟨j,hj⟩ := P.selected_recorded s A n state hm (hcap (n+1))
    exact ⟨n+1,j,hj.symm ▸ hR⟩

def Program.queryCount (P : Program d State) (A : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (state : State) : ℕ :=
  ∑ i ∈ Finset.range n, if P.mode (P.run A i state)=2 then 1 else 0

theorem Program.record_mode_query (P : Program d State) (s : ℕ)
    (t : State × TestRegister.Register s (EuclideanSpace ℝ (Fin d))) :
    (P.record s).mode t=2 ↔ P.mode t.1=2 := by
  by_cases h0 : P.mode t.1=0
  · simp [Program.record,h0]
  · by_cases h2 : P.mode t.1=2 <;> simp [Program.record,h0,h2]

/-- Recording test selections performs no additional matrix products. -/
theorem Program.record_calls (P : Program d State) (s : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (state : State) :
    (P.record s).calls (fun v => A*ᵥv) n (state,TestRegister.empty) = P.queryCount A n state := by
  rw [MachineCompiler.Program.calls_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (if (P.record s).mode (P.recordRun s A i state)=2 then 1 else 0) = _
  simp only [P.record_mode_query,P.recordRun_state]

theorem Program.record_query (P : Program d State) (s : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (state : State) :
    (P.record s).query (P.recordRun s A n state)=P.query (P.run A n state) := by
  change P.query (P.recordRun s A n state).1= _
  rw [P.recordRun_state]

theorem Program.record_norm (P : Program d State) (s : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (state : State)
    (hnorm : ∀ i<n, P.mode (P.run A i state)=3 → ‖P.test (P.run A i state)‖≤1) (j : Fin s) :
    ‖(P.record s).output (P.recordRun s A n state) j‖≤1 := by
  by_cases hzero : (P.record s).output (P.recordRun s A n state) j=0
  · simp [hzero]
  · obtain ⟨i,hi,hm,he⟩ := P.recorded_origin s A n state j hzero
    rw [he]
    exact hnorm i hi hm

end
end GradientHessian.TestSelectionMachine
