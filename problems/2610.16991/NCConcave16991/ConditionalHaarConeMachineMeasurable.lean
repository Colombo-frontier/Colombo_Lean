import NCConcave16991.ConditionalHaarConeMachineStep

/-! # Measurability of the actual phased cone reference interpreter -/

open Set MeasureTheory

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

set_option maxHeartbeats 1000000

instance requestMeasurableSingletonClass (n M : ℕ) : MeasurableSingletonClass (Request n M) := by
  constructor
  intro r
  apply measurableSet_sum_iff.mpr
  exact ⟨(Sum.inl ⁻¹' ({r} : Set (Request n M))).to_countable.measurableSet,
    (Sum.inr ⁻¹' ({r} : Set (Request n M))).to_countable.measurableSet⟩

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (n M : ℕ) (R : ℝ) (hR : 0 < R)

attribute [fun_prop] control_measurable progress_measurable rows_measurable means_measurable
  phase_measurable pending_measurable pendingStage_measurable release_measurable
  nextPhase_measurable pendingIndex_measurable request_measurable measurable_mk

@[fun_prop] theorem stageIndex_measurable : Measurable (stageIndex E n M R hR) :=
  (measurable_of_countable (fun j : ℕ ↦ (⟨j % (M + 1), Nat.mod_lt _ (by omega)⟩ : Fin (M + 1)))).comp
    (pendingStage_measurable E n M R hR)

@[fun_prop] theorem releaseRow_measurable (hn : 0 < n) : Measurable (releaseRow E n M R hR hn) :=
  (measurable_of_countable (fun j : Fin (n + 2) ↦ (⟨(j.val - 2) % n, Nat.mod_lt _ hn⟩ : Fin n))).comp
    (phase_measurable E n M R hR)

@[fun_prop] theorem actionQuery_measurable (hn : 0 < n) : Measurable (actionQuery E n M R hR hn) :=
  measurable_const.sumElim measurable_id

@[fun_prop] theorem actionOutput_measurable : Measurable (actionOutput E n M R hR) :=
  measurable_id.sumElim measurable_const

@[fun_prop] theorem actionIsQuery_measurable : Measurable (actionIsQuery E n M R hR) :=
  measurable_const.sumElim measurable_const

@[fun_prop] theorem controlHistory_measurable : Measurable (controlHistory E n M R hR) :=
  measurable_const.sumElim measurable_id

@[fun_prop] theorem controlOutput_measurable : Measurable (controlOutput E n M R hR) :=
  measurable_id.sumElim measurable_const

@[fun_prop] theorem controlIsRunning_measurable : Measurable (controlIsRunning E n M R hR) :=
  measurable_const.sumElim measurable_const

@[fun_prop] theorem measurable_someIndex {X : Type*} [MeasurableSpace X]
    {i : X → Fin n} (hi : Measurable i) : Measurable (fun x ↦ some (i x)) :=
  (measurable_of_countable (fun j : Fin n ↦ some j)).comp hi

@[fun_prop] theorem measurable_shouldRelease {X : Type*} [MeasurableSpace X]
    {c : X → ConeCounter.State n} {i : X → Fin n} (hc : Measurable c) (hi : Measurable i) :
    Measurable (fun x ↦ shouldRelease n (c x) (i x)) :=
  (measurable_of_countable (fun p : ConeCounter.State n × Fin n ↦ shouldRelease n p.1 p.2)).comp (hc.prodMk hi)

@[fun_prop] theorem measurable_counterStep {X : Type*} [MeasurableSpace X]
    {c : X → ConeCounter.State n} {i : X → Option (Fin n)} (hc : Measurable c) (hi : Measurable i) :
    Measurable (fun x ↦ ConeCounter.step (c x) (i x)) :=
  (ConeCounter.step_measurable n).comp (hc.prodMk hi)

theorem appendControl_measurable : Measurable (fun p : Control E n M R hR × Query E n M R hR ×
    OracleAnswer (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M) ↦
    appendControl E n M R hR p.1 p.2.1 p.2.2) := by
  have hb : Measurable (fun p : Control E n M R hR × Query E n M R hR ×
      OracleAnswer (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M) ↦
      controlIsRunning E n M R hR p.1) := (controlIsRunning_measurable E n M R hR).comp measurable_fst
  unfold appendControl
  apply Measurable.ite (hb (measurableSet_singleton true))
  · apply measurable_inr.comp
    exact (OraclePolicy.appendHistory_measurable (Domain E M R hR)).comp
      (((controlHistory_measurable E n M R hR).comp measurable_fst).prodMk measurable_snd)
  · exact measurable_inl.comp ((controlOutput_measurable E n M R hR).comp measurable_fst)

@[fun_prop] theorem measurable_appendControl {X : Type*} [MeasurableSpace X]
    {c : X → Control E n M R hR} {o : X → Query E n M R hR}
    {a : X → OracleAnswer (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M)}
    (hc : Measurable c) (ho : Measurable o) (ha : Measurable a) :
    Measurable (fun x ↦ appendControl E n M R hR (c x) (o x) (a x)) :=
  (appendControl_measurable E n M R hR).comp (hc.prodMk (ho.prodMk ha))

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain E M R hR) (n := n) (dx := ConeProblem.primalDimension E M) Ω)

@[fun_prop] theorem measurable_policyAction {X : Type*} [MeasurableSpace X]
    {seed : X → Ω} {c : X → Control E n M R hR} (hs : Measurable seed) (hc : Measurable c) :
    Measurable (fun x ↦ OracleSimulation.action (Domain E M R hR) P (seed x) (c x)) :=
  (OracleSimulation.action_measurable (Domain E M R hR) P).comp (hs.prodMk hc)

theorem prepare_measurable : Measurable (fun p : Ω × State E n M R hR ↦ prepare E n M R hR P p.1 p.2) := by
  unfold prepare
  apply measurable_mk <;> fun_prop

theorem paidQuery_measurable (q : ℝ) : Measurable (fun p : State E n M R hR × Query E n M R hR × E ↦
    paidQuery E n M R hR q p.1 p.2.1 p.2.2) := by
  have hc : MeasurableSet {p : State E n M R hR × Query E n M R hR × E | p.1.pendingStage < M + 1} :=
    ((pendingStage_measurable E n M R hR).comp measurable_fst)
      (({j : ℕ | j < M + 1} : Set ℕ).to_countable.measurableSet)
  unfold paidQuery
  apply Measurable.ite hc
  · dsimp only
    apply measurable_mk <;> fun_prop
  · dsimp only
    apply measurable_mk <;> fun_prop

theorem paidUpdate_measurable (hn : 0 < n) (q : ℝ) : Measurable (fun p : State E n M R hR × E ↦
    paidUpdate E n M R hR hn q p.1 p.2) := by
  have hc : MeasurableSet {p : State E n M R hR × E | actionIsQuery E n M R hR p.1.pending} :=
    ((actionIsQuery_measurable E n M R hR).comp
      ((pending_measurable E n M R hR).comp measurable_fst)) (measurableSet_singleton true)
  unfold paidUpdate
  apply Measurable.ite hc
  · exact (paidQuery_measurable E n M R hR q).comp
      (measurable_fst.prodMk (((actionQuery_measurable E n M R hR hn).comp
        ((pending_measurable E n M R hR).comp measurable_fst)).prodMk measurable_snd))
  · apply measurable_mk <;> fun_prop

theorem freeUpdate_measurable (hn : 0 < n) : Measurable (fun p : State E n M R hR × E ↦
    freeUpdate E n M R hR hn p.1 p.2) := by
  have hb : MeasurableSet {p : State E n M R hR × E | p.1.release} :=
    ((release_measurable E n M R hR).comp measurable_fst) (measurableSet_singleton true)
  have hc : MeasurableSet {p : State E n M R hR × E | p.1.pendingStage < M + 1} :=
    ((pendingStage_measurable E n M R hR).comp measurable_fst)
      (({j : ℕ | j < M + 1} : Set ℕ).to_countable.measurableSet)
  have hl : MeasurableSet {p : State E n M R hR × E | p.1.phase.val = n + 1} :=
    ((phase_measurable E n M R hR).comp measurable_fst)
      (({j : Fin (n + 2) | j.val = n + 1} : Set (Fin (n + 2))).to_countable.measurableSet)
  unfold freeUpdate
  apply Measurable.ite hb
  · apply Measurable.ite hc
    · dsimp only
      apply measurable_mk
      · fun_prop
      · fun_prop
      · fun_prop
      · apply Measurable.ite hl <;> fun_prop
      · fun_prop
      · fun_prop
      · fun_prop
      · fun_prop
    · apply measurable_mk <;> fun_prop
  · apply measurable_mk <;> fun_prop

theorem update_measurable (hn : 0 < n) (q : ℝ) : Measurable
    (fun p : (Ω × State E n M R hR) × E ↦ update E n M R hR P p.1.1 hn q p.1.2 p.2) := by
  have hc (v : ℕ) : MeasurableSet {p : (Ω × State E n M R hR) × E | p.1.2.phase.val = v} :=
    ((phase_measurable E n M R hR).comp (measurable_snd.comp measurable_fst))
      (({j : Fin (n + 2) | j.val = v} : Set (Fin (n + 2))).to_countable.measurableSet)
  unfold update
  apply Measurable.ite (hc 0)
  · exact (prepare_measurable E n M R hR P).comp measurable_fst
  · apply Measurable.ite (hc 1)
    · exact (paidUpdate_measurable E n M R hR hn q).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    · exact (freeUpdate_measurable E n M R hR hn).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

@[fun_prop] theorem measurable_update {X : Type*} [MeasurableSpace X]
    (hn : 0 < n) (q : ℝ) {seed : X → Ω} {s : X → State E n M R hR} {a : X → E}
    (hs : Measurable seed) (hu : Measurable s) (ha : Measurable a) :
    Measurable (fun x ↦ update E n M R hR P (seed x) hn q (s x) (a x)) :=
  (update_measurable E n M R hR P hn q).comp ((hs.prodMk hu).prodMk ha)

theorem requestedAnswer_measurable : Measurable (fun p : Request n M × (Fin (M + 1) → Fin n → E) ↦
    requestedAnswer E n M p.2 p.1) := by
  apply measurable_from_prod_countable_right
  intro r
  cases r with
  | inl _ => exact measurable_const
  | inr ji => exact (measurable_pi_apply ji.2).comp (measurable_pi_apply ji.1)

@[fun_prop] theorem measurable_requestedAnswer {X : Type*} [MeasurableSpace X]
    {rows : X → Fin (M + 1) → Fin n → E} {r : X → Request n M}
    (hr : Measurable rows) (hq : Measurable r) :
    Measurable (fun x ↦ requestedAnswer E n M (rows x) (r x)) :=
  (requestedAnswer_measurable E n M).comp (hq.prodMk hr)

theorem stepWithRows_measurable (hn : 0 < n) (q : ℝ) : Measurable
    (fun p : Ω × (Fin (M + 1) → Fin n → E) × State E n M R hR ↦
      stepWithRows E n M R hR P p.1 hn q p.2.1 p.2.2) := by
  unfold stepWithRows
  apply measurable_update <;> fun_prop

theorem runWithRows_measurable (hn : 0 < n) (q : ℝ) (t : ℕ) : Measurable
    (fun p : Ω × (Fin (M + 1) → Fin n → E) ↦ runWithRows E n M R hR P p.1 hn q p.2 t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (stepWithRows_measurable E n M R hR P hn q).comp
      (measurable_fst.prodMk (measurable_snd.prodMk ih))

theorem boundary_measurable (hn : 0 < n) (q : ℝ) (t : ℕ) : Measurable
    (fun p : Ω × (Fin (M + 1) → Fin n → E) ↦ boundary E n M R hR P p.1 hn q p.2 t) :=
  runWithRows_measurable E n M R hR P hn q ((n + 2) * t)

theorem output_measurable : Measurable (fun p : Ω × State E n M R hR ↦ output E n M R hR P p.1 p.2) :=
  (OracleSimulation.finish_measurable (Domain E M R hR) P).comp
    (measurable_fst.prodMk ((control_measurable E n M R hR).comp measurable_snd))

end

end NCConcave16991.Haar.ConeMachine
