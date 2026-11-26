import NCConcave16991.ConditionalHaarConeMachineState
import NCConcave16991.ConeReferenceCache

/-! # The explicit n+2-phase cone reference interpreter -/

open Set MeasureTheory

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n M : ℕ) (R : ℝ) (hR : 0 < R)

def stageIndex (s : State E n M R hR) : Fin (M + 1) :=
  ⟨s.pendingStage % (M + 1), Nat.mod_lt _ (by omega)⟩

def releaseRow (hn : 0 < n) (s : State E n M R hR) : Fin n :=
  ⟨(s.phase.val - 2) % n, Nat.mod_lt _ hn⟩

def dummyQuery (hn : 0 < n) : Query E n M R hR :=
  (⟨0,hn⟩, 0, ⟨0, by change (0 : DualSpace (ConeProblem.dualDimension E M)) ∈ Metric.closedBall 0 R; simp [hR.le]⟩)

def actionQuery (hn : 0 < n) (a : Action E n M R hR) : Query E n M R hR :=
  a.elim (fun _ ↦ dummyQuery E n M R hR hn) id

def actionOutput (a : Action E n M R hR) : PrimalSpace (ConeProblem.primalDimension E M) :=
  a.elim id (fun _ ↦ 0)

def actionIsQuery (a : Action E n M R hR) : Bool := a.elim (fun _ ↦ false) (fun _ ↦ true)

def controlHistory (c : Control E n M R hR) : OraclePolicy.History (Domain E M R hR) (n := n)
    (dx := ConeProblem.primalDimension E M) :=
  c.elim (fun _ ↦ OraclePolicy.emptyHistory (Domain E M R hR)) id

def controlOutput (c : Control E n M R hR) : PrimalSpace (ConeProblem.primalDimension E M) :=
  c.elim id (fun _ ↦ 0)

def controlIsRunning (c : Control E n M R hR) : Bool := c.elim (fun _ ↦ false) (fun _ ↦ true)

def appendControl (c : Control E n M R hR) (o : Query E n M R hR)
    (a : OracleAnswer (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M)) : Control E n M R hR :=
  if controlIsRunning E n M R hR c then
    Sum.inr (OraclePolicy.appendHistory (Domain E M R hR) (controlHistory E n M R hR c) (o,a))
  else Sum.inl (controlOutput E n M R hR c)

def shouldRelease (c : ConeCounter.State n) (i : Fin n) : Bool :=
  decide (ConeCounter.threshold n ≤ (insert i c.2).card)

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain E M R hR) (n := n) (dx := ConeProblem.primalDimension E M) Ω)

def prepare (seed : Ω) (s : State E n M R hR) : State E n M R hR :=
  {s with
    phase := nextPhase E n M R hR s
    pending := OracleSimulation.action (Domain E M R hR) P seed s.control
    pendingStage := s.progress.1
    release := false}

def paidQuery (q : ℝ) (s : State E n M R hR) (o : Query E n M R hR) (a : E) : State E n M R hR :=
  if s.pendingStage < M + 1 then
    let rows := ConeReferenceCache.putRow s.rows (stageIndex E n M R hR s) o.1 a
    let reply := ConeReferenceCache.replyFromCache R q s.pendingStage s.means rows o
    {s with
      control := appendControl E n M R hR s.control o reply
      progress := ConeCounter.step s.progress (some o.1)
      rows := rows
      phase := nextPhase E n M R hR s
      release := shouldRelease n s.progress o.1}
  else
    let reply := ConeReferenceCache.replyFromCache R q s.pendingStage s.means s.rows o
    {s with
      control := appendControl E n M R hR s.control o reply
      phase := nextPhase E n M R hR s
      release := false}

def paidUpdate (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E) : State E n M R hR :=
  if actionIsQuery E n M R hR s.pending then
    paidQuery E n M R hR q s (actionQuery E n M R hR hn s.pending) a
  else
    {s with
      control := Sum.inl (actionOutput E n M R hR s.pending)
      phase := nextPhase E n M R hR s
      release := false}

def freeUpdate (hn : 0 < n) (s : State E n M R hR) (a : E) : State E n M R hR :=
  if s.release then
    if s.pendingStage < M + 1 then
      let j := stageIndex E n M R hR s
      let rows := ConeReferenceCache.putRow s.rows j (releaseRow E n M R hR hn s) a
      let means := if s.phase.val = n + 1 then ConeReferenceCache.releaseMean rows s.means j else s.means
      {s with rows := rows, means := means, phase := nextPhase E n M R hR s}
    else {s with phase := nextPhase E n M R hR s}
  else {s with phase := nextPhase E n M R hR s}

def update (seed : Ω) (hn : 0 < n) (q : ℝ) (s : State E n M R hR) (a : E) : State E n M R hR :=
  if s.phase.val = 0 then prepare E n M R hR P seed s else
  if s.phase.val = 1 then paidUpdate E n M R hR hn q s a else
    freeUpdate E n M R hR hn s a

def requestedAnswer (rows : Fin (M + 1) → Fin n → E) (r : Request n M) : E :=
  r.elim (fun _ ↦ 0) (fun ji ↦ rows ji.1 ji.2)

def stepWithRows (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (s : State E n M R hR) : State E n M R hR :=
  update E n M R hR P seed hn q s (requestedAnswer E n M rows (request E n M R hR hn s))

def runWithRows (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) : ℕ → State E n M R hR
  | 0 => initial E n M R hR
  | t + 1 => stepWithRows E n M R hR P seed hn q rows (runWithRows seed hn q rows t)

def boundary (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → E) (t : ℕ) : State E n M R hR :=
  runWithRows E n M R hR P seed hn q rows ((n + 2) * t)

def output (seed : Ω) (s : State E n M R hR) : PrimalSpace (ConeProblem.primalDimension E M) :=
  OracleSimulation.finish (Domain E M R hR) P seed s.control

end

end NCConcave16991.Haar.ConeMachine
