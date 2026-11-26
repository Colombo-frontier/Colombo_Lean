import NCConcave16991.DenseSmoothMachineState

/-! # The actual alignment-triggered sequential reference interaction

A completion is tested on the query before its reply. It reveals the
completed stage, supplies one selected successor initialization row,
and advances by at most one stage. A noncompletion reply uses only the
paid current row and the previously known data.
-/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open Set MeasureTheory

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)

abbrev Domain := Machine.Domain n T hn ρ hρ
abbrev Query := Machine.Query E n T hn ρ hρ
abbrev Control := Machine.Control E n T hn ρ hρ

structure State where
  base : Machine.State E n T hn ρ hρ
  assigned : Fin (T + 1) → ℕ

def initial : State E n T hn ρ hρ := ⟨Machine.initial E n T hn ρ hρ, fun _ ↦ 0⟩

def frontier (s : State E n T hn ρ hρ) : ℕ := s.base.progress.1
def stageIndex (s : State E n T hn ρ hρ) : Fin (T + 1) := Machine.stageIndex E n T hn ρ hρ s.base
def successorIndex (s : State E n T hn ρ hρ) : Fin (T + 1) :=
  ⟨(frontier E n T hn ρ hρ s + 1) % (T + 1), Nat.mod_lt _ (by omega)⟩

def paidQuery (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a : E) (complete : Bool) (direction : E) (releasedRows : Fin n → E) (initializationRow : E) : State E n T hn ρ hρ :=
  if frontier E n T hn ρ hρ s < T + 1 then
    let j := stageIndex E n T hn ρ hρ s
    let paidRows := ConeReferenceCache.putRow s.base.rows j o.1 a
    let assigned := Function.update s.assigned j (s.assigned j + 1)
    if complete then
      let f := frontier E n T hn ρ hρ s + 1
      let oldRows := Function.update paidRows j releasedRows
      let directions := Function.update s.base.directions j direction
      let rows := if f < T + 1 then
        ConeReferenceCache.putRow oldRows (successorIndex E n T hn ρ hρ s) o.1 initializationRow else oldRows
      let seen := if f < T + 1 then {o.1} else ∅
      let reply := referenceReply hn hρ f directions (fun i j ↦ rows j i) o
      ⟨⟨Machine.appendControl E n T hn ρ hρ s.base.control o reply, (f, seen), rows, directions⟩, assigned⟩
    else
      let reply := Machine.cachedReply E n T hn ρ hρ s.base paidRows o
      ⟨⟨Machine.appendControl E n T hn ρ hρ s.base.control o reply,
        (frontier E n T hn ρ hρ s, insert o.1 s.base.progress.2), paidRows, s.base.directions⟩, assigned⟩
  else
    ⟨{s.base with control := (Machine.appendControl E n T hn ρ hρ s.base.control o
      (Machine.cachedReply E n T hn ρ hρ s.base s.base.rows o))}, s.assigned⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

def action (seed : Ω) (s : State E n T hn ρ hρ) :=
  OracleSimulation.action (Domain n T hn ρ hρ) P seed s.base.control

def step (seed : Ω) (s : State E n T hn ρ hρ) (a : E) (complete : Bool)
    (direction : E) (releasedRows : Fin n → E) (initializationRow : E) : State E n T hn ρ hρ :=
  (action E n T hn ρ hρ P seed s).elim
    (fun x ↦ ⟨{s.base with control := Sum.inl x}, s.assigned⟩)
    (fun o ↦ paidQuery E n T hn ρ hρ s o a complete direction releasedRows initializationRow)

def completion (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ) : Bool :=
  (action E n T hn ρ hρ P seed s).elim (fun _ ↦ false) (fun o ↦
    if frontier E n T hn ρ hρ s < T + 1 then
      decide ((5 / 32 : ℝ) < coordinate A.direction ((primalCoordinates E T).symm o.2.1)
        (stageIndex E n T hn ρ hρ s)) else false)

def request (seed : Ω) (s : State E n T hn ρ hρ) : Option (Machine.RowIndex n T) :=
  (action E n T hn ρ hρ P seed s).elim (fun _ ↦ none) (fun o ↦
    if frontier E n T hn ρ hρ s < T + 1 then some (stageIndex E n T hn ρ hρ s, o.1) else none)

def freshRequest (seed : Ω) (s : State E n T hn ρ hρ) : Option (Machine.RowIndex n T) :=
  (request E n T hn ρ hρ P seed s).filter (fun ji ↦ ji.2 ∉ s.base.progress.2)

def initializationRequest (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ) : Option (Machine.RowIndex n T) :=
  if completion E n T hn ρ hρ P seed A s then
    (action E n T hn ρ hρ P seed s).elim (fun _ ↦ none) (fun o ↦
      if frontier E n T hn ρ hρ s + 1 < T + 1 then some (successorIndex E n T hn ρ hρ s, o.1) else none)
  else none

def stepWithTable (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ) : State E n T hn ρ hρ :=
  let answer := (request E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ A.row ji.2 ji.1)
  let init := (initializationRequest E n T hn ρ hρ P seed A s).elim 0 (fun ji ↦ A.row ji.2 ji.1)
  step E n T hn ρ hρ P seed s answer (completion E n T hn ρ hρ P seed A s)
    (A.direction (stageIndex E n T hn ρ hρ s)) (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s)) init

/-- The censored continuation has no alignment test, direction release or
successor access: its only current-stage input is the selected row. -/
def precompletionStep (seed : Ω) (s : State E n T hn ρ hρ) (a : E) : State E n T hn ρ hρ :=
  step E n T hn ρ hρ P seed s a false 0 (fun _ ↦ 0) 0

def runWithTable (seed : Ω) (A : Table E n T ρ) : ℕ → State E n T hn ρ hρ
  | 0 => initial E n T hn ρ hρ
  | t + 1 => stepWithTable E n T hn ρ hρ P seed A (runWithTable seed A t)

def output (seed : Ω) (s : State E n T hn ρ hρ) : PrimalSpace (primalDimension E T) :=
  OracleSimulation.finish (Domain n T hn ρ hρ) P seed s.base.control

end

end NCConcave16991.DenseSmooth.Revelation
