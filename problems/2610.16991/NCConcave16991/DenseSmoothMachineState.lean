import NCConcave16991.DenseSmoothOracle
import NCConcave16991.DenseSmoothCounter
import NCConcave16991.ConeReferenceCache
import NCConcave16991.OracleSimulation

/-! # A public full-history interpreter with explicit paid row and release inputs -/

namespace NCConcave16991.DenseSmooth.Machine

noncomputable section

open Set MeasureTheory

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)

abbrev Domain := smoothDualDomain (parameters hn hρ T)
abbrev Query := OracleQuery n (primalDimension E T) (Domain n T hn ρ hρ)
abbrev Action := OraclePolicy.Action (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T)
abbrev Control := OracleSimulation.State (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T)
abbrev Rows := Fin (T + 1) → Fin n → E
abbrev Directions := Fin (T + 1) → E
abbrev RowIndex := Fin (T + 1) × Fin n

structure State where
  control : Control E n T hn ρ hρ
  progress : Counter.State n
  rows : Rows E n T
  directions : Directions E T

def initial : State E n T hn ρ hρ where
  control := Sum.inr (OraclePolicy.emptyHistory (Domain n T hn ρ hρ))
  progress := Counter.initial n
  rows := fun _ _ ↦ 0
  directions := fun _ ↦ 0

def stageIndex (s : State E n T hn ρ hρ) : Fin (T + 1) := ⟨s.progress.1 % (T + 1), Nat.mod_lt _ (by omega)⟩

def rowDirection (row : Fin n → E) : E := ((n : ℝ) * ρ)⁻¹ • ∑ i, row i

include hn hρ in
theorem rowDirection_eq (A : Table E n T ρ) (j : Fin (T + 1)) :
    rowDirection E n ρ (fun i ↦ A.row i j) = A.direction j := by
  have hnonzero : (n : ℝ) * ρ ≠ 0 := mul_ne_zero (by exact_mod_cast hn.ne') hρ.ne'
  rw [rowDirection, A.row_sum, smul_smul, inv_mul_cancel₀ hnonzero, one_smul]

def appendControl (c : Control E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a : OracleAnswer (primalDimension E T) 0) : Control E n T hn ρ hρ :=
  c.elim Sum.inl (fun history ↦ Sum.inr (OraclePolicy.appendHistory (Domain n T hn ρ hρ) history (o, a)))

def cachedReply (s : State E n T hn ρ hρ) (rows : Rows E n T) (o : Query E n T hn ρ hρ) :
    OracleAnswer (primalDimension E T) 0 :=
  referenceReply hn hρ s.progress.1 s.directions (fun i j ↦ rows j i) o

def shouldRelease (r : ℕ) (s : State E n T hn ρ hρ) (i : Fin n) : Bool :=
  decide (r ≤ (insert i s.progress.2).card)

/-- The one selected row is paid. A complete stage is used only in the
release branch, after forming the reply at the pre-query frontier. -/
def paidQuery (r : ℕ) (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a : E) (releasedRows : Fin n → E) : State E n T hn ρ hρ :=
  if s.progress.1 < T + 1 then
    let j := stageIndex E n T hn ρ hρ s
    let paidRows := ConeReferenceCache.putRow s.rows j o.1 a
    let reply := cachedReply E n T hn ρ hρ s paidRows o
    {control := appendControl E n T hn ρ hρ s.control o reply
     progress := Counter.step r s.progress (some o.1)
     rows := if shouldRelease E n T hn ρ hρ r s o.1 then Function.update paidRows j releasedRows else paidRows
     directions := if shouldRelease E n T hn ρ hρ r s o.1 then
       Function.update s.directions j (rowDirection E n ρ releasedRows) else s.directions}
  else
    {s with control := appendControl E n T hn ρ hρ s.control o (cachedReply E n T hn ρ hρ s s.rows o)}

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

def request (seed : Ω) (s : State E n T hn ρ hρ) : Option (RowIndex n T) :=
  (OracleSimulation.action (Domain n T hn ρ hρ) P seed s.control).elim (fun _ ↦ none)
    (fun o ↦ if s.progress.1 < T + 1 then some (stageIndex E n T hn ρ hρ s, o.1) else none)

def step (seed : Ω) (r : ℕ) (s : State E n T hn ρ hρ) (a : E) (releasedRows : Fin n → E) : State E n T hn ρ hρ :=
  (OracleSimulation.action (Domain n T hn ρ hρ) P seed s.control).elim
    (fun x ↦ {s with control := Sum.inl x})
    (fun o ↦ paidQuery E n T hn ρ hρ r s o a releasedRows)

def stepWithRows (seed : Ω) (r : ℕ) (rows : Rows E n T) (s : State E n T hn ρ hρ) : State E n T hn ρ hρ :=
  let answer := (request E n T hn ρ hρ P seed s).elim 0 (fun ji ↦ rows ji.1 ji.2)
  step E n T hn ρ hρ P seed r s answer (rows (stageIndex E n T hn ρ hρ s))

def runWithRows (seed : Ω) (r : ℕ) (rows : Rows E n T) : ℕ → State E n T hn ρ hρ
  | 0 => initial E n T hn ρ hρ
  | t + 1 => stepWithRows E n T hn ρ hρ P seed r rows (runWithRows seed r rows t)

def output (seed : Ω) (s : State E n T hn ρ hρ) : PrimalSpace (primalDimension E T) :=
  OracleSimulation.finish (Domain n T hn ρ hρ) P seed s.control

end

end NCConcave16991.DenseSmooth.Machine
