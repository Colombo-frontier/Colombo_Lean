import NCConcave16991.PersistentProgramAdvance
import NCConcave16991.OracleProgramControl
import NCConcave16991.OracleProgramCompiler
import NCConcave16991.ProgramAccounting
import NCConcave16991.PersistentPublic

/-!
# A public reply-driven program for the complete persistent algorithm

Constructors use only public parameters, the known dual domain, an initial
point and a private seed. The unknown Problem occurs only in correctness
theorems. A private uniform output index selects a chronological prefix, and
ignored feasible queries pad that prefix to a single public fixed budget.
-/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.PersistentProgram

noncomputable section

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

def prefixBudget (n q b k : ℕ) : ℕ → ℕ
  | 0 => n
  | t + 1 => prefixBudget n q b k t + (2 * k + if (t + 1) % q = 0 then n else 2 * b)

theorem prefixBudget_eq (n q b k t : ℕ) :
    prefixBudget n q b k t = persistentChronologicalBudget n q b k t := by
  induction t with
  | zero => simp [prefixBudget, persistentChronologicalBudget]
  | succ t ih =>
    simp only [prefixBudget, ih, persistentChronologicalBudget, Finset.sum_range_succ]
    omega

theorem prefixBudget_le_full (n q b k S : ℕ) (j : Fin S) :
    prefixBudget n q b k j ≤ persistentChronologicalBudget n q b k S := by
  rw [prefixBudget_eq]
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_of_lt j.isLt))

def processProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (b q k : ℕ)
    (x0 : PrimalSpace dx) : (t : ℕ) →
    OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy) (OuterState dx dy)
      (FiniteProcess.History (Noise p.n b k) t) (prefixBudget p.n q b k t)
  | 0 => OracleProgram.map
      (fullSignedPass K (fun _ : FiniteProcess.History (Noise p.n b k) 0 ↦
        (⟨jointPoint x0 y0, hy0⟩ : productDomain dx K)) measurable_const)
      (fun v ↦ (x0, v)) (measurable_const.prodMk measurable_id)
  | t + 1 => OracleProgram.bind
      (OracleProgram.withSeed (processProgram y0 hy0 b q k x0 t)
        (fun h : FiniteProcess.History (Noise p.n b k) (t + 1) ↦ h.1) measurable_fst)
      (OracleProgram.withSeed (advanceProgram y0 hy0 b q k t)
        (fun a : FiniteProcess.History (Noise p.n b k) (t + 1) × OuterState dx dy ↦
          (a.1.2, a.2)) ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

set_option backward.isDefEq.respectTransparency false in
theorem eval_processProgram (P : Problem p dx dy K) (y0 : DualSpace dy)
    (hy0 : y0 ∈ K.carrier) (b q k : ℕ) (x0 : PrimalSpace dx) (t : ℕ)
    (h : FiniteProcess.History (Noise p.n b k) t) :
    OracleProgram.eval (processProgram y0 hy0 b q k x0 t) (oracleResponse P) h =
      fromProcessState (PersistentProcess.process (signedComponentGradient P) y0 q
        (persistentInnerSolve P y0 hy0 k) x0 t h) := by
  induction t with
  | zero =>
    simp only [processProgram, OracleProgram.eval_map, eval_fullSignedPass]
    rfl
  | succ t ih =>
    simp only [processProgram, OracleProgram.eval_bind, OracleProgram.eval_withSeed, ih,
      eval_advanceProgram]
    rfl

def selectedProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (b q k S : ℕ)
    (x0 : PrimalSpace dx) :
    OracleProgram.ProblemProgram K (n := p.n) (dx := dx)
      (FiniteProcess.History (Noise p.n b k) S × Fin S)
      (persistentChronologicalBudget p.n q b k S) :=
  OracleProgram.select Prod.snd measurable_snd (fun j : Fin S ↦
    OracleProgram.padTo
      (OracleProgram.withSeed
        (OracleProgram.map (processProgram y0 hy0 b q k x0 j) Prod.fst measurable_fst)
        (fun ω : FiniteProcess.History (Noise p.n b k) S × Fin S ↦
          FiniteProcess.historyPrefix j S (Nat.le_of_lt j.isLt) ω.1)
        (measurable_of_countable _))
      (prefixBudget_le_full p.n q b k S j)
      (fun _ ↦ (⟨0, p.n_pos⟩, x0, ⟨y0, hy0⟩)) measurable_const)

set_option backward.isDefEq.respectTransparency false in
/-- The actual compiled numerical output is exactly the analyzed independent
selected output, for every private seed and every unknown admissible Problem. -/
theorem eval_selectedProgram (P : Problem p dx dy K) (y0 : DualSpace dy)
    (hy0 : y0 ∈ K.carrier) (b q k S : ℕ) (x0 : PrimalSpace dx)
    (h0 : P.initialPoint = x0)
    (ω : FiniteProcess.History (Noise p.n b k) S × Fin S) :
    OracleProgram.eval (selectedProgram y0 hy0 b q k S x0) (oracleResponse P) ω =
      persistentSampleOutput (b := b) (S := S) P y0 hy0 q k ω := by
  simp only [selectedProgram, OracleProgram.eval_select, OracleProgram.eval_padTo,
    OracleProgram.eval_withSeed, OracleProgram.eval_map, eval_processProgram]
  rw [← h0]
  rfl

end

end NCConcave16991.PersistentProgram
