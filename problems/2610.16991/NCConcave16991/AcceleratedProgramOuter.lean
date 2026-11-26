import NCConcave16991.AcceleratedProgramProx
import NCConcave16991.AcceleratedOuterProbability
import NCConcave16991.AcceleratedBudget
import NCConcave16991.OracleProgramControl
import NCConcave16991.OracleProgramCompiler

/-! # A public fixed-budget oracle program for accelerated outer iterations -/

open Set MeasureTheory

namespace NCConcave16991.AcceleratedProgram

noncomputable section

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

def outerStepBudget (p : ProblemParameters) : ℕ :=
  Accelerated.dualHorizon p * Accelerated.publicResidualBudget p

def outerPrefixProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) :
    (t : ℕ) → OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy) (PrimalSpace dx)
      (FiniteProcess.History (Accelerated.OuterNoise p) t) (t * outerStepBudget p)
  | 0 => OracleProgram.castBudget
      (OracleProgram.pure (fun _ : FiniteProcess.History (Accelerated.OuterNoise p) 0 ↦ x0) measurable_const)
      (by simp)
  | t + 1 => OracleProgram.castBudget
      (OracleProgram.bind
        (OracleProgram.withSeed (outerPrefixProgram y0 hy0 x0 t)
          (fun h : FiniteProcess.History (Accelerated.OuterNoise p) (t + 1) ↦ h.1) measurable_fst)
        (OracleProgram.withSeed
          (proxProgram (Accelerated.gapCap p) (Accelerated.dualRegularization p)
            (Accelerated.outerTolerance p) (Accelerated.stageFailure p) y0 hy0)
          (fun a : FiniteProcess.History (Accelerated.OuterNoise p) (t + 1) × PrimalSpace dx ↦
            (a.1.2, a.2)) ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      (by change t * outerStepBudget p + outerStepBudget p = (t + 1) * outerStepBudget p; ring)

set_option backward.isDefEq.respectTransparency false in
theorem eval_outerPrefixProgram (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) (h0 : P.initialPoint = x0)
    (t : ℕ) (h : FiniteProcess.History (Accelerated.OuterNoise p) t) :
    OracleProgram.eval (outerPrefixProgram y0 hy0 x0 t) (oracleResponse P) h =
      Accelerated.publicCenter P hAS y0 hy0 t h := by
  induction t with
  | zero =>
    simp only [outerPrefixProgram, OracleProgram.eval_castBudget, OracleProgram.eval_pure]
    rw [← h0]
    rfl
  | succ t ih =>
    simp only [outerPrefixProgram, OracleProgram.eval_castBudget, OracleProgram.eval_bind,
      OracleProgram.eval_withSeed, ih, eval_proxProgram P hAS]
    rfl

theorem outerPrefixBudget_le (p : ProblemParameters) (j : Fin (Accelerated.outerHorizon p)) :
    j.val * outerStepBudget p ≤ Accelerated.publicAcceleratedBudget p := by
  calc
    _ ≤ Accelerated.outerHorizon p * outerStepBudget p :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt j.isLt)
    _ = _ := by dsimp [outerStepBudget, Accelerated.publicAcceleratedBudget]; ring

def selectedOuterProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) :
    OracleProgram.ProblemProgram K (n := p.n) (dx := dx)
      (Accelerated.OuterHistory p × Fin (Accelerated.outerHorizon p))
      (Accelerated.publicAcceleratedBudget p) :=
  OracleProgram.select Prod.snd measurable_snd (fun j : Fin (Accelerated.outerHorizon p) ↦
    OracleProgram.padTo
      (OracleProgram.withSeed (outerPrefixProgram y0 hy0 x0 j)
        (fun ω : Accelerated.OuterHistory p × Fin (Accelerated.outerHorizon p) ↦
          FiniteProcess.historyPrefix j (Accelerated.outerHorizon p) (Nat.le_of_lt j.isLt) ω.1)
        (measurable_of_countable _))
      (outerPrefixBudget_le p j)
      (fun _ ↦ (⟨0, p.n_pos⟩, x0, ⟨y0, hy0⟩)) measurable_const)

set_option backward.isDefEq.respectTransparency false in
theorem eval_selectedOuterProgram (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (x0 : PrimalSpace dx) (h0 : P.initialPoint = x0)
    (ω : Accelerated.OuterHistory p × Fin (Accelerated.outerHorizon p)) :
    OracleProgram.eval (selectedOuterProgram y0 hy0 x0) (oracleResponse P) ω =
      Accelerated.outerOutput P hAS y0 hy0 ω := by
  simp only [selectedOuterProgram, OracleProgram.eval_select, OracleProgram.eval_padTo,
    OracleProgram.eval_withSeed, eval_outerPrefixProgram P hAS y0 hy0 x0 h0]
  simp only [Accelerated.outerOutput, Accelerated.checkedPath,
    dite_eq_left (Nat.le_of_lt ω.2.isLt)]

end

end NCConcave16991.AcceleratedProgram
