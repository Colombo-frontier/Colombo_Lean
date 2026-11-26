import NCConcave16991.PersistentProgramInner

/-! # One complete persistent outer advance, implemented only through oracle replies -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.PersistentProgram

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

abbrev Noise (n b k : ℕ) := InnerAlgorithm.Seed n k × (Fin b → Fin n)

def fromProcessState (s : PersistentProcess.State dx dy) : OuterState dx dy := (s.center, s.estimate)
def toProcessState (s : OuterState dx dy) : PersistentProcess.State dx dy := ⟨s.1, s.2⟩

def innerSolveProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (k : ℕ) :
    OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy) (PrimalSpace dx)
      (InnerAlgorithm.Seed p.n k × OuterState dx dy) (2 * k) :=
  OracleProgram.map (innerProgram y0 hy0 k) Prod.snd measurable_snd

theorem eval_innerSolveProgram (P : Problem p dx dy K) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (k : ℕ) (ω : InnerAlgorithm.Seed p.n k) (s : OuterState dx dy) :
    OracleProgram.eval (innerSolveProgram (p := p) (dx := dx) y0 hy0 k) (oracleResponse P) (ω, s) =
      persistentInnerSolve P y0 hy0 k (toProcessState s) ω := by
  rw [innerSolveProgram, OracleProgram.eval_map, eval_innerProgram]
  exact (persistentInnerSolve_eq_estimatedOutput P y0 hy0 k (toProcessState s) ω).symm

abbrev EstimateInput (b k : ℕ) := (Noise p.n b k × OuterState dx dy) × PrimalSpace dx

def refreshProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (b k : ℕ) :
    OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy) (OuterState dx dy)
      (EstimateInput (p := p) (dx := dx) (dy := dy) b k) p.n :=
  OracleProgram.mapWithSeed
    (fullSignedPass K (fun a => anchorPoint y0 hy0 (a.2, 0))
      ((anchorPoint_measurable y0 hy0).comp (measurable_snd.prodMk measurable_const)))
    (fun a estimate => (a.2, estimate)) (by fun_prop)

def differenceProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (b k : ℕ) :
    OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy) (OuterState dx dy)
      (EstimateInput (p := p) (dx := dx) (dy := dy) b k) (2 * b) :=
  OracleProgram.mapWithSeed
    (signedDifferenceBatch K (fun a => a.1.1.2) (fun _ => by fun_prop)
      (fun a => anchorPoint y0 hy0 (a.2, 0)) (fun a => anchorPoint y0 hy0 a.1.2)
      ((anchorPoint_measurable y0 hy0).comp (measurable_snd.prodMk measurable_const))
      ((anchorPoint_measurable y0 hy0).comp (by fun_prop)))
    (fun a difference => (a.2, a.1.2.2 + difference)) (by fun_prop)

def estimateProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (b q k t : ℕ) :
    OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy) (OuterState dx dy)
      (EstimateInput (p := p) (dx := dx) (dy := dy) b k)
      (if (t + 1) % q = 0 then p.n else 2 * b) :=
  if h : (t + 1) % q = 0 then OracleProgram.castBudget (refreshProgram y0 hy0 b k) (by simp [h])
  else OracleProgram.castBudget (differenceProgram y0 hy0 b k) (by simp [h])

set_option backward.isDefEq.respectTransparency false in
theorem eval_estimateProgram (P : Problem p dx dy K) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (b q k t : ℕ) (a : EstimateInput (p := p) (dx := dx) (dy := dy) b k) :
    OracleProgram.eval (estimateProgram y0 hy0 b q k t) (oracleResponse P) a =
      (a.2, if (t + 1) % q = 0 then averageMap (signedComponentGradient P) (jointPoint a.2 y0)
        else a.1.2.2 + minibatchMean
          (fun i => signedComponentGradient P i (jointPoint a.2 y0) -
            signedComponentGradient P i (jointPoint a.1.2.1 y0)) a.1.1.2) := by
  by_cases h : (t + 1) % q = 0
  · simp only [estimateProgram, h, dite_true, OracleProgram.eval_castBudget, ite_true]
    rw [refreshProgram, OracleProgram.eval_mapWithSeed, eval_fullSignedPass]
    rfl
  · simp only [estimateProgram, h, dite_false, OracleProgram.eval_castBudget, ite_false]
    rw [differenceProgram, OracleProgram.eval_mapWithSeed, eval_signedDifferenceBatch]
    rfl

/-- A complete outer advance: actual 2k-query inner solve followed by exact refresh or fresh differences. -/
def advanceProgram (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (b q k t : ℕ) :
    OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy) (OuterState dx dy)
      (Noise p.n b k × OuterState dx dy)
      (2 * k + if (t + 1) % q = 0 then p.n else 2 * b) :=
  OracleProgram.bind
    (OracleProgram.withSeed (innerSolveProgram y0 hy0 k)
      (fun a : Noise p.n b k × OuterState dx dy => (a.1.1, a.2)) (by fun_prop))
    (estimateProgram y0 hy0 b q k t)

/-- The implemented stage is pointwise the actual persistent stochastic advance. -/
theorem eval_advanceProgram (P : Problem p dx dy K) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (b q k t : ℕ) (ω : Noise p.n b k) (s : OuterState dx dy) :
    OracleProgram.eval (advanceProgram (p := p) (dx := dx) y0 hy0 b q k t) (oracleResponse P) (ω, s) =
      fromProcessState (PersistentProcess.advance (signedComponentGradient P) y0 q
        (persistentInnerSolve P y0 hy0 k) t (toProcessState s) ω) := by
  rw [advanceProgram, OracleProgram.eval_bind, OracleProgram.eval_withSeed,
    eval_innerSolveProgram, eval_estimateProgram]
  rfl

end NCConcave16991.PersistentProgram
