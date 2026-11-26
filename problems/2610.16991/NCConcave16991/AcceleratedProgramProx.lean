import NCConcave16991.AcceleratedProgramSolver
import NCConcave16991.AcceleratedStochasticProx

/-!
# The full accelerated inexact proximal algorithm as an oracle program

Each stage extrapolates using its reply-derived state, calls the actual
finite-seed SVRG engine, and updates the unprojected estimate sequence and
weighted primal sum. The complete output is the analyzed stochasticProxOutput.
-/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.AcceleratedProgram

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

abbrev State := Accelerated.State (PrimalSpace dx) (DualSpace dy)
abbrev Result := Accelerated.ProxResult (X := PrimalSpace dx) (Y := DualSpace dy)

theorem center_measurable (τ : ℝ) (k : ℕ) :
    Measurable (Accelerated.center (X := PrimalSpace dx) (Y := DualSpace dy) τ k) := by
  unfold Accelerated.center
  fun_prop

def stageUpdate (τ : ℝ) (k : ℕ)
    (s : PrimalSpace dx × State (dx := dx) (dy := dy)) (r : Result (dx := dx) (dy := dy)) :
    PrimalSpace dx × State (dx := dx) (dy := dy) :=
  (s.1, ⟨r.y, s.2.z - Accelerated.weight τ k • (τ • (Accelerated.center τ k s.2 - r.y)),
    s.2.primalSum + Accelerated.weight τ k • r.x⟩)

theorem stageUpdate_measurable (τ : ℝ) (k : ℕ) :
    Measurable (Function.uncurry (stageUpdate (dx := dx) (dy := dy) τ k)) := by
  let A := (PrimalSpace dx × State (dx := dx) (dy := dy)) × Result (dx := dx) (dy := dy)
  have hc : Measurable (fun a : A ↦ a.1.1) := by fun_prop
  have hs : Measurable (fun a : A ↦ a.1.2) := by fun_prop
  have hy := Accelerated.proxResult_y_measurable.comp (measurable_snd : Measurable (fun a : A ↦ a.2))
  have hx := Accelerated.proxResult_x_measurable.comp (measurable_snd : Measurable (fun a : A ↦ a.2))
  have hz := Accelerated.state_z_measurable.comp hs
  have hm := Accelerated.state_primalSum_measurable.comp hs
  have hv := (center_measurable (dx := dx) (dy := dy) τ k).comp hs
  have hτ : Measurable (fun _ : A ↦ τ) := measurable_const
  have ha : Measurable (fun _ : A ↦ Accelerated.weight τ k) := measurable_const
  exact hc.prodMk (Accelerated.state_mk_measurable.comp
    (hy.prodMk ((hz.sub (ha.smul (hτ.smul (hv.sub hy)))).prodMk (hm.add (ha.smul hx)))))

def proxEngineBudget (p : ProblemParameters) (Δ τ δ failure : ℝ) : ℕ :=
  SVRG.residualQueryBudget p.n (4 * p.L) τ
    (Accelerated.solverEpochCount p Δ τ (Accelerated.proxTolerance p Δ τ δ) failure)

def stageProgram (Δ τ δ failure : ℝ) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (k : ℕ) :
    OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy)
      (PrimalSpace dx × State (dx := dx) (dy := dy))
      (Accelerated.SolverSeed p Δ τ (Accelerated.proxTolerance p Δ τ δ) failure ×
        (PrimalSpace dx × State (dx := dx) (dy := dy)))
      (proxEngineBudget p Δ τ δ failure) :=
  OracleProgram.mapWithSeed
    (OracleProgram.withSeed
      (solverProgram Δ τ (Accelerated.proxTolerance p Δ τ δ) failure y0 hy0)
      (fun a ↦ (a.1, (a.2.1, Accelerated.center τ k a.2.2)))
      (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
        ((center_measurable (dx := dx) (dy := dy) τ k).comp (measurable_snd.comp measurable_snd)))))
    (fun a r ↦ stageUpdate τ k a.2 r)
    ((stageUpdate_measurable τ k).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

def statesProgram (Δ τ δ failure : ℝ) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    (k : ℕ) → OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy)
      (PrimalSpace dx × State (dx := dx) (dy := dy))
      (FiniteProcess.History (Accelerated.SolverSeed p Δ τ (Accelerated.proxTolerance p Δ τ δ) failure) k ×
        PrimalSpace dx) (k * proxEngineBudget p Δ τ δ failure)
  | 0 => OracleProgram.castBudget
      (OracleProgram.pure (fun a ↦ (a.2, (⟨y0, y0, 0⟩ : State (dx := dx) (dy := dy))))
        (measurable_snd.prodMk measurable_const)) (by simp)
  | k + 1 => OracleProgram.castBudget
      (OracleProgram.bind
        (OracleProgram.withSeed (statesProgram Δ τ δ failure y0 hy0 k)
          (fun a : FiniteProcess.History
              (Accelerated.SolverSeed p Δ τ (Accelerated.proxTolerance p Δ τ δ) failure) (k + 1) × PrimalSpace dx ↦
            (a.1.1, a.2)) ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        (OracleProgram.withSeed (stageProgram Δ τ δ failure y0 hy0 k)
          (fun a : (FiniteProcess.History
              (Accelerated.SolverSeed p Δ τ (Accelerated.proxTolerance p Δ τ δ) failure) (k + 1) × PrimalSpace dx) ×
              (PrimalSpace dx × State (dx := dx) (dy := dy)) ↦
            (a.1.1.2, a.2))
          ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))) (by ring)

def proxProgram (Δ τ δ failure : ℝ) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    OracleProgram.Fixed (OracleQuery p.n dx K) (OracleAnswer dx dy) (PrimalSpace dx)
      (Accelerated.ProxSeed p Δ τ δ failure × PrimalSpace dx)
      (Accelerated.horizon τ p.diameter δ * proxEngineBudget p Δ τ δ failure) :=
  OracleProgram.map (statesProgram Δ τ δ failure y0 hy0 (Accelerated.horizon τ p.diameter δ))
    (fun a ↦ (Accelerated.mass τ (Accelerated.horizon τ p.diameter δ))⁻¹ • a.2.primalSum)
    (by
      have hmass : Measurable (fun _ : PrimalSpace dx × State (dx := dx) (dy := dy) ↦
          (Accelerated.mass τ (Accelerated.horizon τ p.diameter δ))⁻¹) := measurable_const
      exact hmass.smul (Accelerated.state_primalSum_measurable.comp measurable_snd))

theorem randomState_succ {I : Type*} (τ : ℝ) (fallback : I)
    (sample : ℕ → DualSpace dy → I → Result (dx := dx) (dy := dy))
    (y0 : DualSpace dy) (k : ℕ) (h : FiniteProcess.History I k) (i : I) :
    Accelerated.randomState τ fallback sample y0 (k + 1) (h, i) =
      Accelerated.advance τ (fun j v ↦ sample j v i) k
        (Accelerated.randomState τ fallback sample y0 k h) := by
  have hs := Accelerated.states_congr_prefix τ
    (Accelerated.replay fallback sample (k + 1) (h, i))
    (Accelerated.replay fallback sample k h) y0 k
    (fun j hj v ↦ Accelerated.replay_extend fallback sample k h i j hj v)
  change Accelerated.advance τ (Accelerated.replay fallback sample (k + 1) (h, i)) k
    (Accelerated.states τ (Accelerated.replay fallback sample (k + 1) (h, i)) y0 k) = _
  rw [hs]
  simp only [Accelerated.advance, Accelerated.replay, Accelerated.seedAt, ite_true]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem eval_stageProgram (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (Δ τ δ failure : ℝ) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (k : ℕ)
    (ω : Accelerated.SolverSeed p Δ τ (Accelerated.proxTolerance p Δ τ δ) failure)
    (s : PrimalSpace dx × State (dx := dx) (dy := dy)) :
    OracleProgram.eval (stageProgram (p := p) (dx := dx) Δ τ δ failure y0 hy0 k) (oracleResponse P) (ω, s) =
      (s.1, Accelerated.advance τ
        (fun j v ↦ Accelerated.proxSample P hAS Δ τ δ failure y0 hy0 s.1 j v ω) k s.2) := by
  rw [stageProgram, OracleProgram.eval_mapWithSeed, OracleProgram.eval_withSeed, eval_solverProgram P hAS]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem eval_statesProgram (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (Δ τ δ failure : ℝ) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (k : ℕ)
    (h : FiniteProcess.History (Accelerated.SolverSeed p Δ τ (Accelerated.proxTolerance p Δ τ δ) failure) k)
    (c : PrimalSpace dx) :
    OracleProgram.eval (statesProgram (p := p) (dx := dx) Δ τ δ failure y0 hy0 k) (oracleResponse P) (h, c) =
      (c, Accelerated.randomState τ
        (Accelerated.solverFallback p Δ τ (Accelerated.proxTolerance p Δ τ δ) failure)
        (Accelerated.proxSample P hAS Δ τ δ failure y0 hy0 c) y0 k h) := by
  induction k with
  | zero =>
    simp only [statesProgram, OracleProgram.eval_castBudget, OracleProgram.eval_pure]
    rfl
  | succ k ih =>
    simp only [statesProgram, OracleProgram.eval_castBudget, OracleProgram.eval_bind,
      OracleProgram.eval_withSeed, ih, eval_stageProgram P hAS]
    rw [randomState_succ]

set_option backward.isDefEq.respectTransparency false in
theorem eval_proxProgram (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (Δ τ δ failure : ℝ) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (h : Accelerated.ProxSeed p Δ τ δ failure) (c : PrimalSpace dx) :
    OracleProgram.eval (proxProgram (p := p) (dx := dx) Δ τ δ failure y0 hy0) (oracleResponse P) (h, c) =
      Accelerated.stochasticProxOutput P hAS Δ τ δ failure y0 hy0 c h := by
  rw [proxProgram, OracleProgram.eval_map, eval_statesProgram P hAS]
  rfl

end NCConcave16991.AcceleratedProgram
