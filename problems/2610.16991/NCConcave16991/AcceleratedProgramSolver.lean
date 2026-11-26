import NCConcave16991.SVRGProgramSolver
import NCConcave16991.AcceleratedProgramDomain
import NCConcave16991.AcceleratedProgramState
import NCConcave16991.AcceleratedSVRGSolver

/-!
# The actual accelerated proximal saddle solver as a reply-driven program

The input parameter (c,v) may be computed from preceding oracle replies.
The program only uses the known ball/domain geometry, public corrections,
private component identities, and exact supplied component-gradient replies.
-/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.AcceleratedProgram

variable {dx dy : ℕ} {D : ℝ} {K : KnownDualDomain dy D}
  {Θ : Type*} [MeasurableSpace Θ]

def extractResult {F : SVRGProgram.DomainFamily (dx := dx) K Θ}
    (r : SVRGProgram.Result F) : Accelerated.ProxResult (X := PrimalSpace dx) (Y := DualSpace dy) :=
  ⟨r.1.2.1.fst, r.1.2.1.snd, r.1.2.2.1.fst, r.1.2.2.1.snd⟩

theorem extractResult_measurable {F : SVRGProgram.DomainFamily (dx := dx) K Θ} :
    Measurable (extractResult (F := F)) := by
  have hp : Measurable (fun r : SVRGProgram.Result F ↦ r.1.2.1) := by fun_prop
  have hn : Measurable (fun r : SVRGProgram.Result F ↦ r.1.2.2.1) := by fun_prop
  have hfst := (WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.measurable
  have hsnd := (WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.measurable
  exact Accelerated.proxResult_mk_measurable.comp
    ((hfst.comp hp).prodMk ((hsnd.comp hp).prodMk ((hfst.comp hn).prodMk (hsnd.comp hn))))

variable {p : ProblemParameters} {K' : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

/-- A public residual engine; no unknown Problem is an argument of the constructor. -/
def solverProgram (Δ τ ζ failure : ℝ) (y0 : DualSpace dy) (hy0 : y0 ∈ K'.carrier) :
    OracleProgram.Fixed (OracleQuery p.n dx K') (OracleAnswer dx dy)
      (Accelerated.ProxResult (X := PrimalSpace dx) (Y := DualSpace dy))
      (Accelerated.SolverSeed p Δ τ ζ failure × Parameter dx dy)
      (SVRG.residualQueryBudget p.n (4 * p.L) τ (Accelerated.solverEpochCount p Δ τ ζ failure)) :=
  OracleProgram.map
    (OracleProgram.withSeed
      (SVRGProgram.engineProgram (domainFamily p Δ K' (dx := dx))
        (correction p τ) (correction_continuous p τ).measurable
        (4 * p.L) τ (Accelerated.solverEpochCount p Δ τ ζ failure))
      (fun a : Accelerated.SolverSeed p Δ τ ζ failure × Parameter dx dy ↦
        (a.1, anchor p Δ K' y0 hy0 a.2))
      (measurable_fst.prodMk ((anchor_measurable p Δ K' y0 hy0).comp measurable_snd)))
    extractResult extractResult_measurable

set_option backward.isDefEq.respectTransparency false in
theorem eval_solverProgram (P : Problem p dx dy K') (hAS : P.averagedSmooth)
    (Δ τ ζ failure : ℝ) (y0 : DualSpace dy) (hy0 : y0 ∈ K'.carrier)
    (c : PrimalSpace dx) (v : DualSpace dy) (ω : Accelerated.SolverSeed p Δ τ ζ failure) :
    OracleProgram.eval (solverProgram (p := p) (dx := dx) Δ τ ζ failure y0 hy0)
      (oracleResponse P) (ω, (c, v)) =
      Accelerated.solverResult P hAS Δ τ ζ failure y0 hy0 c v ω := by
  rw [solverProgram, OracleProgram.eval_map, OracleProgram.eval_withSeed, SVRGProgram.eval_engineProgram]
  have hT : (fun θ : Parameter dx dy ↦ averageMap
      (fun i z ↦ signedComponentGradient P i z + correction p τ (θ, z))) =
      (fun θ ↦ Accelerated.proximalOperator (Accelerated.ballSaddle P hAS Δ y0 θ.1) τ θ.2) := by
    funext θ z
    change averageMap (Accelerated.proximalComponents P τ θ.2 θ.1) z = _
    rw [Accelerated.average_proximalComponents, Accelerated.proximalOperator_ballSaddle]
  rw [hT]
  rfl

end NCConcave16991.AcceleratedProgram
