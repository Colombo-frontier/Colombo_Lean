import NCConcave16991.AcceleratedSVRGOperator

/-! # A genuine finite-seed SVRG solver, uniformly over adaptive dual extrapolations -/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.Accelerated

/-- The public epoch count depends only on public radii and tolerances, not on v. -/
def solverEpochCount (p : ProblemParameters) (Δ τ ζ failure : ℝ) : ℕ :=
  SVRG.residualEpochCount (4 * p.L) (2 * publicRadius p Δ + p.diameter) ζ failure

abbrev SolverSeed (p : ProblemParameters) (Δ τ ζ failure : ℝ) :=
  FiniteProcess.History (InnerAlgorithm.Seed p.n (SVRG.epochLength (4 * p.L) τ))
    (solverEpochCount p Δ τ ζ failure)

variable (p : ProblemParameters) [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

def solverLaw (Δ τ ζ failure : ℝ) : Measure (SolverSeed p Δ τ ζ failure) :=
  SVRG.epochsLaw (n := p.n) (4 * p.L) τ (solverEpochCount p Δ τ ζ failure)

instance solverLaw_probability (Δ τ ζ failure : ℝ) : IsProbabilityMeasure (solverLaw p Δ τ ζ failure) := by
  unfold solverLaw
  infer_instance

variable {p} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

/-- The actual SVRG epochs followed by a projected full step and explicit normal extraction. -/
def solverResult (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ τ ζ failure : ℝ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) (v : DualSpace dy)
    (ω : SolverSeed p Δ τ ζ failure) : ProxResult (X := PrimalSpace dx) (Y := DualSpace dy) :=
  projectedResult (ballSaddle P hAS Δ y0 c) τ v (4 * p.L)
    (SVRG.epochsIterate (feasibleProduct (ballSaddle P hAS Δ y0 c))
      (feasibleProduct_nonempty _) (feasibleProduct_closed _) (feasibleProduct_convex _)
      (proximalComponents P τ v c) (proximalAnchor P hAS Δ y0 hy0 c) (4 * p.L) τ
      (solverEpochCount p Δ τ ζ failure) ω)

def solverBad (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ τ ζ failure : ℝ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) (v : DualSpace dy)
    (ω : SolverSeed p Δ τ ζ failure) : Prop :=
  ζ < ‖jointResidual (ballSaddle P hAS Δ y0 c) τ v (solverResult P hAS Δ τ ζ failure y0 hy0 c v ω)‖

/-- The only observable failure is the actual computed norm test; feasibility and normals are automatic. -/
theorem solverResult_jointCheck (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ τ ζ failure : ℝ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) (v : DualSpace dy)
    (ω : SolverSeed p Δ τ ζ failure) (hgood : ¬solverBad P hAS Δ τ ζ failure y0 hy0 c v ω) :
    JointCheck (ballSaddle P hAS Δ y0 c) τ ζ v (solverResult P hAS Δ τ ζ failure y0 hy0 c v ω) := by
  have hL := p.L_pos
  have hr : ‖jointResidual (ballSaddle P hAS Δ y0 c) τ v (solverResult P hAS Δ τ ζ failure y0 hy0 c v ω)‖ ≤ ζ :=
    le_of_not_gt hgood
  unfold solverResult at hr ⊢
  rw [projectedResult_jointResidual] at hr
  exact projectedResult_jointCheck _ τ v (by positivity) _ hr

/-- The actual finite-seed residual fails with probability at most failure, uniformly in every v. -/
theorem solver_failure_uniform (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (Δ : ℝ) {τ ζ failure : ℝ} (hτ : 0 < τ) (hτL : τ ≤ p.L) (hζ : 0 < ζ) (hf : 0 < failure)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) (v : DualSpace dy) :
    (solverLaw p Δ τ ζ failure).real {ω | solverBad P hAS Δ τ ζ failure y0 hy0 c v ω} ≤ failure := by
  let F := ballSaddle P hAS Δ y0 c
  let S := feasibleProduct F
  let G := proximalComponents P τ v c
  let d := 2 * publicRadius p Δ + p.diameter
  have hL := p.L_pos
  have hd : 0 ≤ d := by dsimp [d]; have hR := publicRadius_pos p Δ; have hD := p.diameter_nonneg; positivity
  have hT : averageMap G = proximalOperator F τ v := by
    funext z
    rw [average_proximalComponents, proximalOperator_ballSaddle]
  have hres := SVRG.residual_failure_of_strongMonotone S (feasibleProduct_nonempty F)
    (feasibleProduct_closed F) (feasibleProduct_convex F)
    (by positivity : 0 < 4 * p.L) hτ hd hζ hf
    (proximalComponents_averagedSmooth P hAS hτ hτL Δ y0 v c)
    (proximalProduct_diameter P hAS Δ y0 c)
    (proximalComponents_strongMono P hAS hτL Δ y0 v c)
    (proximalAnchor P hAS Δ y0 hy0 c)
  have he : {ω | solverBad P hAS Δ τ ζ failure y0 hy0 c v ω} =
      {ω | ζ < ‖SVRG.fullStepResidual S (feasibleProduct_nonempty F) (feasibleProduct_closed F)
        (feasibleProduct_convex F) (averageMap G) (4 * p.L)
        (SVRG.epochsIterate S (feasibleProduct_nonempty F) (feasibleProduct_closed F) (feasibleProduct_convex F)
          G (proximalAnchor P hAS Δ y0 hy0 c) (4 * p.L) τ (solverEpochCount p Δ τ ζ failure) ω)‖} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    dsimp only [solverBad, solverResult]
    rw [projectedResult_jointResidual, ← hT]
  rw [he]
  exact hres

end NCConcave16991.Accelerated
