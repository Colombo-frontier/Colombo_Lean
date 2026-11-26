import NCConcave16991.AcceleratedSVRGSolver
import NCConcave16991.AcceleratedRandom

/-!
# A genuine randomized inexact proximal solver for the original value function

Every accelerated stage uses a fresh independent finite SVRG seed. Its
extrapolated dual center is chosen from the preceding seeds. The actual
unrestricted primal objective certificate fails only if one computed residual
test fails, with probability bounded by the chronological union estimate.
-/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.Accelerated

variable (p : ProblemParameters) [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

def proxTolerance (Δ τ δ : ℝ) : ℝ :=
  tolerance τ p.diameter δ (2 * publicRadius p Δ + p.diameter)

abbrev ProxSeed (Δ τ δ failure : ℝ) :=
  FiniteProcess.History (SolverSeed p Δ τ (proxTolerance p Δ τ δ) failure)
    (horizon τ p.diameter δ)

def proxLaw (Δ τ δ failure : ℝ) : Measure (ProxSeed p Δ τ δ failure) :=
  FiniteProcess.law (solverLaw p Δ τ (proxTolerance p Δ τ δ) failure) (horizon τ p.diameter δ)

instance proxLaw_probability (Δ τ δ failure : ℝ) : IsProbabilityMeasure (proxLaw p Δ τ δ failure) := by
  exact FiniteProcess.law_probability _ _

def solverFallback (Δ τ ζ failure : ℝ) : SolverSeed p Δ τ ζ failure :=
  Classical.choice (nonempty_of_isProbabilityMeasure (solverLaw p Δ τ ζ failure))

variable {p} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

def proxSample (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ τ δ failure : ℝ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) :
    ℕ → DualSpace dy → SolverSeed p Δ τ (proxTolerance p Δ τ δ) failure →
      ProxResult (X := PrimalSpace dx) (Y := DualSpace dy) :=
  fun _ v ω ↦ solverResult P hAS Δ τ (proxTolerance p Δ τ δ) failure y0 hy0 c v ω

/-- The literal finite-history primal output of independent accelerated solves. -/
def stochasticProxOutput (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ τ δ failure : ℝ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx)
    (h : ProxSeed p Δ τ δ failure) : PrimalSpace dx :=
  randomOutput τ (solverFallback p Δ τ (proxTolerance p Δ τ δ) failure)
    (proxSample P hAS Δ τ δ failure y0 hy0 c) y0 (horizon τ p.diameter δ) h

/-- The actual finite sequence of observable residual tests; its failure bound
does not require the current center to satisfy an objective-gap estimate. -/
def stochasticProxBad (P : Problem p dx dy K) (hAS : P.averagedSmooth) (Δ τ δ failure : ℝ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx)
    (h : ProxSeed p Δ τ δ failure) : Prop :=
  ¬∀ k < horizon τ p.diameter δ,
    JointCheck (ballSaddle P hAS Δ y0 c) τ (proxTolerance p Δ τ δ)
      (center τ k (states τ (replay (solverFallback p Δ τ (proxTolerance p Δ τ δ) failure)
        (proxSample P hAS Δ τ δ failure y0 hy0 c) (horizon τ p.diameter δ) h) y0 k))
      (resultAt τ (replay (solverFallback p Δ τ (proxTolerance p Δ τ δ) failure)
        (proxSample P hAS Δ τ δ failure y0 hy0 c) (horizon τ p.diameter δ) h) y0 k)

theorem proxTolerance_pos (p : ProblemParameters) {Δ τ δ : ℝ} (hδ : 0 < δ) :
    0 < proxTolerance p Δ τ δ := by
  apply tolerance_pos hδ
  have hR := publicRadius_pos p Δ
  have hD := p.diameter_nonneg
  positivity

/-- The actual solver supplies the complete normal/feasibility check; only its
explicitly computed residual norm can fail. -/
theorem proxSample_check_failure (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (Δ : ℝ) {τ δ failure : ℝ} (hτ : 0 < τ) (hτL : τ ≤ p.L) (hδ : 0 < δ)
    (hf : 0 < failure) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (c : PrimalSpace dx) (k : ℕ) (v : DualSpace dy) :
    (solverLaw p Δ τ (proxTolerance p Δ τ δ) failure).real
      {ω | ¬JointCheck (ballSaddle P hAS Δ y0 c) τ (proxTolerance p Δ τ δ) v
        (proxSample P hAS Δ τ δ failure y0 hy0 c k v ω)} ≤ failure := by
  have he : {ω | ¬JointCheck (ballSaddle P hAS Δ y0 c) τ (proxTolerance p Δ τ δ) v
        (proxSample P hAS Δ τ δ failure y0 hy0 c k v ω)} =
      {ω | solverBad P hAS Δ τ (proxTolerance p Δ τ δ) failure y0 hy0 c v ω} := by
    ext ω
    constructor
    · intro hn
      by_contra hb
      exact hn (solverResult_jointCheck P hAS Δ τ (proxTolerance p Δ τ δ) failure y0 hy0 c v ω hb)
    · intro hb hc
      exact not_lt_of_ge hc.2.2.2.2 hb
  rw [he]
  exact solver_failure_uniform P hAS Δ hτ hτL (proxTolerance_pos p hδ) hf y0 hy0 c v

/-- All adaptive residual checks hold except on an event of probability at
most K*failure under the actual nested independent seed law. -/
theorem stochasticProx_checks_failure (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (Δ : ℝ) {τ δ failure : ℝ} (hτ : 0 < τ) (hτL : τ ≤ p.L) (hδ : 0 < δ)
    (hf : 0 < failure) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (c : PrimalSpace dx) :
    (proxLaw p Δ τ δ failure).real {h | ¬∀ k < horizon τ p.diameter δ,
      JointCheck (ballSaddle P hAS Δ y0 c) τ (proxTolerance p Δ τ δ)
        (center τ k (states τ (replay (solverFallback p Δ τ (proxTolerance p Δ τ δ) failure)
          (proxSample P hAS Δ τ δ failure y0 hy0 c) (horizon τ p.diameter δ) h) y0 k))
        (resultAt τ (replay (solverFallback p Δ τ (proxTolerance p Δ τ δ) failure)
          (proxSample P hAS Δ τ δ failure y0 hy0 c) (horizon τ p.diameter δ) h) y0 k)} ≤
      (horizon τ p.diameter δ : ℝ) * failure :=
  random_checks_failure_probability (ballSaddle P hAS Δ y0 c) τ (proxTolerance p Δ τ δ)
    (solverFallback p Δ τ (proxTolerance p Δ τ δ) failure)
    (proxSample P hAS Δ τ δ failure y0 hy0 c) y0
    (solverLaw p Δ τ (proxTolerance p Δ τ δ) failure) hf.le
    (proxSample_check_failure P hAS Δ hτ hτL hδ hf y0 hy0 c) (horizon τ p.diameter δ)

theorem stochasticProxBad_probability (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (Δ : ℝ) {τ δ failure : ℝ} (hτ : 0 < τ) (hτL : τ ≤ p.L) (hδ : 0 < δ)
    (hf : 0 < failure) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) :
    (proxLaw p Δ τ δ failure).real {h | stochasticProxBad P hAS Δ τ δ failure y0 hy0 c h} ≤
      (horizon τ p.diameter δ : ℝ) * failure :=
  stochasticProx_checks_failure P hAS Δ hτ hτL hδ hf y0 hy0 c

/-- The checked actual output has the literal unrestricted primal objective
certificate used by the outer proximal loop. -/
theorem stochasticProxOutput_certificate (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {Δ τ δ failure : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx)
    (hgap : primalObjective K P.component c - sInf (range (primalObjective K P.component)) ≤ Δ)
    (h : ProxSeed p Δ τ δ failure)
    (hgood : ¬stochasticProxBad P hAS Δ τ δ failure y0 hy0 c h) :
    primalObjective K P.component (stochasticProxOutput P hAS Δ τ δ failure y0 hy0 c h) +
        p.L * ‖stochasticProxOutput P hAS Δ τ δ failure y0 hy0 c h - c‖ ^ 2 ≤
      primalObjective K P.component (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) +
        p.L * ‖proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c - c‖ ^ 2 + δ :=
  public_inexact_proximal_certificate P hAS hτ hδ y0 hy0 c hgap
    (replay (solverFallback p Δ τ (proxTolerance p Δ τ δ) failure)
      (proxSample P hAS Δ τ δ failure y0 hy0 c) (horizon τ p.diameter δ) h)
    (Classical.not_not.mp hgood)

/-- The complete randomized inexact-proximal certificate is about the original
unrestricted value function and its true proximal minimizer. No stochastic
moment, solver accuracy or residual probability is an assumption. -/
theorem stochasticProx_objective_failure (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {Δ τ δ failure : ℝ} (hτ : 0 < τ) (hτL : τ ≤ p.L) (hδ : 0 < δ)
    (hf : 0 < failure) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (c : PrimalSpace dx)
    (hgap : primalObjective K P.component c - sInf (range (primalObjective K P.component)) ≤ Δ) :
    (proxLaw p Δ τ δ failure).real {h |
      primalObjective K P.component (proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c) +
          p.L * ‖proximalMap p.L_pos (P.primal_continuous hAS) P.value_bddBelow c - c‖ ^ 2 + δ <
        primalObjective K P.component (stochasticProxOutput P hAS Δ τ δ failure y0 hy0 c h) +
          p.L * ‖stochasticProxOutput P hAS Δ τ δ failure y0 hy0 c h - c‖ ^ 2} ≤
      (horizon τ p.diameter δ : ℝ) * failure := by
  have hc := stochasticProx_checks_failure P hAS Δ hτ hτL hδ hf y0 hy0 c
  apply le_trans ?_ hc
  apply measureReal_mono
  · intro h hb hchecks
    have hp := public_inexact_proximal_certificate P hAS hτ hδ y0 hy0 c hgap
      (replay (solverFallback p Δ τ (proxTolerance p Δ τ δ) failure)
        (proxSample P hAS Δ τ δ failure y0 hy0 c) (horizon τ p.diameter δ) h) hchecks
    exact not_lt_of_ge hp hb
  · exact measure_ne_top _ _

end NCConcave16991.Accelerated
