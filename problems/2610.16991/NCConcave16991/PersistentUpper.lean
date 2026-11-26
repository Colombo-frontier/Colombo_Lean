import NCConcave16991.PersistentProgramProcess
import NCConcave16991.OracleProgramGuarantees
import NCConcave16991.UpperAssembly

/-!
# Uniform fixed-budget averaging upper bound

The private law and reply-driven program are chosen before the unknown
component functions. This connects the actual proved persistent trajectory to
the unrestricted randomized oracle model, rather than assuming an algorithm
or a stochastic convergence certificate.
-/

open Set MeasureTheory

namespace NCConcave16991

noncomputable section

def persistentOracleBudget (p : ProblemParameters) : ℕ :=
  persistentChronologicalBudget p.n (persistentPublicEpoch p) (persistentPublicBatch p)
    (persistentPublicInnerSteps p) (persistentPublicOuterSteps p)

theorem persistentOracleBudget_le (p : ProblemParameters) :
    persistentOracleBudget p ≤ persistentPublicBudget p :=
  persistentChronologicalBudget_le _ _ _ _ _ (persistent_public_parameters p).1

theorem persistent_validSquaredExpectationBudget (p : ProblemParameters) :
    ValidSquaredExpectationBudget p (persistentOracleBudget p) := by
  classical
  intro dx dy K x0
  let y0 : DualSpace dy := Classical.choose K.nonempty
  have hy0 : y0 ∈ K.carrier := Classical.choose_spec K.nonempty
  let Q := PersistentProgram.selectedProgram (p := p) (dx := dx) y0 hy0
    (persistentPublicBatch p) (persistentPublicEpoch p) (persistentPublicInnerSteps p)
    (persistentPublicOuterSteps p) x0
  let A := OracleProgram.randomizedPolicy K Q (persistentPublicLaw p)
  refine ⟨A, ?_⟩
  intro P h0 hAS
  apply (OracleProgram.squaredExpectationGuarantee_iff Q (persistentPublicLaw p) P).2
  have he (ω : PersistentPublicSeed p) :
      OracleProgram.eval Q (oracleResponse P) ω = persistentPublicOutput P y0 hy0 ω :=
    PersistentProgram.eval_selectedProgram P y0 hy0 _ _ _ _ x0 h0 ω
  constructor
  · intro ω
    rw [he]
    exact (P.moreau_hasGradientAt hAS (persistentPublicOutput P y0 hy0 ω)).differentiableAt
  · constructor
    · exact Integrable.of_finite
    · simp_rw [he]
      exact persistent_public_original_gradient_mean P hAS y0 hy0

/-- The first upper bound in Theorem 3.2, with a concrete universal constant. -/
theorem persistent_averaging_upper (p : ProblemParameters) :
    ∃ budget : ℕ, ValidSquaredExpectationBudget p budget ∧
      (budget : ℝ) ≤ (2 : ℝ) ^ 88 * ((p.n : ℝ) + (1 + dimensionlessA p) *
        ((p.n : ℝ) ^ (1 / 2 : ℝ) * clippedDiameter (dimensionlessB p) +
          clippedDiameter (dimensionlessB p) ^ 4)) := by
  refine ⟨persistentOracleBudget p, persistent_validSquaredExpectationBudget p, ?_⟩
  exact (Nat.cast_le.mpr (persistentOracleBudget_le p)).trans (persistent_public_rate_bound p)

theorem persistent_averaging_validBudget (p : ProblemParameters) :
    ValidBudget p .averaged (persistentOracleBudget p) :=
  validBudget_of_squaredExpectation (persistent_validSquaredExpectationBudget p)

end

end NCConcave16991
