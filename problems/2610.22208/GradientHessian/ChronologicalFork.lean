import GradientHessian.OracleBranches
import GradientHessian.OracleSimulation
import GradientHessian.GaussianPosterior
import GradientHessian.ForkColumns

/-! One shared preprocessor followed by isolated fresh-mark branches.
Every query is part of the same unconditioned, measurable oracle procedure. -/

namespace GradientHessian.ChronologicalFork
open Matrix MeasureTheory LowRank OracleComposition ForkColumns ForkTrace
noncomputable section

variable {d p q r : ℕ} {Seed State Fresh O : Type*}
  [MeasurableSpace Seed] [MeasurableSpace State] [MeasurableSpace Fresh] [MeasurableSpace O]

def procedure (pre : Procedure d p Seed State) (post : Procedure d q (State × Fresh) O)
    (r : ℕ) : Procedure d (p + r*q) (Seed × (Fin r → Fresh)) (Fin r → O) :=
  ((pre.comap ⟨Prod.fst, measurable_fst⟩).withSeed).fork r
    (fun i => post.comap ⟨fun t => (t.2, t.1.2 i),
      measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst.snd)⟩)

theorem run_procedure (pre : Procedure d p Seed State) (post : Procedure d q (State × Fresh) O)
    (r : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (seed : Seed × (Fin r → Fresh)) (i : Fin r) :
    (procedure pre post r).run A seed i = (post.run A (pre.run A seed.1, seed.2 i)) := by
  simp only [procedure, Procedure.run_fork, Procedure.run_comap, Procedure.run_withSeed]

theorem procedure_calls (pre : Procedure d p Seed State) (post : Procedure d q (State × Fresh) O)
    (r : ℕ) (oracle : (Fin d → ℝ) → Fin d → ℝ) (seed : Seed × (Fin r → Fresh)) :
    ((procedure pre post r).toProgram seed).calls oracle = p + r*q :=
  Procedure.calls_toProgram _ oracle seed

theorem branchProjector_measurable {d r s : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (branchProjector (r := r) (s := s) P) := by
  apply (measurable_testProjector P).comp
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  unfold flattenedTests SphereColumnNorm.columnMatrix
  fun_prop

/-- The fork's projector is an actual output of the adaptive product policy.
The upper bound follows from the Gaussian posterior theorem without any
independent-branch posterior assumption. -/
theorem procedure_overlap (a b Q r s : ℕ) {Seed : Type*} [MeasurableSpace Seed]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (proc : Procedure (a + Q) Q Seed (Fin r → Fin s → EuclideanSpace ℝ (Fin (a + Q))))
    (P : Matrix (Fin (a + Q)) (Fin (a + Q)) ℝ)
    (hb : b ≤ a) (ha : 0 < a) {v : NNReal} (hv : v ≠ 0) :
    (∫ t : Seed × Matrix (Fin (a+Q)) (Fin (b+Q)) ℝ,
      (branchProjector P (proc.run (t.2*t.2ᵀ) t.1) * leftKernelProjector t.2).trace
      ∂seedLaw.prod (iidMatrixLaw (a+Q) (b+Q) v)) ≤
        2*((a:ℝ)-b)*((Q:ℝ)+(r*s:ℕ))/a := by
  exact GaussianPosterior.arbitrary_rank_posterior_overlap a b Q seedLaw proc.policy hb ha hv
    (fun h => branchProjector P (proc.decode.1 h))
    ((branchProjector_measurable P).comp proc.decode.2)
    (fun h => testProjector_isProjector P (flattenedTests (proc.decode.1 h)))
    (fun h => testProjector_trace_le P (flattenedTests (proc.decode.1 h)))

/-- Full exact finite fork, including the one-product source-matrix simulation.
The seed contains independent data only; the preprocessor's matrix dependence
is computed by its charged oracle calls. -/
theorem source_fork_run (pre : Procedure d p Seed State)
    (post : Procedure d q (State × Fresh) O) (r : ℕ)
    (scale : ℝ) (D W : Matrix (Fin d) (Fin d) ℝ)
    (seed : Seed × (Fin r → Fresh)) (i : Fin r) :
    (OracleSimulation.procedure scale D (procedure pre post r)).run W seed i =
      post.run (MatrixSandwichOracle.transformedMatrix scale D W)
        (pre.run (MatrixSandwichOracle.transformedMatrix scale D W) seed.1, seed.2 i) := by
  rw [OracleSimulation.run_procedure, run_procedure]

end
end GradientHessian.ChronologicalFork
