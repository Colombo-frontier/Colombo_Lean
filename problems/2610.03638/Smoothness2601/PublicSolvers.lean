import Smoothness2601.PublicOracle
import Smoothness2601.PublicProjected
import Smoothness2601.HypergradientSource

/-! Concrete public programs for all source inner/difference/adjoint and
hypergradient operations. Definitions depend only on public budgets, tuning
parameters and inputs. Semantic theorems quantify Population/Oracle afterwards. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful Bilevel.PrimitiveGeometry
namespace Smoothness2601.PublicSolvers
open FixedProgram AdjointGeometry

variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

def difference (k : ℕ) (h B : ℝ) : Program (Adaptive.Query X Y) (Joint X Y) (X × Y × Y) (Joint X Y) :=
  PublicBatches.sequentialRun PublicOracle.fullCall PublicOracle.fallback
    (DifferencingOracle.query k h) (DifferencingOracle.query_measurable k h)
    (DifferencingOracle.nodeWeight k h) (DifferencingOracle.nodeBatch k h B) (2*k+2)

def differenceY (k : ℕ) (h B : ℝ) : Program (Adaptive.Query X Y) (Joint X Y) (X × Y × Y) Y :=
  (difference k h B).map (fullSnd (X := X) (Y := Y)) (fullSnd (X := X) (Y := Y)).continuous.measurable

def differenceX (k : ℕ) (h B : ℝ) : Program (Adaptive.Query X Y) (Joint X Y) (X × Y × Y) X :=
  (difference k h B).map (fullFst (X := X) (Y := Y)) (fullFst (X := X) (Y := Y)).continuous.measurable

def inner (b : Budgets) (D u : ℝ) : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) Y :=
  PublicBatches.innerIterate (PublicOracle.blockY true) PublicOracle.fallback
    (fun z => (z.1.1,z.2)) (by fun_prop) Prod.snd measurable_snd
    (InnerGeometry.stepsize b)
    (InnerSolve.batchCount (InnerGeometry.stepsize b) b.σ (InnerGeometry.rate b) D u)
    (InnerSolve.count (InnerGeometry.rate b) D u)

def adjointStep (b : Budgets) (k : ℕ) (h : ℝ) (N : ℕ) :
    Program (Adaptive.Query X Y) (Joint X Y) ((X × Y) × Y) Y :=
  (PublicProjected.projectedStep (PublicOracle.blockY false) PublicOracle.fallback
    (differenceY k h N) (fun p => (p.1,p.2.1)) (by fun_prop)
    (fun p => p.2.2) (by fun_prop) (ballRadius b) N (stepsize b)).reparam
      (AdjointSolve.clippedInput b) (AdjointSolve.clippedInput_measurable b)

def adjoint (b : Budgets) (k : ℕ) (h u : ℝ) : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) Y :=
  PublicProjected.run PublicOracle.fallback
    (fun j => adjointStep b k h (AdjointSolve.batch b ((2*k+1:ℕ)/h) u j))
    (AdjointSolve.iterations b u)

def direction (b : Budgets) (k : ℕ) (h : ℝ) (N : ℕ) :
    Program (Adaptive.Query X Y) (Joint X Y) ((X × Y) × Y) X :=
  (PublicProjected.rawStep (PublicOracle.blockX false) PublicOracle.fallback
    (differenceX k h N) (fun p => (p.1,p.2.1)) (by fun_prop)
    (fun _ => 0) measurable_const N 1).reparam
      (AdjointSolve.clippedInput b) (AdjointSolve.clippedInput_measurable b)

def adjointThenDirection (b : Budgets) (k : ℕ) (h u ε : ℝ) :
    Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X :=
  (adjoint b k h u).bind (direction b k h (HypergradientKernels.outputBatch b ((2*k+1:ℕ)/h) ε))

def hypergradient (b : Budgets) (k : ℕ) (h D uy uv ε : ℝ) :
    Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X :=
  (inner b D uy).bind ((adjointThenDirection b k h uv ε).reparam
    (fun z => (z.1.1,z.2)) (by fun_prop))

def source (b : Budgets) (M Λ β cₐ : ℝ) (r : ℕ) (D ε : ℝ) :
    Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X :=
  hypergradient b (Population.stencilHalfOrder r) (HypergradientSource.differenceRadius b M Λ β cₐ ε r)
    D (HypergradientSource.innerAccuracy b ε) (HypergradientSource.adjointAccuracy b ε) ε

variable {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {H : Type} [MeasurableSpace H] (O : Adaptive.Oracle P H)

theorem difference_interpret (k : ℕ) (h B : ℝ) :
    (difference (X := X) (Y := Y) k h B).interpret O.law = DifferencingOracle.estimator P O k h B :=
  PublicBatches.sequentialRun_interpret _ _ O.law (InnerOracle.fullJoint P O)
    (PublicOracle.fullCall_interpret P O) _ _ _ _ _

theorem differenceY_interpret (k : ℕ) (h B : ℝ) :
    (differenceY (X := X) (Y := Y) k h B).interpret O.law = DifferencingOracle.estimatorY P O k h B := by
  rw [differenceY, Program.interpret_map, difference_interpret P O]
  rfl

theorem differenceX_interpret (k : ℕ) (h B : ℝ) :
    (differenceX (X := X) (Y := Y) k h B).interpret O.law = DifferencingOracle.estimatorX P O k h B := by
  rw [differenceX, Program.interpret_map, difference_interpret P O]
  rfl

theorem inner_interpret (D u : ℝ) :
    (inner (X := X) (Y := Y) b D u).interpret O.law = HypergradientSolve.inner P O D u :=
  PublicBatches.innerIterate_interpret _ _ O.law (InnerOracle.blockY P O true)
    (PublicOracle.blockY_interpret P O true) _ _ _ _ _ _ _

theorem adjointStep_interpret (k : ℕ) (h : ℝ) (N : ℕ) :
    (adjointStep (X := X) (Y := Y) b k h N).interpret O.law = AdjointSolve.step P O k h N := by
  rw [adjointStep, Program.interpret_reparam,
    PublicProjected.projectedStep_interpret _ _ O.law (InnerOracle.blockY P O false)
      (PublicOracle.blockY_interpret P O false), differenceY_interpret P O]
  rfl

theorem adjoint_interpret (k : ℕ) (h u : ℝ) :
    (adjoint (X := X) (Y := Y) b k h u).interpret O.law = AdjointSolve.program P O k h u := by
  rw [adjoint, PublicProjected.run_interpret]
  simp_rw [adjointStep_interpret P O]
  rfl

theorem direction_interpret (k : ℕ) (h : ℝ) (N : ℕ) :
    (direction (X := X) (Y := Y) b k h N).interpret O.law = HypergradientKernels.direction P O k h N := by
  rw [direction, Program.interpret_reparam,
    PublicProjected.rawStep_interpret _ _ O.law (InnerOracle.blockX P O false)
      (PublicOracle.blockX_interpret P O false), differenceX_interpret P O]
  rfl

theorem adjointThenDirection_interpret (k : ℕ) (h u ε : ℝ) :
    (adjointThenDirection (X := X) (Y := Y) b k h u ε).interpret O.law =
      HypergradientSolve.adjointThenDirection P O k h u ε := by
  rw [adjointThenDirection, Program.interpret_bind, adjoint_interpret P O, direction_interpret P O]
  rfl

theorem hypergradient_interpret (k : ℕ) (h D uy uv ε : ℝ) :
    (hypergradient (X := X) (Y := Y) b k h D uy uv ε).interpret O.law =
      HypergradientSolve.program P O k h D uy uv ε := by
  rw [hypergradient, Program.interpret_bind, Program.interpret_reparam,
    inner_interpret P O, adjointThenDirection_interpret P O]
  rfl

/-- One concrete program works before the quantification over population and
oracle. Its execution equals the entire source estimator, with hidden history
and every original-call counter preserved. -/
theorem source_interpret (M Λ β cₐ : ℝ) (r : ℕ) (D ε : ℝ) :
    (source (X := X) (Y := Y) b M Λ β cₐ r D ε).interpret O.law =
      HypergradientSource.program P O M Λ β cₐ r D ε :=
  hypergradient_interpret P O _ _ _ _ _ _

include P O in
/-- The source's public sample count equals the compiler horizon. Both count
claims come from actual execution laws already proved above. -/
theorem source_horizon (M Λ β cₐ : ℝ) (r : ℕ) (D ε : ℝ) (history : H) :
    (source (X := X) (Y := Y) b M Λ β cₐ r D ε).horizon =
      HypergradientSource.samples b M Λ β cₐ r D ε := by
  have hc := HypergradientSource.program_calls P O M Λ β cₐ r D ε
  rw [← source_interpret P O M Λ β cₐ r D ε] at hc
  have hn := (source (X := X) (Y := Y) b M Λ β cₐ r D ε).interpret_calls O.law (0,0) history
  obtain ⟨z,hzn,hzm⟩ := (hn.and (hc (0,0) history)).exists
  exact hzn.symm.trans hzm

/-- The same single public algorithm implements the complete source estimator
for every population and valid adaptive oracle. -/
theorem source_compiled_output (M Λ β cₐ : ℝ) (r : ℕ) (D ε : ℝ)
    (history : H) (input : X × Y) :
    Adaptive.outputKernel (FixedProgram.compile (source (X := X) (Y := Y) b M Λ β cₐ r D ε)) O
      (HypergradientSource.samples b M Λ β cₐ r D ε) history input =
      ((HypergradientSource.program P O M Λ β cₐ r D ε).law (input,history)).map Prod.fst := by
  rw [← source_horizon P O M Λ β cₐ r D ε history, FixedProgram.compile_output,
    source_interpret P O]

end Smoothness2601.PublicSolvers
