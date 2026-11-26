import Smoothness2601.BoundaryOuter
import Smoothness2601.PublicOuter

/-! A public finite-program implementation of the boundary upper routine.
The population and oracle appear only in semantic verification. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful Bilevel.PrimitiveGeometry
namespace Smoothness2601.PublicBoundary
open FixedProgram

variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

def inner (b : Budgets) (ε : ℝ) : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) Y :=
  (PublicBatches.affineBatch (PublicOracle.blockY true) PublicOracle.fallback
    (BoundarySolve.innerCount b ε) (InnerGeometry.stepsize b)).reparam
      (fun p => (p,p.2)) (measurable_id.prodMk measurable_snd)

def upper (b : Budgets) (ε : ℝ) : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X :=
  (PublicBatches.affineBatch (PublicOracle.blockX false) PublicOracle.fallback
    (BoundarySolve.upperCount b ε) (-1)).reparam (fun p => (p,0)) (measurable_id.prodMk measurable_const)

def program (b : Budgets) (ε : ℝ) : Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X :=
  (inner b ε).bind ((upper b ε).reparam (fun z => (z.1.1,z.2))
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

def algorithm (b : Budgets) {ε : ℝ} (hε : 0 < ε) : Adaptive.Algorithm X Y :=
  letI : NeZero (OuterSchedule.iterations b ε) := ⟨(OuterSchedule.iterations_pos b hε).ne'⟩
  PublicOuter.algorithm (program b ε) (OuterSchedule.stepsize b ε) (OuterSchedule.iterations b ε)

variable {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {H : Type} [MeasurableSpace H] (O : Adaptive.Oracle P H)

theorem inner_interpret (ε : ℝ) : (inner (X := X) (Y := Y) b ε).interpret O.law =
    BoundarySolve.inner P O ε := by
  rw [inner,Program.interpret_reparam,
    PublicBatches.affineBatch_interpret _ _ O.law (InnerOracle.blockY P O true)
      (PublicOracle.blockY_interpret P O true)]
  rfl

theorem upper_interpret (ε : ℝ) : (upper (X := X) (Y := Y) b ε).interpret O.law =
    BoundarySolve.upper P O ε := by
  rw [upper,Program.interpret_reparam,
    PublicBatches.affineBatch_interpret _ _ O.law (InnerOracle.blockX P O false)
      (PublicOracle.blockX_interpret P O false)]
  rfl

theorem program_interpret (ε : ℝ) : (program (X := X) (Y := Y) b ε).interpret O.law =
    BoundarySolve.program P O ε := by
  rw [program,Program.interpret_bind,Program.interpret_reparam,inner_interpret,upper_interpret]
  rfl

theorem algorithm_output {ε : ℝ} (hε : 0 < ε) (input : X × Y) (history : H) :
    Adaptive.outputKernel (algorithm (X := X) (Y := Y) b hε) O
      (BoundaryCost.count b ε) history input =
      (BoundaryOuter.outputLaw P O hε input history).map NormalizedExecution.selected := by
  letI : NeZero (OuterSchedule.iterations b ε) := ⟨(OuterSchedule.iterations_pos b hε).ne'⟩
  let S := program (X := X) (Y := Y) b ε
  let η := OuterSchedule.stepsize b ε
  let n := OuterSchedule.iterations b ε
  have he : (PublicOuter.path S η n).interpret O.law = BoundaryOuter.path P O ε := by
    rw [PublicOuter.path_interpret,program_interpret]
    rfl
  have hc := BoundaryOuter.path_calls P O ε
  rw [← he] at hc
  have hn := (PublicOuter.path S η n).interpret_calls O.law input history
  obtain ⟨z,hzn,hzc⟩ := (hn.and (hc input history)).exists
  have hcount : (PublicOuter.selectedProgram S η n).horizon = BoundaryCost.count b ε := hzn.symm.trans hzc
  have hout := PublicOuter.algorithm_output (A := S) O η n input history
  rw [hcount,program_interpret] at hout
  exact hout

end Smoothness2601.PublicBoundary
