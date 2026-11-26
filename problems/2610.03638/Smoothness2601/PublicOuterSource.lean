import Smoothness2601.PublicOuter
import Smoothness2601.OuterSource

noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful Bilevel.PrimitiveGeometry
namespace Smoothness2601.PublicOuter
open FixedProgram NormalizedExecution
variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {H : Type} [MeasurableSpace H]
  {b : Budgets} {P : Population (X := X) (Y := Y) b} (O : Adaptive.Oracle P H)
def sourceEstimator (b : Budgets) (M Λ β cₐ : ℝ) (r : ℕ) (ε : ℝ) :
    Program (Adaptive.Query X Y) (Joint X Y) (X × Y) X :=
  PublicSolvers.source b M Λ β cₐ r (OuterSchedule.radius b ε) ε

/-- A single actual Adaptive.Algorithm, fixed using only public parameters. -/
def sourceAlgorithm (b : Budgets) (M Λ β cₐ : ℝ) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Adaptive.Algorithm X Y :=
  letI : NeZero (OuterSchedule.iterations b ε) := ⟨(OuterSchedule.iterations_pos b hε).ne'⟩
  algorithm (sourceEstimator b M Λ β cₐ r ε)
    (OuterSchedule.stepsize b ε) (OuterSchedule.iterations b ε)

theorem sourceEstimator_interpret (M Λ β cₐ : ℝ) (r : ℕ) (ε : ℝ) :
    (sourceEstimator (X := X) (Y := Y) b M Λ β cₐ r ε).interpret O.law =
      OuterSource.estimator P O M Λ β cₐ r ε :=
  PublicSolvers.source_interpret P O _ _ _ _ _ _ _

/-- The compiled public algorithm has exactly the output measure used by the
source stationarity proof, at exactly the source fixed original-call count. -/
theorem sourceAlgorithm_output (M Λ β cₐ : ℝ) (r : ℕ) {ε : ℝ} (hε : 0 < ε)
    (input : X × Y) (history : H) :
    Adaptive.outputKernel (sourceAlgorithm (X := X) (Y := Y) b M Λ β cₐ r hε) O
      (OuterSource.callCount b M Λ β cₐ r ε) history input =
      (OuterSource.outputLaw P O M Λ β cₐ r hε input history).map NormalizedExecution.selected := by
  letI : NeZero (OuterSchedule.iterations b ε) := ⟨(OuterSchedule.iterations_pos b hε).ne'⟩
  let S := sourceEstimator (X := X) (Y := Y) b M Λ β cₐ r ε
  let η := OuterSchedule.stepsize b ε
  let n := OuterSchedule.iterations b ε
  have he : (path S η n).interpret O.law = OuterSource.path P O M Λ β cₐ r ε := by
    rw [path_interpret, sourceEstimator_interpret]
    rfl
  have hc := OuterSource.path_calls P O M Λ β cₐ r ε
  rw [← he] at hc
  have hn := (path S η n).interpret_calls O.law input history
  obtain ⟨z,hzn,hzc⟩ := (hn.and (hc input history)).exists
  have hcount : (selectedProgram S η n).horizon = OuterSource.callCount b M Λ β cₐ r ε :=
    hzn.symm.trans hzc
  have hout := algorithm_output (A := S) O η n input history
  rw [hcount, sourceEstimator_interpret] at hout
  exact hout

end Smoothness2601.PublicOuter
