import Smoothness2601.BoundaryCost
import Smoothness2601.NormalizedOutput

/-! Actual boundary normalized trajectory, with exact fixed calls and an
integrable expected stationarity bound under the original oracle model. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.Stateful
namespace Smoothness2601.BoundaryOuter
open OuterSchedule HypergradientGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {H : Type} [MeasurableSpace H] (O : Adaptive.Oracle P H)

def path (ε : ℝ) : Procedure (X × Y) H (NormalizedExecution.Path X (iterations b ε)) :=
  NormalizedExecution.run (BoundarySolve.program P O ε) (stepsize b ε) (iterations b ε)

theorem path_calls (ε : ℝ) : (path P O ε).CallsEq (fun _ => BoundaryCost.count b ε) :=
  NormalizedExecution.run_calls _ _ (BoundarySolve.program_calls P O ε) _ _

def outputLaw {ε : ℝ} (hε : 0 < ε) (p : X × Y) (history : H) :
    Measure (Fin (iterations b ε) × Outcome (NormalizedExecution.Path X (iterations b ε)) H) :=
  letI : NeZero (iterations b ε) := ⟨(iterations_pos b hε).ne'⟩
  NormalizedExecution.outputLaw (BoundarySolve.program P O ε) (stepsize b ε) (iterations b ε) p history

instance outputLaw_probability {ε : ℝ} (hε : 0 < ε) (p : X × Y) (history : H) :
    IsProbabilityMeasure (outputLaw P O hε p history) := by unfold outputLaw; infer_instance

variable [FiniteDimensional ℝ Y]

theorem expected_stationarity (heq : b.L₁ = b.μ) {ε : ℝ} (hε : 0 < ε)
    (p : X × Y) (history : H) (hinit : P.Initialized p.1 p.2) :
    Integrable (fun z => ‖gradient P.objective (NormalizedExecution.selected z)‖)
      (outputLaw P O hε p history) ∧
    (∫ z, ‖gradient P.objective (NormalizedExecution.selected z)‖
      ∂outputLaw P O hε p history) ≤ 3*ε/4 := by
  letI : NeZero (iterations b ε) := ⟨(iterations_pos b hε).ne'⟩
  have hf (x : X) : HasGradientAt P.objective (gradient P.objective x) x :=
    (P.primitive.hasGradient_hyperobjective P.primitive.canonicalResponse x).differentiableAt.hasGradientAt
  have hfloor (x : X) : sInf (Set.range P.objective) ≤ P.objective x :=
    csInf_le hinit.bounded_below ⟨x,rfl⟩
  have hh := NormalizedExecution.expected_selected_norm (BoundarySolve.program P O ε)
    P.objective (gradient P.objective) (outerSmoothness_pos b).le (stepsize_pos b hε)
    hf (outer_smoothness P) (sInf (Set.range P.objective)) hfloor (iterations b ε)
    (R := travel b ε) le_rfl p history hinit.initial_gap
    (fun x h _ => BoundarySolve.program_error P O heq hε (x,p.2) h)
  exact ⟨hh.1,hh.2.trans (stationarity_budget b hε)⟩

end Smoothness2601.BoundaryOuter
