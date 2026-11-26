import FreshGradientMinimax.ParameterRead
import FreshGradientMinimax.CostedTransport

/-! Carry an arbitrary measurable input parameter through a program,
retaining its correlation with the input and with all later outputs. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleProgram
variable {dx dy : ℕ} {X Y Θ : Type}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Θ]

def carryParameter (P : OracleProgram dx dy X Y) : OracleProgram dx dy (Θ × X) (Θ × Y) :=
  P.parameterRead (fun i s => (s.1, P.read i s.2))
    (fun i => measurable_fst.prodMk ((P.read_measurable i).comp measurable_snd))

theorem carryParameter_fiber (P : OracleProgram dx dy X Y)
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (θ : Θ) :
    ((P.carryParameter (Θ := Θ)).lawKernel K).comap (fun x => (θ, x)) measurable_prodMk_left =
      (P.lawKernel K).map (costedMap (fun y => (θ, y))) := by
  rw [carryParameter, parameterRead_law]
  change (P.map (fun y => (θ, y)) measurable_prodMk_left).lawKernel K = _
  exact P.map_law _ _ K

end OracleProgram
end FreshGradientMinimax
