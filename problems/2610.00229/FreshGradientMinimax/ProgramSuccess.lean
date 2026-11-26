import FreshGradientMinimax.ProgramCap
import FreshGradientMinimax.Probability

/-! Moment bounds for a genuine program imply success of its compiled
fixed-budget algorithm, using the exact capped output distribution. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace OracleProgram
variable {dx dy : ℕ} {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

theorem budgetMethod_success (P : OracleProgram dx dy X Y) (f : Y → Euclid dx) (hf : Measurable f)
    (x : X) (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (g : Euclid dx → Euclid dx) (hg : Measurable g) {N : ℕ} {B ε : ℝ}
    (hB : 0 < B) (hε : 0 < ε) (hN : 12 * B ≤ (N : ℝ))
    (hc : Integrable costValue (P.originalKernel K x))
    (hcm : (∫ p, costValue p ∂P.originalKernel K x) ≤ B)
    (he : Integrable (fun p : Y × ℕ => ‖g (f p.1)‖ ^ 2) (P.originalKernel K x))
    (hem : (∫ p, ‖g (f p.1)‖ ^ 2 ∂P.originalKernel K x) ≤ ε ^ 2 / 12) :
    5 / 6 ≤ ((P.budgetMethod f hf x).outputLaw K N).real {u | ‖g u‖ ≤ ε} := by
  letI : IsProbabilityMeasure (P.originalKernel K x) := by rw [originalKernel_eq_law]; infer_instance
  have hb : MeasurableSet {p : Y × ℕ | ε < ‖g (cappedRead f N p)‖} :=
    measurableSet_lt measurable_const (hg.comp (cappedRead_measurable hf N)).norm
  have hs := fixed_budget_success (ν := P.originalKernel K x) Prod.snd
    (fun p : Y × ℕ => f p.1) (cappedRead f N) g hB hε hN hc hcm he hem
    (fun p hp => if_pos hp) hb
  rw [budgetMethod_outputLaw, Measure.real,
    Measure.map_apply (cappedRead_measurable hf N) (measurableSet_le hg.norm measurable_const)]
  exact hs

end OracleProgram
end FreshGradientMinimax
