import Smoothness2601.IndependentExecution
import Smoothness2601.FiniteCoins

/-! The pathwise real-state lower-bound process is exactly the unrestricted
adaptive execution, with arbitrary private random initial memory. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior PrimitiveGeometry IndependentDraws
open scoped ENNReal
namespace Smoothness2601.PrefixSimulator

variable {d T : ℕ} {b : Budgets}
  (A : Adaptive.Algorithm (Space d) ℝ)
  (reply : Frame d T → Adaptive.Query (Space d) ℝ → Bool → Joint (Space d) ℝ)
  (U : Frame d T)
  (hr : Measurable (fun z : Adaptive.Query (Space d) ℝ × Bool => reply U z.1 z.2))
  {P : Population (X := Space d) (Y := ℝ) b} (O : Adaptive.Oracle P Unit)
  (ν : Measure Bool) [IsProbabilityMeasure ν]
  (hlaw : ∀ q, O.law (q,()) = ν.map (fun coin => (reply U q coin,())))

include hr hlaw in
theorem realState_execution_law (N : ℕ) (initial : A.Memory) :
    Adaptive.execution A O N (initial,()) = (law ν N).map
      (fun z => (realState A reply (coinSequence N z) initial U N,())) := by
  rw [IndependentExecution.execution_law A (reply U) hr O ν hlaw]
  congr 1
  funext z
  rw [realState_eq_independent_run]
  rfl

include hr hlaw in
theorem realState_output_law (N : ℕ) (input : Space d × ℝ) :
    Adaptive.outputKernel A O N () input = ((A.initialLaw input).prod (law ν N)).map
      (fun z => A.output (realState A reply (coinSequence N z.2) z.1 U N)) := by
  rw [IndependentExecution.output_law A (reply U) hr O ν hlaw]
  congr 1
  funext z
  rw [realState_eq_independent_run]
  rfl

include hr hlaw in
theorem realState_lintegral_output (N : ℕ) (input : Space d × ℝ)
    (risk : Space d → ℝ≥0∞) (hm : Measurable risk) :
    (∫⁻ x, risk x ∂Adaptive.outputKernel A O N () input) =
      ∫⁻ z, risk (A.output (realState A reply (coinSequence N z.2) z.1 U N))
        ∂(A.initialLaw input).prod (law ν N) := by
  rw [realState_output_law A reply U hr O ν hlaw]
  apply MeasureTheory.lintegral_map hm
  have hh := A.output_measurable.comp (IndependentExecution.memoryRun_joint_measurable A (reply U) hr N)
  convert hh using 1
  funext z
  rw [realState_eq_independent_run]
  rfl

end Smoothness2601.PrefixSimulator
