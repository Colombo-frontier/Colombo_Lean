import FreshGradientMinimax.EstimatorProgram
import FreshGradientMinimax.ProgramResult
import FreshGradientMinimax.UniformMeasure

/-! Independent finite uniform sampling is a zero-query OracleProgram.
Its result law is the uniform mixture of the selected readout marginals. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

theorem finiteMixtureKernel_measure_comp (p : ℕ → ℝ) (L : ℕ → Kernel X Y)
    (k : ℕ) (ν : Measure X) :
    finiteMixtureKernel p L k ∘ₘ ν = ∑ j ∈ Finset.range k, ENNReal.ofReal (p j) • (L j ∘ₘ ν) := by
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  simp only [finiteMixtureKernel_apply, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_finset_sum _ (fun j _ => measurable_const.mul ((L j).measurable_coe hA))]
  apply Finset.sum_congr rfl
  intro j _
  rw [lintegral_const_mul _ ((L j).measurable_coe hA), Measure.bind_apply hA (L j).aemeasurable]

theorem uniformMeasure_congr (ρ τ : ℕ → Measure X) (T : ℕ) (h : ∀ j < T, ρ j = τ j) :
    uniformMeasure ρ T = uniformMeasure τ T := by
  unfold uniformMeasure
  simp only [finiteMixtureKernel_apply, Kernel.const_apply]
  exact Finset.sum_congr rfl (fun j hj => congrArg _ (h j (Finset.mem_range.mp hj)))

namespace OracleProgram
variable {dx dy : ℕ}

def uniformRead {T : ℕ} (hT : 0 < T) (f : ℕ → X → Y) (hf : ∀ j, Measurable (f j)) :
    OracleProgram dx dy X Y where
  Seed := ℕ
  seedLaw := finiteSeedLaw (fun _ => 1 / (T : ℝ)) T
  seedProbability := finiteSeedLaw_probability _ _ (fun _ _ => by positivity) (uniform_weights_sum hT)
  State := X
  machine _ := (pure (dx := dx) (dy := dy) id measurable_id).machine ()
  init _ := id
  init_measurable _ := measurable_id
  read := f
  read_measurable := hf
  calls _ := 0

theorem uniformRead_law {T : ℕ} (hT : 0 < T) (f : ℕ → X → Y) (hf : ∀ j, Measurable (f j))
    (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (uniformRead hT f hf).lawKernel K =
      finiteMixtureKernel (fun _ => 1 / (T : ℝ)) (fun j => taggedKernel (Kernel.deterministic (f j) (hf j)) 0) T := by
  letI := finiteSeedLaw_probability (fun _ => 1 / (T : ℝ)) T (fun _ _ => by positivity) (uniform_weights_sum hT)
  change mixtureKernel (finiteSeedLaw (fun _ => 1 / (T : ℝ)) T) ((uniformRead hT f hf).branchKernel K) = _
  rw [mixtureKernel_finiteSeedLaw]
  congr 1
  funext j
  change taggedKernel ((Kernel.deterministic id measurable_id).map (f j)) 0 = _
  rw [Kernel.deterministic_map _ (hf j)]
  rfl

theorem uniformRead_result {T : ℕ} (hT : 0 < T) (f : ℕ → X → Y) (hf : ∀ j, Measurable (f j))
    (K : Kernel (Joint dx dy) (Joint dx dy)) :
    (uniformRead hT f hf).resultKernel K =
      finiteMixtureKernel (fun _ => 1 / (T : ℝ)) (fun j => Kernel.deterministic (f j) (hf j)) T := by
  rw [resultKernel, uniformRead_law, finiteMixtureKernel_map _ _ _ _ measurable_fst]
  simp_rw [taggedKernel_first]

theorem uniformRead_result_law {T : ℕ} (hT : 0 < T) (f : ℕ → X → Y) (hf : ∀ j, Measurable (f j))
    (K : Kernel (Joint dx dy) (Joint dx dy)) (ν : Measure X) :
    (uniformRead hT f hf).resultKernel K ∘ₘ ν = uniformMeasure (fun j => ν.map (f j)) T := by
  rw [uniformRead_result, finiteMixtureKernel_measure_comp, uniformMeasure, finiteMixtureKernel_apply]
  simp only [Measure.deterministic_comp_eq_map, Kernel.const_apply]

theorem uniformRead_cost {T : ℕ} (hT : 0 < T) (f : ℕ → X → Y) (hf : ∀ j, Measurable (f j))
    (K : Kernel (Joint dx dy) (Joint dx dy)) (x : X) :
    Integrable costValue ((uniformRead hT f hf).lawKernel K x) ∧
    (∫ z, costValue z ∂(uniformRead hT f hf).lawKernel K x) = 0 := by
  rw [uniformRead_law]
  have hi (j : ℕ) (_hj : j < T) := taggedKernel_cost_integrable (Kernel.deterministic (f j) (hf j)) 0 x
  refine ⟨finiteMixtureKernel_integrable _ _ _ _ _ hi, ?_⟩
  unfold costValue
  rw [finiteMixtureKernel_integral _ _ _ _ _ (fun _ _ => by positivity) hi]
  simp only [taggedKernel_mean_cost, Nat.cast_zero, smul_zero, Finset.sum_const_zero]

end OracleProgram
end FreshGradientMinimax
