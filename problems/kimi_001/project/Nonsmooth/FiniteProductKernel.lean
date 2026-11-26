import Nonsmooth.ProductPosteriorAtoms
import Mathlib.Probability.Kernel.Composition.Prod

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {k : ℕ}

theorem finite_product_kernel_measurable (κ : Fin k → Kernel α β) [∀ i, IsMarkovKernel (κ i)] :
    Measurable (fun x : α => Measure.pi (fun i => κ i x)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm isPiSystem_pi
  rintro s ⟨B, hB, rfl⟩
  simp_rw [Measure.pi_pi]
  exact Finset.measurable_prod _ (fun i _ => (κ i).measurable_coe (hB i (mem_univ i)))

/-- Product of finitely many Markov kernels with a common conditioning parameter. -/
def finiteProductKernel (κ : Fin k → Kernel α β) [∀ i, IsMarkovKernel (κ i)] : Kernel α (Fin k → β) where
  toFun x := Measure.pi (fun i => κ i x)
  measurable' := finite_product_kernel_measurable κ

instance finiteProductKernel_markov (κ : Fin k → Kernel α β) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (finiteProductKernel κ) where
  isProbabilityMeasure x := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun i => κ i x)))

theorem finiteProductKernel_rectangle (κ : Fin k → Kernel α β) [∀ i, IsMarkovKernel (κ i)]
    (x : α) (B : Fin k → Set β) :
    finiteProductKernel κ x (Set.univ.pi B) = ∏ i, κ i x (B i) := Measure.pi_pi _ _

theorem finiteProductKernel_coordinate (κ : Fin k → Kernel α β) [∀ i, IsMarkovKernel (κ i)]
    (x : α) (i : Fin k) :
    (finiteProductKernel κ x).map (fun a : Fin k → β => a i) = κ i x := by
  classical
  ext A hA
  rw [Measure.map_apply (measurable_pi_apply i) hA]
  have he : (fun a : Fin k → β => a i) ⁻¹' A =
      Set.univ.pi (fun j => if j = i then A else Set.univ) := by
    ext a
    constructor
    · intro ha j _
      by_cases hj : j = i
      · simpa [hj] using ha
      · simp [hj]
    · intro ha
      simpa using ha i (mem_univ i)
  rw [he, finiteProductKernel_rectangle]
  simp [apply_ite]

theorem finiteProductKernel_independent (κ : Fin k → Kernel α β) [∀ i, IsMarkovKernel (κ i)]
    (x : α) : iIndepFun (fun i (a : Fin k → β) => a i) (finiteProductKernel κ x) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  simp only [finiteProductKernel_coordinate]
  exact Measure.map_id

end
end Nonsmooth
