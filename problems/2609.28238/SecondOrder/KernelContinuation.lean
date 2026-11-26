import SecondOrder.AdaptiveKernelLaw
import Mathlib.Probability.Kernel.Composition.MeasureComp

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

universe u
namespace SecondOrder
noncomputable section
variable {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]

/-- The actual continuation kernel from a complete entry history. The
history prefix is retained, and responses can depend on all earlier replies. -/
def kernelContinuation (K : ∀ n, Kernel (FiniteHistory S A n) A) (n : ℕ) :
    (k : ℕ) → Kernel (FiniteHistory S A n) (FiniteHistory S A (n+k))
  | 0 => Kernel.id
  | k+1 => (Kernel.id ×ₖ K (n+k)) ∘ₖ kernelContinuation K n k

instance kernelContinuation_markov (K : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    ∀ k, IsMarkovKernel (kernelContinuation K n k)
  | 0 => inferInstanceAs (IsMarkovKernel (Kernel.id))
  | k+1 => by
    letI := kernelContinuation_markov K n k
    exact inferInstanceAs (IsMarkovKernel ((Kernel.id ×ₖ K (n+k)) ∘ₖ kernelContinuation K n k))

/-- Cutting an adaptive law at any deterministic time gives the mixture of
the same continuation kernels over its actual entry-history law. -/
theorem adaptiveKernelLaw_cut (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    ∀ k, adaptiveKernelLaw μ K (n+k) = kernelContinuation K n k ∘ₘ adaptiveKernelLaw μ K n := by
  intro k
  induction k with
  | zero => exact Measure.id_comp.symm
  | succ k ih =>
    change adaptiveKernelLaw μ K (n+k) ⊗ₘ K (n+k) = _
    rw [Measure.compProd_eq_comp_prod,ih,Measure.comp_assoc]
    rfl

theorem adaptiveKernelLaw_cut_event (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (n k : ℕ) {E : Set (FiniteHistory S A (n+k))} (hE : MeasurableSet E) :
    adaptiveKernelLaw μ K (n+k) E =
      ∫⁻ h, kernelContinuation K n k h E ∂adaptiveKernelLaw μ K n := by
  rw [adaptiveKernelLaw_cut μ K n k,Measure.bind_apply hE (kernelContinuation K n k).aemeasurable]

/-- An unnormalised entry law can have zero mass. Pointwise continuation
bounds integrate with its actual entry mass, without conditioning on survival. -/
theorem kernelContinuation_entry_bound (K : ∀ n, Kernel (FiniteHistory S A n) A)
    (n k : ℕ) (η : Measure (FiniteHistory S A n))
    {E : Set (FiniteHistory S A (n+k))} (hE : MeasurableSet E) {q : ℝ≥0∞}
    (hq : ∀ᵐ h ∂η, kernelContinuation K n k h E ≤ q) :
    (kernelContinuation K n k ∘ₘ η) E ≤ q * η Set.univ := by
  rw [Measure.bind_apply hE (kernelContinuation K n k).aemeasurable]
  exact (lintegral_mono_ae hq).trans_eq (lintegral_const q)

end
end SecondOrder
