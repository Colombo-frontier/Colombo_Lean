import SecondOrder.KernelFirstEntry

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

universe u
namespace SecondOrder
noncomputable section
variable {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]

/-- A union bound across actual history marginals of an adaptive process.
The last test need not be followed by a response. -/
theorem adaptiveKernelLaw_exit_le_sum (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n)) (N : ℕ) :
    (adaptiveKernelLaw μ K N).real (kernelSurvivalSet safe N)ᶜ ≤
      ∑ n ∈ Finset.range (N+1), (adaptiveKernelLaw μ K n).real (safe n)ᶜ := by
  have ht := adaptiveKernelLaw_firstExit_total μ K safe hs N
  have he : (adaptiveKernelLaw μ K N).real (kernelSurvivalSet safe N)ᶜ =
      ∑ n ∈ Finset.range (N+1), (adaptiveKernelLaw μ K n).real (kernelFirstExitSet safe n) := by
    rw [measureReal_compl (kernelSurvivalSet_measurable safe hs N)]
    have hu : (adaptiveKernelLaw μ K N).real Set.univ=1 := by
      simp only [measureReal_def,measure_univ,ENNReal.toReal_one]
    rw [hu]
    linarith
  rw [he]
  apply Finset.sum_le_sum
  intro n hn
  exact measureReal_mono Set.inter_subset_right

theorem adaptiveKernelLaw_exit_uniform (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n))
    (N : ℕ) {b : ℝ} (hb : ∀ n, n≤N → (adaptiveKernelLaw μ K n).real (safe n)ᶜ≤b) :
    (adaptiveKernelLaw μ K N).real (kernelSurvivalSet safe N)ᶜ≤(N+1:ℕ)*b := by
  apply (adaptiveKernelLaw_exit_le_sum μ K safe hs N).trans
  calc
    _ ≤ ∑ _n ∈ Finset.range (N+1), b := Finset.sum_le_sum (fun n hn => hb n (by have := Finset.mem_range.mp hn; omega))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

end
end SecondOrder
