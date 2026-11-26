import SecondOrder.KernelContinuation

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

universe u
namespace SecondOrder
noncomputable section
variable {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]

theorem compProd_restrict_history (μ : Measure S) [SFinite μ]
    (K : Kernel S A) [IsSFiniteKernel K] {s : Set S} (hs : MeasurableSet s) :
    (μ ⊗ₘ K).restrict (Prod.fst ⁻¹' s) = μ.restrict s ⊗ₘ K := by
  ext E hE
  rw [Measure.restrict_apply hE,Measure.compProd_apply (hE.inter (measurable_fst hs)),
    Measure.compProd_apply hE,←lintegral_indicator hs]
  apply lintegral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    congr 1
    ext a
    simp [hx]
  · rw [Set.indicator_of_not_mem hx]
    have he : Prod.mk x ⁻¹' (E ∩ Prod.fst ⁻¹' s) = ∅ := by ext a; simp [hx]
    rw [he,measure_empty]

/-- Histories satisfying every safety test up to and including the current
query/output. A test can describe nonactivation or remaining below a cap. -/
def kernelSurvivalSet (safe : ∀ n, Set (FiniteHistory S A n)) :
    (n : ℕ) → Set (FiniteHistory S A n)
  | 0 => safe 0
  | n+1 => safe (n+1) ∩ Prod.fst ⁻¹' kernelSurvivalSet safe n

theorem kernelSurvivalSet_measurable (safe : ∀ n, Set (FiniteHistory S A n))
    (hs : ∀ n, MeasurableSet (safe n)) : ∀ n, MeasurableSet (kernelSurvivalSet safe n) := by
  intro n
  induction n with
  | zero => exact hs 0
  | succ n ih => exact (hs (n+1)).inter (measurable_fst ih)

theorem kernelSurvivalSet_subset (safe : ∀ n, Set (FiniteHistory S A n)) (n : ℕ) :
    kernelSurvivalSet safe n ⊆ safe n := by
  cases n with
  | zero => exact Set.Subset.rfl
  | succ n => exact Set.inter_subset_left

/-- Two actual interactions have identical laws on all surviving histories
if their response kernels agree until the first failed safety test. -/
theorem adaptiveKernelLaw_survival_eq (μ : Measure S) [IsProbabilityMeasure μ]
    (K Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n))
    (heq : ∀ n h, h ∈ safe n → K n h=Q n h) :
    ∀ n, (adaptiveKernelLaw μ K n).restrict (kernelSurvivalSet safe n) =
      (adaptiveKernelLaw μ Q n).restrict (kernelSurvivalSet safe n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (adaptiveKernelLaw μ K n ⊗ₘ K n).restrict
      (safe (n+1) ∩ Prod.fst ⁻¹' kernelSurvivalSet safe n) =
      (adaptiveKernelLaw μ Q n ⊗ₘ Q n).restrict
      (safe (n+1) ∩ Prod.fst ⁻¹' kernelSurvivalSet safe n)
    rw [←Measure.restrict_restrict (hs (n+1)),←Measure.restrict_restrict (hs (n+1)),
      compProd_restrict_history _ _ (kernelSurvivalSet_measurable safe hs n),
      compProd_restrict_history _ _ (kernelSurvivalSet_measurable safe hs n),ih]
    congr 1
    apply Measure.compProd_congr
    filter_upwards [ae_restrict_mem (kernelSurvivalSet_measurable safe hs n)] with h hh
    exact heq n h (kernelSurvivalSet_subset safe n hh)

theorem adaptiveKernelLaw_survival_probability_eq (μ : Measure S) [IsProbabilityMeasure μ]
    (K Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n))
    (heq : ∀ n h, h ∈ safe n → K n h=Q n h) (n : ℕ) :
    adaptiveKernelLaw μ K n (kernelSurvivalSet safe n) =
      adaptiveKernelLaw μ Q n (kernelSurvivalSet safe n) := by
  have hh := congrArg (fun η : Measure (FiniteHistory S A n) => η Set.univ)
    (adaptiveKernelLaw_survival_eq μ K Q safe hs heq n)
  simpa only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] using hh

/-- Safety is inspected only at earlier response times. In particular an
entry query may fail the current safety test before its reply is sampled. -/
def kernelBeforeSet (safe : ∀ n, Set (FiniteHistory S A n)) :
    (n : ℕ) → Set (FiniteHistory S A n)
  | 0 => Set.univ
  | n+1 => Prod.fst ⁻¹' kernelSurvivalSet safe n

theorem kernelBeforeSet_measurable (safe : ∀ n, Set (FiniteHistory S A n))
    (hs : ∀ n, MeasurableSet (safe n)) : ∀ n, MeasurableSet (kernelBeforeSet safe n) := by
  intro n
  cases n with
  | zero => exact MeasurableSet.univ
  | succ n => exact measurable_fst (kernelSurvivalSet_measurable safe hs n)

theorem kernelSurvivalSet_eq_inter_before (safe : ∀ n, Set (FiniteHistory S A n)) (n : ℕ) :
    kernelSurvivalSet safe n = safe n ∩ kernelBeforeSet safe n := by
  cases n with
  | zero => exact (Set.inter_univ _).symm
  | succ n => rfl

theorem adaptiveKernelLaw_before_eq (μ : Measure S) [IsProbabilityMeasure μ]
    (K Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n))
    (heq : ∀ n h, h ∈ safe n → K n h=Q n h) (n : ℕ) :
    (adaptiveKernelLaw μ K n).restrict (kernelBeforeSet safe n) =
      (adaptiveKernelLaw μ Q n).restrict (kernelBeforeSet safe n) := by
  cases n with
  | zero => rfl
  | succ n =>
    change (adaptiveKernelLaw μ K n ⊗ₘ K n).restrict (Prod.fst ⁻¹' kernelSurvivalSet safe n) =
      (adaptiveKernelLaw μ Q n ⊗ₘ Q n).restrict (Prod.fst ⁻¹' kernelSurvivalSet safe n)
    rw [compProd_restrict_history _ _ (kernelSurvivalSet_measurable safe hs n),
      compProd_restrict_history _ _ (kernelSurvivalSet_measurable safe hs n),
      adaptiveKernelLaw_survival_eq μ K Q safe hs heq n]
    apply Measure.compProd_congr
    filter_upwards [ae_restrict_mem (kernelSurvivalSet_measurable safe hs n)] with h hh
    exact heq n h (kernelSurvivalSet_subset safe n hh)

/-- First-failure probabilities also coincide. This is the law-level
coupling argument and does not require a common response sampler. -/
theorem adaptiveKernelLaw_exit_probability_eq (μ : Measure S) [IsProbabilityMeasure μ]
    (K Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (safe : ∀ n, Set (FiniteHistory S A n)) (hs : ∀ n, MeasurableSet (safe n))
    (heq : ∀ n h, h ∈ safe n → K n h=Q n h) (n : ℕ) :
    adaptiveKernelLaw μ K n (kernelSurvivalSet safe n)ᶜ =
      adaptiveKernelLaw μ Q n (kernelSurvivalSet safe n)ᶜ := by
  rw [measure_compl (kernelSurvivalSet_measurable safe hs n) (measure_ne_top _ _),
    measure_compl (kernelSurvivalSet_measurable safe hs n) (measure_ne_top _ _),
    adaptiveKernelLaw_survival_probability_eq μ K Q safe hs heq n,measure_univ,measure_univ]

end
end SecondOrder
