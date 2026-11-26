import SecondOrder.KernelStageExperiment
import SecondOrder.KernelSurvivalUnion

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

def kernelHiddenEvent (E : ∀ n, H → FiniteHistory S A n → Prop) (n : ℕ) :
    Set (FiniteHistory (H × S) A n) :=
  {h | E n (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)}

theorem kernelHiddenEvent_measurable (E : ∀ n, H → FiniteHistory S A n → Prop)
    (hE : ∀ n, MeasurableSet {z : H × FiniteHistory S A n | E n z.1 z.2}) (n : ℕ) :
    MeasurableSet (kernelHiddenEvent E n) := (hE n).preimage (historyHiddenPair_measurable n)

/-- The reference probability of any activation in the actual sequence
of queries, including the terminal test, is bounded directly from its
time marginals. No finite response support is used. -/
theorem kernelStageReference_ever_bound (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (selected : ∀ n, FiniteHistory S A n → Prop) (hs : ∀ n, MeasurableSet {h | selected n h})
    (cap : ℕ) (Q dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (Q n)] [∀ n, IsMarkovKernel (dummy n)]
    (E : ∀ n, H → FiniteHistory S A n → Prop)
    (hE : ∀ n, MeasurableSet {z : H × FiniteHistory S A n | E n z.1 z.2})
    {δ : ℝ} (hδ : 0≤δ) (htail : ∀ n h, ρ.real {θ | E n θ h}≤δ) (N : ℕ) :
    (kernelStageReferenceLaw ρ μ selected hs cap Q dummy N).real
      (kernelSurvivalSet (fun n => (kernelHiddenEvent E n)ᶜ) N)ᶜ≤(N+1:ℕ)*δ := by
  unfold kernelStageReferenceLaw
  change (adaptiveKernelLaw (ρ.prod μ)
    (cappedResponseKernel (fun n h => selected n (finiteHistoryMapInitial Prod.snd n h))
      (fun n => (hs n).preimage (finiteHistoryMapInitial_measurable measurable_snd n)) cap
      (hiddenIndependentKernel Q) (hiddenIndependentKernel dummy)) N).real _≤_
  rw [cappedResponseKernel_hidden selected hs cap Q dummy]
  apply adaptiveKernelLaw_exit_uniform (ρ.prod μ) _ (fun n => (kernelHiddenEvent E n)ᶜ)
    (fun n => (kernelHiddenEvent_measurable E hE n).compl) N
  intro n _
  rw [compl_compl]
  exact hiddenIndependentKernel_reference_event_real ρ μ _ n (E n) (hE n) hδ (htail n)

/-- An actual capped stage activates at one of its pre-response queries
or its terminal output with probability at most the information budget
divided by the prior rarity logarithm. -/
theorem kernelStage_firstActivation_bound (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ] [MeasurableSpace.CountablyGenerated A]
    (selected : ∀ n, FiniteHistory S A n → Prop) (hs : ∀ n, MeasurableSet {h | selected n h})
    (cap : ℕ) (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    (Q dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)] [∀ n, IsMarkovKernel (dummy n)]
    {κ : ℝ} (hκ : 0≤κ)
    (hKL : ∀ n h, klDiv (K n h) (Q n (finiteHistoryMapInitial Prod.snd n h))≤ENNReal.ofReal κ)
    (hsame : ∀ n h, ¬stageSelected selected n h → K n h=Q n (finiteHistoryMapInitial Prod.snd n h))
    (E : ∀ n, H → FiniteHistory S A n → Prop)
    (hE : ∀ n, MeasurableSet {z : H × FiniteHistory S A n | E n z.1 z.2})
    {δ L : ℝ} (hδ : 0<δ) (htail : ∀ n h, ρ.real {θ | E n θ h}≤δ)
    (N : ℕ) (hL : 0<L) (hlog : L≤Real.log (1/((N+1:ℕ)*δ))) :
    (kernelStageTrueLaw ρ μ selected hs cap K dummy N).real
      (kernelSurvivalSet (fun n => (kernelHiddenEvent E n)ᶜ) N)ᶜ≤((cap:ℝ)*κ+Real.log 2)/L := by
  have hi : klDiv (kernelStageTrueLaw ρ μ selected hs cap K dummy N)
      (kernelStageReferenceLaw ρ μ selected hs cap Q dummy N)≤ENNReal.ofReal ((cap:ℝ)*κ) :=
    cappedAdaptiveKernelLaw_kl (ρ.prod μ) (stageSelected selected) (stageSelected_measurable selected hs)
      cap K (hiddenIndependentKernel Q) (hiddenIndependentKernel dummy) hκ hKL hsame N
  exact measure_rare_event_bound
    (kernelSurvivalSet_measurable _ (fun n => (kernelHiddenEvent_measurable E hE n).compl) N).compl
    (by positivity) (mul_nonneg (Nat.cast_nonneg _) hκ) hi hL hlog
    (kernelStageReference_ever_bound ρ μ selected hs cap Q dummy E hE hδ.le htail N)

end
end SecondOrder
