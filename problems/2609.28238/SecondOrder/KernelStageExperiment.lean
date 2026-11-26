import SecondOrder.KernelReferenceEvents
import SecondOrder.MeasureRareEvent

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

def stageSelected (selected : ∀ n, FiniteHistory S A n → Prop)
    (n : ℕ) (h : FiniteHistory (H × S) A n) : Prop :=
  selected n (finiteHistoryMapInitial Prod.snd n h)

theorem stageSelected_measurable (selected : ∀ n, FiniteHistory S A n → Prop)
    (hs : ∀ n, MeasurableSet {h | selected n h}) (n : ℕ) :
    MeasurableSet {h : FiniteHistory (H × S) A n | stageSelected selected n h} :=
  (hs n).preimage (finiteHistoryMapInitial_measurable measurable_snd n)

def kernelStageTrueLaw (ρ : Measure H) (μ : Measure S)
    (selected : ∀ n, FiniteHistory S A n → Prop) (hs : ∀ n, MeasurableSet {h | selected n h})
    (cap : ℕ) (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    (dummy : ∀ n, Kernel (FiniteHistory S A n) A) (N : ℕ) : Measure (FiniteHistory (H × S) A N) :=
  adaptiveKernelLaw (ρ.prod μ) (cappedResponseKernel (stageSelected selected)
    (stageSelected_measurable selected hs) cap K (hiddenIndependentKernel dummy)) N

def kernelStageReferenceLaw (ρ : Measure H) (μ : Measure S)
    (selected : ∀ n, FiniteHistory S A n → Prop) (hs : ∀ n, MeasurableSet {h | selected n h})
    (cap : ℕ) (Q dummy : ∀ n, Kernel (FiniteHistory S A n) A) (N : ℕ) : Measure (FiniteHistory (H × S) A N) :=
  adaptiveKernelLaw (ρ.prod μ) (cappedResponseKernel (stageSelected selected)
    (stageSelected_measurable selected hs) cap (hiddenIndependentKernel Q) (hiddenIndependentKernel dummy)) N

instance kernelStageTrueLaw_probability (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (selected : ∀ n, FiniteHistory S A n → Prop) (hs : ∀ n, MeasurableSet {h | selected n h})
    (cap : ℕ) (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    (dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (dummy n)] (N : ℕ) :
    IsProbabilityMeasure (kernelStageTrueLaw ρ μ selected hs cap K dummy N) := by
  unfold kernelStageTrueLaw
  infer_instance

instance kernelStageReferenceLaw_probability (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (selected : ∀ n, FiniteHistory S A n → Prop) (hs : ∀ n, MeasurableSet {h | selected n h})
    (cap : ℕ) (Q dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (Q n)] [∀ n, IsMarkovKernel (dummy n)] (N : ℕ) :
    IsProbabilityMeasure (kernelStageReferenceLaw ρ μ selected hs cap Q dummy N) := by
  unfold kernelStageReferenceLaw
  infer_instance

def kernelStageEvent {ι : Type*} (N : ℕ) (E : ι → H → FiniteHistory S A N → Prop) :
    Set (FiniteHistory (H × S) A N) :=
  {h | ∃ i, E i (finiteHistoryInitial N h).1 (finiteHistoryMapInitial Prod.snd N h)}

theorem kernelStageEvent_measurable {ι : Type*} [Fintype ι] (N : ℕ)
    (E : ι → H → FiniteHistory S A N → Prop)
    (hE : ∀ i, MeasurableSet {z : H × FiniteHistory S A N | E i z.1 z.2}) :
    MeasurableSet (kernelStageEvent N E) := by
  have he : kernelStageEvent N E =
      ⋃ i, {h | E i (finiteHistoryInitial N h).1 (finiteHistoryMapInitial Prod.snd N h)} := by
    ext h
    simp only [kernelStageEvent,Set.mem_setOf_eq,Set.mem_iUnion]
  rw [he]
  exact MeasurableSet.iUnion (fun i => (hE i).preimage (historyHiddenPair_measurable N))

/-- A capped adaptive stage with an arbitrary countably generated response
space. Both its entropy budget and its reference activation probability are
derived from the kernels and the hidden prior. -/
theorem kernelStage_activation_bound (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ] [MeasurableSpace.CountablyGenerated A]
    (selected : ∀ n, FiniteHistory S A n → Prop) (hs : ∀ n, MeasurableSet {h | selected n h})
    (cap : ℕ) (K : ∀ n, Kernel (FiniteHistory (H × S) A n) A)
    (Q dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)] [∀ n, IsMarkovKernel (dummy n)]
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hKL : ∀ n h, klDiv (K n h) (Q n (finiteHistoryMapInitial Prod.snd n h)) ≤ ENNReal.ofReal κ)
    (hsame : ∀ n h, ¬ stageSelected selected n h → K n h=Q n (finiteHistoryMapInitial Prod.snd n h))
    (N : ℕ) (E : Fin (N+1) → H → FiniteHistory S A N → Prop)
    (hE : ∀ i, MeasurableSet {z : H × FiniteHistory S A N | E i z.1 z.2})
    {δ L : ℝ} (hδ : 0 < δ) (htail : ∀ i h, ρ.real {θ | E i θ h} ≤ δ)
    (hL : 0 < L) (hlog : L ≤ Real.log (1/((N+1:ℕ)*δ))) :
    (kernelStageTrueLaw ρ μ selected hs cap K dummy N).real (kernelStageEvent N E) ≤
      ((cap:ℝ)*κ+Real.log 2)/L := by
  have hi : klDiv (kernelStageTrueLaw ρ μ selected hs cap K dummy N)
      (kernelStageReferenceLaw ρ μ selected hs cap Q dummy N) ≤ ENNReal.ofReal ((cap:ℝ)*κ) :=
    cappedAdaptiveKernelLaw_kl (ρ.prod μ) (stageSelected selected) (stageSelected_measurable selected hs)
      cap K (hiddenIndependentKernel Q) (hiddenIndependentKernel dummy) hκ hKL hsame N
  have hr : (kernelStageReferenceLaw ρ μ selected hs cap Q dummy N).real (kernelStageEvent N E) ≤
      (N+1:ℕ)*δ := by
    simpa only [Fintype.card_fin] using cappedKernel_reference_union ρ μ selected hs cap Q dummy N E hE hδ.le htail
  exact measure_rare_event_bound (kernelStageEvent_measurable N E hE) (by positivity)
    (mul_nonneg (Nat.cast_nonneg _) hκ) hi hL hlog hr

end
end SecondOrder
