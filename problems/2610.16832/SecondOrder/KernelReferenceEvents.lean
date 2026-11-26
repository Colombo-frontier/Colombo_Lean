import SecondOrder.KernelHiddenIndependence
import SecondOrder.CappedKernelInformation

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical BigOperators

universe u
namespace SecondOrder
noncomputable section
variable {H S A : Type u} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace A]

theorem hiddenIndependentKernel_reference_event_real (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Q : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (Q n)]
    (n : ℕ) (E : H → FiniteHistory S A n → Prop)
    (hE : MeasurableSet {z : H × FiniteHistory S A n | E z.1 z.2})
    {q : ℝ} (hq : 0 ≤ q) (htail : ∀ h, ρ.real {θ | E θ h} ≤ q) :
    (adaptiveKernelLaw (ρ.prod μ) (hiddenIndependentKernel Q) n).real
      {h | E (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)} ≤ q := by
  apply ENNReal.toReal_le_of_le_ofReal hq
  apply hiddenIndependentKernel_reference_event ρ μ Q n E hE
  intro h
  rw [← ENNReal.ofReal_toReal (measure_ne_top ρ {θ | E θ h})]
  exact ENNReal.ofReal_le_ofReal (htail h)

/-- All queries and the output may be measurable functions of the entire
reference history. Their activation events retain the independent prior tail. -/
theorem hiddenIndependentKernel_reference_union (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Q : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (Q n)]
    {ι : Type*} [Fintype ι] (n : ℕ) (E : ι → H → FiniteHistory S A n → Prop)
    (hE : ∀ i, MeasurableSet {z : H × FiniteHistory S A n | E i z.1 z.2})
    {q : ℝ} (hq : 0 ≤ q) (htail : ∀ i h, ρ.real {θ | E i θ h} ≤ q) :
    (adaptiveKernelLaw (ρ.prod μ) (hiddenIndependentKernel Q) n).real
      {h | ∃ i, E i (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)} ≤
      (Fintype.card ι:ℝ)*q := by
  have he : {h : FiniteHistory (H × S) A n |
      ∃ i, E i (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)} =
      ⋃ i, {h | E i (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)} := by
    ext h
    simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _i : ι, q := Finset.sum_le_sum (fun i _ =>
      hiddenIndependentKernel_reference_event_real ρ μ Q n (E i) (hE i) hq (htail i))
    _ = (Fintype.card ι:ℝ)*q := by simp

theorem kernelChargeCount_hidden (selected : ∀ n, FiniteHistory S A n → Prop) (cap : ℕ) :
    ∀ n (h : FiniteHistory (H × S) A n),
    kernelChargeCount (fun n h => selected n (finiteHistoryMapInitial Prod.snd n h)) cap n h =
      kernelChargeCount selected cap n (finiteHistoryMapInitial Prod.snd n h) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [kernelChargeCount,finiteHistoryMapInitial,ih]

theorem cappedResponseKernel_hidden (selected : ∀ n, FiniteHistory S A n → Prop)
    (hs : ∀ n, MeasurableSet {h | selected n h}) (cap : ℕ)
    (Q dummy : ∀ n, Kernel (FiniteHistory S A n) A) :
    cappedResponseKernel (fun n h => selected n (finiteHistoryMapInitial Prod.snd n h))
      (fun n => (hs n).preimage (finiteHistoryMapInitial_measurable measurable_snd n)) cap
      (hiddenIndependentKernel (H := H) Q) (hiddenIndependentKernel dummy) =
      hiddenIndependentKernel (cappedResponseKernel selected hs cap Q dummy) := by
  funext n
  apply Kernel.ext
  intro h
  simp only [cappedResponseKernel,Kernel.piecewise_apply,Set.mem_setOf_eq,
    hiddenIndependentKernel,Kernel.comap_apply,kernelChargeCount_hidden]

theorem cappedKernel_reference_union (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (selected : ∀ n, FiniteHistory S A n → Prop) (hs : ∀ n, MeasurableSet {h | selected n h})
    (cap : ℕ) (Q dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (Q n)] [∀ n, IsMarkovKernel (dummy n)]
    {ι : Type*} [Fintype ι] (n : ℕ) (E : ι → H → FiniteHistory S A n → Prop)
    (hE : ∀ i, MeasurableSet {z : H × FiniteHistory S A n | E i z.1 z.2})
    {q : ℝ} (hq : 0 ≤ q) (htail : ∀ i h, ρ.real {θ | E i θ h} ≤ q) :
    (adaptiveKernelLaw (ρ.prod μ)
      (cappedResponseKernel (fun n h => selected n (finiteHistoryMapInitial Prod.snd n h))
        (fun n => (hs n).preimage (finiteHistoryMapInitial_measurable measurable_snd n)) cap
        (hiddenIndependentKernel Q) (hiddenIndependentKernel dummy)) n).real
      {h | ∃ i, E i (finiteHistoryInitial n h).1 (finiteHistoryMapInitial Prod.snd n h)} ≤
      (Fintype.card ι:ℝ)*q := by
  rw [cappedResponseKernel_hidden selected hs cap Q dummy]
  exact hiddenIndependentKernel_reference_union ρ μ _ n E hE hq htail

end
end SecondOrder
