import SampleReuse.PersistentTableLaw
import SampleReuse.MeasurableDisclosure

/-! Fixed reusable-table transcript laws for arbitrary measurable private seeds. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped Classical ENNReal
namespace SampleReuse
noncomputable section
variable {S Key A : Type} [Fintype Key] [Fintype A]
  [MeasurableSpace S] [MeasurableSpace Key] [MeasurableSingletonClass Key]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem tableHistory_measurable (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) :
    ∀ n, Measurable (fun z : S × (Key → A) => tableHistory query z.1 z.2 n) := by
  intro n
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    change Measurable (fun z : S × (Key → A) =>
      (tableHistory query z.1 z.2 n, z.2 (query n (tableHistory query z.1 z.2 n))))
    exact ih.prodMk ((measurable_of_countable (fun z : (Key → A) × Key => z.1 z.2)).comp
      (measurable_snd.prodMk ((hq n).comp ih)))

def preallocatedHistoryKernel (query : ∀ n, FiniteHistory S A n → Key)
    (_hq : ∀ n, Measurable (query n)) (p : Key → PMF A)
    (n : ℕ) : Kernel S (FiniteHistory S A n) :=
  (Kernel.id ×ₖ Kernel.const S (finitePiPMF p).toMeasure).map
    (fun z : S × (Key → A) => tableHistory query z.1 z.2 n)

instance preallocatedHistoryKernel_markov (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : Key → PMF A) (n : ℕ) :
    IsMarkovKernel (preallocatedHistoryKernel query hq p n) := by
  unfold preallocatedHistoryKernel
  exact Kernel.IsMarkovKernel.map _ (tableHistory_measurable query hq n)

theorem preallocatedHistoryKernel_apply (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : Key → PMF A) (n : ℕ) (s : S) :
    preallocatedHistoryKernel query hq p n s = (preallocatedHistoryPMF query p s n).toMeasure := by
  rw [preallocatedHistoryKernel, Kernel.map_apply _ (tableHistory_measurable query hq n),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (tableHistory_measurable query hq n) measurable_prodMk_left]
  exact PMF.toMeasure_map _ _ (measurable_of_countable _)

theorem kernel_comp_finite_map {B C D : Type*} [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B] [MeasurableSpace C] [MeasurableSpace D]
    (p : PMF B) (f : B → C) (hf : Measurable f) (K : Kernel C D)
    (q : C → PMF D) (hK : ∀ c, K c = (q c).toMeasure) :
    K ∘ₘ (p.map f).toMeasure = (p.bind (fun b => q (f b))).toMeasure := by
  ext E hE
  rw [Measure.bind_apply hE K.aemeasurable, ← PMF.toMeasure_map f p hf,
    lintegral_map' (K.measurable_coe hE).aemeasurable hf.aemeasurable, lintegral_fintype,
    PMF.toMeasure_bind_apply _ _ _ hE, tsum_fintype]
  apply Finset.sum_congr rfl
  intro b _
  rw [hK, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  exact mul_comm _ _

theorem append_disclosure_kernel_apply (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : Key → PMF A) (n : ℕ) (h : FiniteHistory S A n) :
    (Kernel.id ×ₖ measurableDisclosureKernel query hq p n) h =
      ((disclosurePMF (disclosureCache query n h (query n h)) (p (query n h))).map (fun a => (h, a))).toMeasure := by
  rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod]
  exact PMF.toMeasure_map _ _ measurable_prodMk_left

theorem preallocatedHistoryKernel_succ (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : Key → PMF A) (n : ℕ) :
    preallocatedHistoryKernel query hq p (n + 1) =
      (Kernel.id ×ₖ measurableDisclosureKernel query hq p n) ∘ₖ preallocatedHistoryKernel query hq p n := by
  ext s : 1
  change preallocatedHistoryKernel query hq p (n + 1) s =
    (preallocatedHistoryKernel query hq p n s).bind (Kernel.id ×ₖ measurableDisclosureKernel query hq p n)
  rw [preallocatedHistoryKernel_apply, preallocatedHistoryPMF_succ,
    preallocatedHistoryKernel_apply]
  have hh := kernel_comp_finite_map (finitePiPMF p)
    (fun table => tableHistory query s table n) (measurable_of_countable _)
    (Kernel.id ×ₖ measurableDisclosureKernel query hq p n)
    (fun h => (disclosurePMF (disclosureCache query n h (query n h)) (p (query n h))).map (fun a => (h, a)))
    (append_disclosure_kernel_apply query hq p n)
  unfold preallocatedHistoryPMF
  rw [PMF.bind_map]
  exact hh.symm

theorem preallocatedHistoryKernel_zero (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : Key → PMF A) :
    preallocatedHistoryKernel query hq p 0 = Kernel.id := by
  ext s : 1
  rw [preallocatedHistoryKernel_apply]
  change ((finitePiPMF p).map (Function.const (Key → A) s)).toMeasure = Measure.dirac s
  rw [PMF.map_const, PMF.toMeasure_pure]

/-- Exact transcript law equality with arbitrary private randomization. The
finite table has a coordinate for every possible handle/block key. -/
theorem preallocated_kernel_law (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : Key → PMF A)
    (μ : Measure S) [IsProbabilityMeasure μ] :
    ∀ n, preallocatedHistoryKernel query hq p n ∘ₘ μ =
      adaptiveKernelLaw μ (measurableDisclosureKernel query hq p) n := by
  intro n
  induction n with
  | zero =>
    rw [preallocatedHistoryKernel_zero]
    exact Measure.bind_dirac
  | succ n ih =>
    rw [preallocatedHistoryKernel_succ, ← Measure.comp_assoc, ih, adaptiveKernelLaw,
      Measure.compProd_eq_comp_prod]
    rfl

/-- Explicit product-measure formulation: all reusable coefficients are
sampled once, independently of the arbitrary private seed, before execution. -/
theorem fixed_table_transcript_law (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : Key → PMF A)
    (μ : Measure S) [IsProbabilityMeasure μ] (n : ℕ) :
    (μ.prod (finitePiPMF p).toMeasure).map
        (fun z : S × (Key → A) => tableHistory query z.1 z.2 n) =
      adaptiveKernelLaw μ (measurableDisclosureKernel query hq p) n := by
  rw [← preallocated_kernel_law query hq p μ n]
  unfold preallocatedHistoryKernel
  rw [← Measure.map_comp μ _ (tableHistory_measurable query hq n),
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

end
end SampleReuse
