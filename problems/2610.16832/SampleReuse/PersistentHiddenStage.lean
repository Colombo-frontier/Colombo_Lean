import SampleReuse.MeasurableDisclosure
import SecondOrder.KernelStageFirstActivation

/-! Capped persistent disclosures of a genuinely random hidden parameter.
The private seed has an arbitrary measurable law. The reference cache keeps
every previously returned array and remains independent of the hidden block. -/

open MeasureTheory ProbabilityTheory InformationTheory SecondOrder
open scoped ENNReal Classical
namespace SampleReuse
noncomputable section
variable {H S A Key : Type} [Fintype H] [Fintype A] [Countable Key]
  [MeasurableSpace H] [MeasurableSingletonClass H] [MeasurableSpace S]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace Key] [MeasurableSingletonClass Key]

local instance : MeasurableSpace (Option A) := ⊤
local instance : MeasurableSingletonClass (Option A) := ⟨fun _ => trivial⟩

def hiddenDisclosureSourceKernel (p : H → Key → PMF A) : Kernel (H × (Option A × Key)) A where
  toFun z := (disclosurePMF z.2.1 (p z.1 z.2.2)).toMeasure
  measurable' := measurable_of_countable _

def hiddenDisclosureKernel (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : H → Key → PMF A)
    (n : ℕ) : Kernel (FiniteHistory (H × S) A n) A :=
  (hiddenDisclosureSourceKernel p).comap
    (fun h => ((finiteHistoryInitial n h).1,
      (disclosureCache query n (finiteHistoryMapInitial Prod.snd n h)
        (query n (finiteHistoryMapInitial Prod.snd n h)),
       query n (finiteHistoryMapInitial Prod.snd n h))))
    ((measurable_fst.comp (finiteHistoryInitial_measurable n)).prodMk
      (((disclosureCache_selected_measurable query hq n).comp
        (finiteHistoryMapInitial_measurable measurable_snd n)).prodMk
        ((hq n).comp (finiteHistoryMapInitial_measurable measurable_snd n))))

instance hiddenDisclosureKernel_markov (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : H → Key → PMF A) (n : ℕ) :
    IsMarkovKernel (hiddenDisclosureKernel query hq p n) where
  isProbabilityMeasure h := by
    change IsProbabilityMeasure (disclosurePMF _ _).toMeasure
    infer_instance

/-- Counts target-stage responses, including revisits. Its entropy cost
can only be smaller, since an already cached array has conditional KL zero. -/
def targetDisclosure (query : ∀ n, FiniteHistory S A n → Key) (target : Key → Prop)
    (n : ℕ) (h : FiniteHistory S A n) : Prop := target (query n h)

omit [Fintype A] [MeasurableSingletonClass A] in
theorem targetDisclosure_measurable (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (target : Key → Prop) (n : ℕ) :
    MeasurableSet {h | targetDisclosure query target n h} :=
  (hq n) (Set.to_countable {key | target key}).measurableSet

theorem hiddenDisclosureKernel_kl (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : H → Key → PMF A) (q : Key → PMF A)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hKL : ∀ θ key, klDiv (p θ key).toMeasure (q key).toMeasure ≤ ENNReal.ofReal κ)
    (n : ℕ) (h : FiniteHistory (H × S) A n) :
    klDiv (hiddenDisclosureKernel query hq p n h)
      (measurableDisclosureKernel query hq q n (finiteHistoryMapInitial Prod.snd n h)) ≤
      ENNReal.ofReal κ := by
  change klDiv (disclosurePMF _ _).toMeasure (disclosurePMF _ _).toMeasure ≤ _
  apply (disclosurePMF_kl _ _ _ (hKL (finiteHistoryInitial n h).1
    (query n (finiteHistoryMapInitial Prod.snd n h)))).trans
  apply ENNReal.ofReal_le_ofReal
  split_ifs <;> first | exact le_rfl | exact hκ

theorem hiddenDisclosureKernel_same (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : H → Key → PMF A) (q : Key → PMF A)
    (target : Key → Prop) (hsame : ∀ θ key, ¬target key → p θ key = q key)
    (n : ℕ) (h : FiniteHistory (H × S) A n)
    (hn : ¬stageSelected (targetDisclosure query target) n h) :
    hiddenDisclosureKernel query hq p n h =
      measurableDisclosureKernel query hq q n (finiteHistoryMapInitial Prod.snd n h) := by
  change (disclosurePMF _ (p (finiteHistoryInitial n h).1
      (query n (finiteHistoryMapInitial Prod.snd n h)))).toMeasure = _
  rw [hsame _ _ hn]
  rfl

/-- Persistent-stage activation probability is derived from its actual
cached response kernels, a product entry prior, and a uniform prior tail.
Neither conditional independence of reused samples nor a KL conclusion is
assumed. The terminal output is included in the event. -/
theorem persistent_stage_firstActivation_bound
    (ρ : Measure H) [IsProbabilityMeasure ρ] (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : H → Key → PMF A) (q : Key → PMF A) (target : Key → Prop)
    (hsame : ∀ θ key, ¬target key → p θ key = q key)
    (cap : ℕ) (dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (dummy n)]
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hKL : ∀ θ key, klDiv (p θ key).toMeasure (q key).toMeasure ≤ ENNReal.ofReal κ)
    (E : ∀ n, H → FiniteHistory S A n → Prop)
    (hE : ∀ n, MeasurableSet {z : H × FiniteHistory S A n | E n z.1 z.2})
    {δ L : ℝ} (hδ : 0 < δ) (htail : ∀ n h, ρ.real {θ | E n θ h} ≤ δ)
    (N : ℕ) (hL : 0 < L) (hlog : L ≤ Real.log (1 / ((N + 1 : ℕ) * δ))) :
    (kernelStageTrueLaw ρ μ (targetDisclosure query target)
      (targetDisclosure_measurable query hq target) cap (hiddenDisclosureKernel query hq p) dummy N).real
      (kernelSurvivalSet (fun n => (kernelHiddenEvent E n)ᶜ) N)ᶜ ≤
      ((cap : ℝ) * κ + Real.log 2) / L :=
  kernelStage_firstActivation_bound ρ μ (targetDisclosure query target)
    (targetDisclosure_measurable query hq target) cap (hiddenDisclosureKernel query hq p)
    (measurableDisclosureKernel query hq q) dummy hκ
    (hiddenDisclosureKernel_kl query hq p q hκ hKL)
    (hiddenDisclosureKernel_same query hq p q target hsame) E hE hδ htail N hL hlog

end
end SampleReuse
