import SampleReuse.DisclosureEntropy
import SecondOrder.CappedKernelInformation
import Mathlib.MeasureTheory.Group.Arithmetic

/-! Persistent disclosure with an arbitrary measurable private random seed. -/

open MeasureTheory ProbabilityTheory InformationTheory SecondOrder
open scoped ENNReal Classical

universe u
namespace SampleReuse
noncomputable section
variable {S A Key : Type u} [Fintype A]
  [MeasurableSpace S] [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace Key] [MeasurableSingletonClass Key] [Countable Key]

local instance : MeasurableSpace (Option A) := ⊤
local instance : MeasurableSingletonClass (Option A) := ⟨fun _ => trivial⟩

/-- Evaluating the reconstructed cache is jointly measurable in the full
history and the requested key, without a finiteness assumption on the seed. -/
theorem disclosureCache_joint_measurable
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n)) :
    ∀ n, Measurable (fun h : FiniteHistory S A n × Key =>
      disclosureCache query n h.1 h.2) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun h : (FiniteHistory S A n × A) × Key =>
      Function.update (disclosureCache query n h.1.1) (query n h.1.1) (some h.1.2) h.2)
    simp only [Function.update_apply]
    apply Measurable.ite
      (measurableSet_eq_fun_of_countable measurable_snd ((hq n).comp measurable_fst.fst))
    · exact (measurable_of_countable (some : A → Option A)).comp measurable_fst.snd
    · exact ih.comp (measurable_fst.fst.prodMk measurable_snd)

theorem disclosureCache_selected_measurable
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (n : ℕ) : Measurable (fun h => disclosureCache query n h (query n h)) :=
  (disclosureCache_joint_measurable query hq n).comp (measurable_id.prodMk (hq n))

/-- The countable input kernel is separated from its history pullback. -/
def disclosureSourceKernel (p : Key → PMF A) : Kernel (Option A × Key) A where
  toFun z := (disclosurePMF z.1 (p z.2)).toMeasure
  measurable' := measurable_of_countable _

/-- Cached-array oracle as a measurable kernel for arbitrary private seeds. -/
def measurableDisclosureKernel (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : Key → PMF A)
    (n : ℕ) : Kernel (FiniteHistory S A n) A :=
  (disclosureSourceKernel p).comap
    (fun h => (disclosureCache query n h (query n h), query n h))
    ((disclosureCache_selected_measurable query hq n).prodMk (hq n))

instance measurableDisclosureKernel_markov
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : Key → PMF A) (n : ℕ) :
    IsMarkovKernel (measurableDisclosureKernel query hq p n) where
  isProbabilityMeasure h := by
    change IsProbabilityMeasure (disclosurePMF _ _).toMeasure
    infer_instance

theorem disclosureCharge_measurable
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (κ : ℝ) (n : ℕ) : Measurable (disclosureCharge query κ n) :=
  Measurable.ite
    ((disclosureCache_selected_measurable query hq n) (measurableSet_singleton none))
    measurable_const measurable_const

/-- Actual transcript KL, with arbitrary private randomization, counts only
new handle-block arrays. The same key can be revisited without limit. -/
theorem measurable_adaptive_disclosure_kl
    (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p q : Key → PMF A) {κ : ℝ} (hκ : 0 ≤ κ)
    (hKL : ∀ key, klDiv (p key).toMeasure (q key).toMeasure ≤ ENNReal.ofReal κ)
    (N : ℕ) :
    klDiv (adaptiveKernelLaw μ (measurableDisclosureKernel query hq p) N)
      (adaptiveKernelLaw μ (measurableDisclosureKernel query hq q) N) ≤
      ENNReal.ofReal (κ * ∫ h, (firstDisclosureCount query N h : ℝ)
        ∂adaptiveKernelLaw μ (measurableDisclosureKernel query hq p) N) := by
  have hb (n : ℕ) (h : FiniteHistory S A n) :
      0 ≤ disclosureCharge query κ n h ∧ disclosureCharge query κ n h ≤ κ := by
    unfold disclosureCharge
    split_ifs <;> exact ⟨by positivity, by first | exact le_rfl | exact hκ⟩
  have hk (n : ℕ) (h : FiniteHistory S A n) :
      klDiv (measurableDisclosureKernel query hq p n h)
        (measurableDisclosureKernel query hq q n h) ≤
        ENNReal.ofReal (disclosureCharge query κ n h) :=
    disclosurePMF_kl _ _ _ (hKL (query n h))
  have ht := adaptiveKernelLaw_kl_le μ (measurableDisclosureKernel query hq p)
    (measurableDisclosureKernel query hq q) (disclosureCharge query κ)
    (disclosureCharge_measurable query hq κ) hκ hb hk N
  simpa only [disclosureCharge_total, integral_const_mul] using ht

/-- First disclosure of a key belonging to a specified hidden stage. -/
def stageDisclosure (query : ∀ n, FiniteHistory S A n → Key) (target : Key → Prop)
    (n : ℕ) (h : FiniteHistory S A n) : Prop :=
  disclosureCache query n h (query n h) = none ∧ target (query n h)

theorem stageDisclosure_measurable
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (target : Key → Prop) (n : ℕ) : MeasurableSet {h | stageDisclosure query target n h} :=
  ((disclosureCache_selected_measurable query hq n) (measurableSet_singleton none)).inter
    ((hq n) (Set.to_countable {key | target key}).measurableSet)

/-- A stopped continuation comparing only one stage pays at most cap·κ.
Other-stage arrays retain their common law, and reused arrays contribute zero.
The private seed may have any measurable probability distribution. -/
theorem measurable_stage_disclosure_cap_kl
    (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p q : Key → PMF A) (target : Key → Prop)
    (hsame : ∀ key, ¬target key → p key = q key)
    (dummy : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (dummy n)]
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hKL : ∀ key, klDiv (p key).toMeasure (q key).toMeasure ≤ ENNReal.ofReal κ)
    (cap N : ℕ) :
    klDiv
      (adaptiveKernelLaw μ
        (cappedResponseKernel (stageDisclosure query target)
          (stageDisclosure_measurable query hq target) cap
          (measurableDisclosureKernel query hq p) dummy) N)
      (adaptiveKernelLaw μ
        (cappedResponseKernel (stageDisclosure query target)
          (stageDisclosure_measurable query hq target) cap
          (measurableDisclosureKernel query hq q) dummy) N) ≤
      ENNReal.ofReal ((cap : ℝ) * κ) := by
  apply cappedAdaptiveKernelLaw_kl μ (stageDisclosure query target)
    (stageDisclosure_measurable query hq target) cap
    (measurableDisclosureKernel query hq p) (measurableDisclosureKernel query hq q)
    dummy hκ
  · intro n h
    change klDiv (disclosurePMF _ _).toMeasure (disclosurePMF _ _).toMeasure ≤ _
    apply (disclosurePMF_kl _ _ _ (hKL (query n h))).trans
    apply ENNReal.ofReal_le_ofReal
    split_ifs <;> first | exact le_rfl | exact hκ
  · intro n h hn
    change (disclosurePMF (disclosureCache query n h (query n h)) (p (query n h))).toMeasure =
      (disclosurePMF (disclosureCache query n h (query n h)) (q (query n h))).toMeasure
    cases hc : disclosureCache query n h (query n h) with
    | none =>
      have hnt : ¬ target (query n h) := by simpa [stageDisclosure, hc] using hn
      rw [hsame _ hnt]
    | some a => rfl

end
end SampleReuse
