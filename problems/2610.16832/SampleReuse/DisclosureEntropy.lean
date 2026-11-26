import SecondOrder.CoefficientResponse
import SecondOrder.AdaptiveKernelLaw

/-!
Persistent array disclosure: an array is drawn at its first use and cached.
The adaptive transcript has relative entropy bounded by the expected number
of first disclosures, not the number of repeated calls. Keys can be pairs
(sample handle, hidden block). The construction below is an actual probability
kernel experiment, with a finite private seed and finite array alphabet.

This file does not yet identify the manuscript's full derivative oracle with
this experiment, nor prove the stage-entry and far-activation assertions.
-/

open MeasureTheory ProbabilityTheory InformationTheory SecondOrder
open scoped ENNReal Classical

universe u
namespace SampleReuse
noncomputable section

/-- A saved array is returned deterministically; an unseen array is sampled. -/
def disclosurePMF {A : Type u} (saved : Option A) (p : PMF A) : PMF A :=
  match saved with
  | none => p
  | some a => PMF.pure a

theorem disclosurePMF_reused {A : Type u} (a : A) (p q : PMF A) :
    disclosurePMF (some a) p = disclosurePMF (some a) q := rfl

theorem disclosurePMF_kl {A : Type u} [MeasurableSpace A]
    (saved : Option A) (p q : PMF A) {κ : ℝ}
    (hKL : klDiv p.toMeasure q.toMeasure ≤ ENNReal.ofReal κ) :
    klDiv (disclosurePMF saved p).toMeasure (disclosurePMF saved q).toMeasure ≤
      ENNReal.ofReal (if saved = none then κ else 0) := by
  cases saved with
  | none => simpa only [disclosurePMF, if_true] using hKL
  | some a => simp [disclosurePMF, klDiv_self]

/-- The manuscript's actual biased coefficient array has KL at most D/R²
on first disclosure and zero on every later use. -/
theorem coefficient_disclosure_kl {ι : Type u} [Fintype ι]
    (R : ℝ) (θ : ι → ℝ) (hR : 2 ≤ R) (hθ : ∀ i, θ i ^ 2 = 1)
    (saved : Option (ι → SignedCoefficient R)) :
    klDiv
        (disclosurePMF saved
          (finitePiPMF (fun i => coefficientPMF R (θ i) hR (hθ i)))).toMeasure
        (disclosurePMF saved
          (finitePiPMF (fun _ : ι => fairCoefficientPMF R hR))).toMeasure ≤
      ENNReal.ofReal (if saved = none then (Fintype.card ι : ℝ) / R ^ 2 else 0) :=
  by
    cases saved with
    | none => simpa [disclosurePMF] using klDiv_coefficientProduct R θ hR hθ
    | some a => simp [disclosurePMF, klDiv_self]

section Adaptive
variable {S A Key : Type u} [Fintype S] [Fintype A]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Reconstruct the stored table from the actual query/response history. -/
def disclosureCache (query : ∀ n, FiniteHistory S A n → Key) :
    (n : ℕ) → FiniteHistory S A n → Key → Option A
  | 0, _ => fun _ => none
  | n + 1, h => Function.update (disclosureCache query n h.1) (query n h.1) (some h.2)

omit [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem disclosureCache_after_response
    (query : ∀ n, FiniteHistory S A n → Key) (n : ℕ)
    (h : FiniteHistory S A n) (a : A) :
    disclosureCache query (n + 1) (h, a) (query n h) = some a := by
  simp [disclosureCache]

/-- Conditional law of the next revealed array, including exact replay. -/
def disclosureKernel (query : ∀ n, FiniteHistory S A n → Key)
    (p : Key → PMF A) (n : ℕ) : Kernel (FiniteHistory S A n) A where
  toFun h := (disclosurePMF (disclosureCache query n h (query n h)) (p (query n h))).toMeasure
  measurable' := measurable_of_countable _

instance disclosureKernel_markov (query : ∀ n, FiniteHistory S A n → Key)
    (p : Key → PMF A) (n : ℕ) : IsMarkovKernel (disclosureKernel query p n) where
  isProbabilityMeasure h := by
    change IsProbabilityMeasure (disclosurePMF _ _).toMeasure
    infer_instance

/-- A deterministic function of the history: each newly disclosed key costs one. -/
def firstDisclosureCount (query : ∀ n, FiniteHistory S A n → Key) :
    (n : ℕ) → FiniteHistory S A n → ℕ
  | 0, _ => 0
  | n + 1, h => firstDisclosureCount query n h.1 +
      if disclosureCache query n h.1 (query n h.1) = none then 1 else 0

omit [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem firstDisclosureCount_le (query : ∀ n, FiniteHistory S A n → Key) :
    ∀ n h, firstDisclosureCount query n h ≤ n := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [firstDisclosureCount]
    split_ifs <;> have := ih h.1 <;> omega

def disclosureCharge (query : ∀ n, FiniteHistory S A n → Key) (κ : ℝ)
    (n : ℕ) (h : FiniteHistory S A n) : ℝ :=
  if disclosureCache query n h (query n h) = none then κ else 0

omit [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem disclosureCharge_total (query : ∀ n, FiniteHistory S A n → Key) (κ : ℝ) :
    ∀ n h, finiteHistoryCost (disclosureCharge query κ) n h =
      κ * firstDisclosureCount query n h := by
  intro n
  induction n with
  | zero => intro h; simp [finiteHistoryCost, firstDisclosureCount]
  | succ n ih =>
    intro h
    simp only [finiteHistoryCost, disclosureCharge, firstDisclosureCount, ih h.1]
    split_ifs <;> push_cast <;> ring

/-- The actual adaptive transcript's KL is charged only for first disclosures.
Repeated queries, adaptively chosen handles, and arbitrary returns to old keys
are all included. The shared private seed has the same law in both experiments. -/
theorem adaptive_disclosure_kl
    (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (p q : Key → PMF A)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hKL : ∀ key, klDiv (p key).toMeasure (q key).toMeasure ≤ ENNReal.ofReal κ)
    (N : ℕ) :
    klDiv (adaptiveKernelLaw μ (disclosureKernel query p) N)
      (adaptiveKernelLaw μ (disclosureKernel query q) N) ≤
      ENNReal.ofReal (κ * ∫ h, (firstDisclosureCount query N h : ℝ)
        ∂adaptiveKernelLaw μ (disclosureKernel query p) N) := by
  have hb (n : ℕ) (h : FiniteHistory S A n) :
      0 ≤ disclosureCharge query κ n h ∧ disclosureCharge query κ n h ≤ κ := by
    unfold disclosureCharge
    split_ifs <;> exact ⟨by positivity, by first | exact le_rfl | exact hκ⟩
  have hk (n : ℕ) (h : FiniteHistory S A n) :
      klDiv (disclosureKernel query p n h) (disclosureKernel query q n h) ≤
        ENNReal.ofReal (disclosureCharge query κ n h) :=
    disclosurePMF_kl _ _ _ (hKL (query n h))
  have ht := adaptiveKernelLaw_kl_le μ (disclosureKernel query p)
    (disclosureKernel query q) (disclosureCharge query κ)
    (fun _ => measurable_of_countable _) hκ hb hk N
  simpa only [disclosureCharge_total, integral_const_mul] using ht

end Adaptive
end
end SampleReuse
