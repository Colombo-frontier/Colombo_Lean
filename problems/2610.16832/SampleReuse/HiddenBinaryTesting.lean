import SampleReuse.BinaryTesting
import SampleReuse.PersistentHiddenStage

open MeasureTheory ProbabilityTheory InformationTheory SecondOrder
open scoped ENNReal Classical

namespace SampleReuse
noncomputable section

variable {S A Key : Type} [Fintype A] [MeasurableSpace S]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace Key] [MeasurableSingletonClass Key] [Countable Key]

def hiddenSelectedCost (query : ∀ n, FiniteHistory S A n → Key) (target : Key → Prop)
    (κ : ℝ) (n : ℕ) (h : FiniteHistory (Bool × S) A n) : ℝ :=
  if target (query n (finiteHistoryMapInitial Prod.snd n h)) then κ else 0

omit [Fintype A] [MeasurableSingletonClass A] in
theorem hiddenSelectedCost_measurable (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (target : Key → Prop) (κ : ℝ) (n : ℕ) :
    Measurable (hiddenSelectedCost query target κ n) :=
  Measurable.ite (((hq n).comp (finiteHistoryMapInitial_measurable measurable_snd n))
    (Set.to_countable {key | target key}).measurableSet) measurable_const measurable_const

omit [Fintype A] [MeasurableSpace S] [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace Key] [MeasurableSingletonClass Key] [Countable Key] in
theorem hiddenSelectedCost_scale (query : ∀ n, FiniteHistory S A n → Key)
    (target : Key → Prop) (κ : ℝ) : ∀ n h,
    finiteHistoryCost (hiddenSelectedCost query target κ) n h =
      κ*finiteHistoryCost (hiddenSelectedCost query target 1) n h := by
  intro n
  induction n with
  | zero => intro h; simp only [finiteHistoryCost,mul_zero]
  | succ n ih =>
    intro h
    simp only [finiteHistoryCost,ih,hiddenSelectedCost]
    split_ifs <;> ring

/-- Information in a cached binary experiment is charged only to selected
calls. Unselected replies have identical laws, while revisits can only lower KL. -/
theorem hidden_selected_disclosure_information
    (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : Bool → Key → PMF A) (q : Key → PMF A) (target : Key → Prop)
    (hsame : ∀ θ key, ¬target key → p θ key = q key)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hKL : ∀ θ key, klDiv (p θ key).toMeasure (q key).toMeasure ≤ ENNReal.ofReal κ)
    (N : ℕ) :
    klDiv (adaptiveKernelLaw ((PMF.uniformOfFintype Bool).toMeasure.prod μ)
      (hiddenDisclosureKernel query hq p) N)
      (adaptiveKernelLaw ((PMF.uniformOfFintype Bool).toMeasure.prod μ)
        (hiddenIndependentKernel (measurableDisclosureKernel query hq q)) N) ≤
      ENNReal.ofReal (κ*∫ h, finiteHistoryCost (hiddenSelectedCost query target 1) N h
        ∂adaptiveKernelLaw ((PMF.uniformOfFintype Bool).toMeasure.prod μ)
          (hiddenDisclosureKernel query hq p) N) := by
  have hc : ∀ n h, 0 ≤ hiddenSelectedCost query target κ n h ∧
      hiddenSelectedCost query target κ n h ≤ κ := by
    intro n h
    unfold hiddenSelectedCost
    split_ifs <;> exact ⟨by positivity,by first | exact le_rfl | exact hκ⟩
  have hi := adaptiveKernelLaw_kl_le ((PMF.uniformOfFintype Bool).toMeasure.prod μ)
    (hiddenDisclosureKernel query hq p) (hiddenIndependentKernel (measurableDisclosureKernel query hq q))
    (hiddenSelectedCost query target κ) (hiddenSelectedCost_measurable query hq target κ) hκ hc
    (fun n h => by
      unfold hiddenSelectedCost
      split_ifs with ht
      · exact hiddenDisclosureKernel_kl query hq p q hκ hKL n h
      · have he := hiddenDisclosureKernel_same query hq p q target hsame n h ht
        change klDiv (hiddenDisclosureKernel query hq p n h)
          (measurableDisclosureKernel query hq q n (finiteHistoryMapInitial Prod.snd n h)) ≤ _
        rw [he,klDiv_self]
        exact zero_le _) N
  simpa only [hiddenSelectedCost_scale query target κ,integral_const_mul] using hi

omit [Fintype A] [MeasurableSingletonClass A] in
theorem hidden_binary_classification_reference
    (μ : Measure S) [IsProbabilityMeasure μ]
    (Q : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (Q n)]
    (N : ℕ) (classify : FiniteHistory S A N → Bool) (hc : Measurable classify) :
    (adaptiveKernelLaw ((PMF.uniformOfFintype Bool).toMeasure.prod μ)
      (hiddenIndependentKernel Q) N).real
      {h | classify (finiteHistoryMapInitial Prod.snd N h) = (finiteHistoryInitial N h).1} ≤ 1/2 := by
  have hE : MeasurableSet {z : Bool × FiniteHistory S A N | classify z.2 = z.1} :=
    measurableSet_eq_fun_of_countable (hc.comp measurable_snd) measurable_fst
  have hh := hiddenIndependentKernel_reference_event (PMF.uniformOfFintype Bool).toMeasure μ Q N
    (fun θ h => classify h = θ) hE (q := (1/2:ℝ≥0∞)) (fun h => by
      have he : {θ : Bool | classify h = θ} = {classify h} := by ext θ; simp [eq_comm]
      rw [he,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      simp [PMF.uniformOfFintype_apply])
  have ht := ENNReal.toReal_mono (by norm_num : (1/2:ℝ≥0∞) ≠ ∞) hh
  simpa only [measureReal_def,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using ht

/-- Any successful classifier obtained from the actual cached experiment
pays a constant information cost through its selected calls. -/
theorem hidden_binary_testing_calls
    (μ : Measure S) [IsProbabilityMeasure μ]
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : Bool → Key → PMF A) (q : Key → PMF A) (target : Key → Prop)
    (hsame : ∀ θ key, ¬target key → p θ key = q key)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hKL : ∀ θ key, klDiv (p θ key).toMeasure (q key).toMeasure ≤ ENNReal.ofReal κ)
    (N : ℕ) (classify : FiniteHistory S A N → Bool) (hc : Measurable classify)
    (hsuccess : (2/3:ℝ) ≤
      (adaptiveKernelLaw ((PMF.uniformOfFintype Bool).toMeasure.prod μ)
        (hiddenDisclosureKernel query hq p) N).real
        {h | classify (finiteHistoryMapInitial Prod.snd N h) = (finiteHistoryInitial N h).1}) :
    binaryTestingConstant ≤ κ*∫ h, finiteHistoryCost (hiddenSelectedCost query target 1) N h
      ∂adaptiveKernelLaw ((PMF.uniformOfFintype Bool).toMeasure.prod μ)
        (hiddenDisclosureKernel query hq p) N := by
  have hs : MeasurableSet {h : FiniteHistory (Bool × S) A N |
      classify (finiteHistoryMapInitial Prod.snd N h) = (finiteHistoryInitial N h).1} :=
    measurableSet_eq_fun_of_countable
      (hc.comp (finiteHistoryMapInitial_measurable measurable_snd N))
      (measurable_fst.comp (finiteHistoryInitial_measurable N))
  have hlo := binary_testing_information_ennreal hs hsuccess
    (hidden_binary_classification_reference μ (measurableDisclosureKernel query hq q) N classify hc)
  have hup := hidden_selected_disclosure_information μ query hq p q target hsame hκ hKL N
  exact (ENNReal.ofReal_le_ofReal_iff'.mp (hlo.trans hup)).resolve_right
    (not_le_of_gt binaryTestingConstant_pos)

end
end SampleReuse
