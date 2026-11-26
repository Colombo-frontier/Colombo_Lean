import SecondOrder.AdaptiveKernelLaw

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical

universe u
namespace SecondOrder
noncomputable section
variable {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]

/-- Count selected responses, stopping the count at the deterministic cap. -/
def kernelChargeCount (selected : ∀ n, FiniteHistory S A n → Prop) (cap : ℕ) :
    (n : ℕ) → FiniteHistory S A n → ℕ
  | 0, _ => 0
  | n+1, h => if kernelChargeCount selected cap n h.1<cap ∧ selected n h.1
      then kernelChargeCount selected cap n h.1+1 else kernelChargeCount selected cap n h.1

theorem kernelChargeCount_le (selected : ∀ n, FiniteHistory S A n → Prop) (cap : ℕ) :
    ∀ n h, kernelChargeCount selected cap n h ≤ cap := by
  intro n
  induction n with
  | zero => intro h; exact Nat.zero_le _
  | succ n ih =>
    intro h
    unfold kernelChargeCount
    split_ifs with hp
    · omega
    · exact ih h.1

theorem kernelChargeCount_measurable (selected : ∀ n, FiniteHistory S A n → Prop)
    (hs : ∀ n, MeasurableSet {h | selected n h}) (cap : ℕ) :
    ∀ n, Measurable (kernelChargeCount selected cap n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measurable.ite
      ((measurableSet_lt (ih.comp measurable_fst) measurable_const).inter
        ((hs n).preimage measurable_fst))
      ((ih.comp measurable_fst).add_const 1) (ih.comp measurable_fst)

def kernelStepCharge (selected : ∀ n, FiniteHistory S A n → Prop) (cap : ℕ) (κ : ℝ)
    (n : ℕ) (h : FiniteHistory S A n) : ℝ :=
  if kernelChargeCount selected cap n h<cap ∧ selected n h then κ else 0

theorem kernelStepCharge_measurable (selected : ∀ n, FiniteHistory S A n → Prop)
    (hs : ∀ n, MeasurableSet {h | selected n h}) (cap : ℕ) (κ : ℝ) (n : ℕ) :
    Measurable (kernelStepCharge selected cap κ n) :=
  Measurable.ite ((measurableSet_lt (kernelChargeCount_measurable selected hs cap n)
    measurable_const).inter (hs n)) measurable_const measurable_const

theorem kernelStepCharge_bounds (selected : ∀ n, FiniteHistory S A n → Prop)
    (cap : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) (h : FiniteHistory S A n) :
    0 ≤ kernelStepCharge selected cap κ n h ∧ kernelStepCharge selected cap κ n h ≤ κ := by
  unfold kernelStepCharge
  split_ifs <;> exact ⟨by positivity, by first | exact le_rfl | exact hκ⟩

theorem kernelStepCharge_total (selected : ∀ n, FiniteHistory S A n → Prop)
    (cap : ℕ) (κ : ℝ) : ∀ n h,
    finiteHistoryCost (kernelStepCharge selected cap κ) n h = κ*kernelChargeCount selected cap n h := by
  intro n
  induction n with
  | zero => intro h; simp only [finiteHistoryCost,kernelChargeCount,Nat.cast_zero,mul_zero]
  | succ n ih =>
    intro h
    simp only [finiteHistoryCost,kernelStepCharge,kernelChargeCount,ih h.1]
    split_ifs <;> push_cast <;> ring

/-- After the last allowed selected response, both experiments use the same
dummy kernel. Before that, all adaptive query dependence is retained. -/
def cappedResponseKernel (selected : ∀ n, FiniteHistory S A n → Prop)
    (hs : ∀ n, MeasurableSet {h | selected n h}) (cap : ℕ)
    (K dummy : ∀ n, Kernel (FiniteHistory S A n) A) (n : ℕ) : Kernel (FiniteHistory S A n) A :=
  Kernel.piecewise (measurableSet_lt (kernelChargeCount_measurable selected hs cap n)
    (measurable_const (a := cap))) (K n) (dummy n)

instance cappedResponseKernel_markov (selected : ∀ n, FiniteHistory S A n → Prop)
    (hs : ∀ n, MeasurableSet {h | selected n h}) (cap : ℕ)
    (K dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (dummy n)] (n : ℕ) :
    IsMarkovKernel (cappedResponseKernel selected hs cap K dummy n) := by
  unfold cappedResponseKernel
  infer_instance

theorem cappedResponseKernel_kl (selected : ∀ n, FiniteHistory S A n → Prop)
    (hs : ∀ n, MeasurableSet {h | selected n h}) (cap : ℕ)
    (K Q dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)] [∀ n, IsMarkovKernel (dummy n)]
    {κ : ℝ} (hKL : ∀ n h, klDiv (K n h) (Q n h) ≤ ENNReal.ofReal κ)
    (hsame : ∀ n h, ¬ selected n h → K n h=Q n h) (n : ℕ) (h : FiniteHistory S A n) :
    klDiv (cappedResponseKernel selected hs cap K dummy n h)
      (cappedResponseKernel selected hs cap Q dummy n h) ≤
      ENNReal.ofReal (kernelStepCharge selected cap κ n h) := by
  by_cases hb : kernelChargeCount selected cap n h<cap
  · by_cases ha : selected n h
    · simpa only [cappedResponseKernel,Kernel.piecewise_apply,Set.mem_setOf_eq,if_pos hb,
        kernelStepCharge,hb,and_self,ha,if_true] using hKL n h
    · simp only [cappedResponseKernel,Kernel.piecewise_apply,Set.mem_setOf_eq,if_pos hb,
        kernelStepCharge,ha,and_false,if_false,hsame n h ha,klDiv_self,ENNReal.ofReal_zero,le_refl]
  · simp only [cappedResponseKernel,Kernel.piecewise_apply,Set.mem_setOf_eq,if_neg hb,
      kernelStepCharge,hb,false_and,if_false,klDiv_self,ENNReal.ofReal_zero,le_refl]

/-- The actual adaptive continuation has KL at most cap*κ, regardless of
the horizon and regardless of the locations of the selected responses. -/
theorem cappedAdaptiveKernelLaw_kl (μ : Measure S) [IsProbabilityMeasure μ]
    [MeasurableSpace.CountablyGenerated A]
    (selected : ∀ n, FiniteHistory S A n → Prop) (hs : ∀ n, MeasurableSet {h | selected n h})
    (cap : ℕ) (K Q dummy : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)] [∀ n, IsMarkovKernel (dummy n)]
    {κ : ℝ} (hκ : 0 ≤ κ) (hKL : ∀ n h, klDiv (K n h) (Q n h) ≤ ENNReal.ofReal κ)
    (hsame : ∀ n h, ¬ selected n h → K n h=Q n h) (N : ℕ) :
    klDiv (adaptiveKernelLaw μ (cappedResponseKernel selected hs cap K dummy) N)
      (adaptiveKernelLaw μ (cappedResponseKernel selected hs cap Q dummy) N) ≤
      ENNReal.ofReal ((cap:ℝ)*κ) := by
  apply adaptiveKernelLaw_kl_of_cap μ _ _ (kernelStepCharge selected cap κ)
    (kernelStepCharge_measurable selected hs cap κ) hκ (kernelStepCharge_bounds selected cap hκ)
    (cappedResponseKernel_kl selected hs cap K Q dummy hKL hsame) N
  intro h
  rw [kernelStepCharge_total]
  calc
    _ ≤ κ*(cap:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast kernelChargeCount_le selected cap N h) hκ
    _ = (cap:ℝ)*κ := mul_comm _ _

end
end SecondOrder
