import SecondOrder.KernelEntropyChain
import SecondOrder.FiniteSeedProbability

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical

universe u
namespace SecondOrder
noncomputable section
variable {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]

/-- The actual law of an arbitrary initial state followed by adaptive kernel
responses. `FiniteHistory` refers to the horizon, not finite response support. -/
def adaptiveKernelLaw (μ : Measure S) (K : ∀ n, Kernel (FiniteHistory S A n) A) :
    (n : ℕ) → Measure (FiniteHistory S A n)
  | 0 => μ
  | n+1 => adaptiveKernelLaw μ K n ⊗ₘ K n

instance adaptiveKernelLaw_probability (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)] :
    (n : ℕ) → IsProbabilityMeasure (adaptiveKernelLaw μ K n)
  | 0 => inferInstanceAs (IsProbabilityMeasure μ)
  | n+1 => by
    letI := adaptiveKernelLaw_probability μ K n
    exact inferInstanceAs (IsProbabilityMeasure (adaptiveKernelLaw μ K n ⊗ₘ K n))

theorem finiteHistoryCost_measurable (c : ∀ n, FiniteHistory S A n → ℝ)
    (hc : ∀ n, Measurable (c n)) : ∀ n, Measurable (finiteHistoryCost c n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add ((hc n).comp measurable_fst)

theorem finiteHistoryCost_le (c : ∀ n, FiniteHistory S A n → ℝ) {C : ℝ}
    (hc : ∀ n h, c n h ≤ C) : ∀ n h, finiteHistoryCost c n h ≤ n*C := by
  intro n
  induction n with
  | zero => intro h; simp only [finiteHistoryCost,Nat.cast_zero,zero_mul,le_refl]
  | succ n ih =>
    intro h
    change finiteHistoryCost c n h.1+c n h.1 ≤ (n+1:ℕ)*C
    calc
      _ ≤ (n:ℝ)*C+C := add_le_add (ih _) (hc n _)
      _ = _ := by push_cast; ring

theorem adaptiveHistoryCost_nonneg (c : ∀ n, FiniteHistory S A n → ℝ)
    (hc : ∀ n h, 0 ≤ c n h) : ∀ n h, 0 ≤ finiteHistoryCost c n h := by
  intro n
  induction n with
  | zero => intro h; exact le_rfl
  | succ n ih => intro h; exact add_nonneg (ih h.1) (hc n h.1)

theorem finiteHistoryCost_integrable (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (c : ∀ n, FiniteHistory S A n → ℝ) (hm : ∀ n, Measurable (c n))
    {C : ℝ} (hc : ∀ n h, 0 ≤ c n h ∧ c n h ≤ C) (n : ℕ) :
    Integrable (finiteHistoryCost c n) (adaptiveKernelLaw μ K n) := by
  apply (integrable_const ((n:ℝ)*C)).mono' (finiteHistoryCost_measurable c hm n).aestronglyMeasurable
  filter_upwards [] with h
  rw [Real.norm_of_nonneg (adaptiveHistoryCost_nonneg c (fun n h => (hc n h).1) n h)]
  exact finiteHistoryCost_le c (fun n h => (hc n h).2) n h

theorem integral_compProd_fst_real {B : Type*} [MeasurableSpace B]
    (μ : Measure S) [IsProbabilityMeasure μ] (K : Kernel S B) [IsMarkovKernel K]
    {f : S → ℝ} (hm : Measurable f) (hi : Integrable f μ) :
    (∫ z, f z.1 ∂μ ⊗ₘ K) = ∫ s, f s ∂μ := by
  have hprod : Integrable (fun z : S × B => f z.1) (μ ⊗ₘ K) := by
    apply (Measure.integrable_compProd_iff (hm.comp measurable_fst).aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun s => ?_), ?_⟩
    · exact integrable_const (f s)
    · simpa using hi.norm
  rw [Measure.integral_compProd hprod]
  simp

theorem adaptiveKernelLaw_cost_succ (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (c : ∀ n, FiniteHistory S A n → ℝ) (hm : ∀ n, Measurable (c n))
    {C : ℝ} (hc : ∀ n h, 0 ≤ c n h ∧ c n h ≤ C) (n : ℕ) :
    (∫ h, finiteHistoryCost c (n+1) h ∂adaptiveKernelLaw μ K (n+1)) =
      (∫ h, finiteHistoryCost c n h ∂adaptiveKernelLaw μ K n)+
      ∫ h, c n h ∂adaptiveKernelLaw μ K n := by
  have hi : Integrable (c n) (adaptiveKernelLaw μ K n) := by
    apply (integrable_const C).mono' (hm n).aestronglyMeasurable
    filter_upwards [] with h
    rw [Real.norm_of_nonneg (hc n h).1]
    exact (hc n h).2
  change (∫ h, (finiteHistoryCost c n h.1+c n h.1) ∂(adaptiveKernelLaw μ K n ⊗ₘ K n)) = _
  rw [integral_compProd_fst_real (adaptiveKernelLaw μ K n) (K n)
    ((finiteHistoryCost_measurable c hm n).add (hm n))
    ((finiteHistoryCost_integrable μ K c hm hc n).add hi),
    integral_add (finiteHistoryCost_integrable μ K c hm hc n) hi]

variable [MeasurableSpace.CountablyGenerated A]

/-- The adaptive information budget is the expected realized predictable
charge. It is not replaced by the horizon times the largest charge. -/
theorem adaptiveKernelLaw_kl_le (μ : Measure S) [IsProbabilityMeasure μ]
    (K Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (c : ∀ n, FiniteHistory S A n → ℝ) (hm : ∀ n, Measurable (c n))
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ n h, 0 ≤ c n h ∧ c n h ≤ C)
    (hKL : ∀ n h, klDiv (K n h) (Q n h) ≤ ENNReal.ofReal (c n h)) :
    ∀ n, klDiv (adaptiveKernelLaw μ K n) (adaptiveKernelLaw μ Q n) ≤
      ENNReal.ofReal (∫ h, finiteHistoryCost c n h ∂adaptiveKernelLaw μ K n) := by
  intro n
  induction n with
  | zero => simp only [adaptiveKernelLaw,klDiv_self,finiteHistoryCost,integral_zero,ENNReal.ofReal_zero,le_refl]
  | succ n ih =>
    have hfin : klDiv (adaptiveKernelLaw μ K n) (adaptiveKernelLaw μ Q n) ≠ ∞ :=
      (lt_of_le_of_lt ih ENNReal.ofReal_lt_top).ne
    have hbound (h : FiniteHistory S A n) : klDiv (K n h) (Q n h) ≤ ENNReal.ofReal C :=
      (hKL n h).trans (ENNReal.ofReal_le_ofReal (hc n h).2)
    have hi : Integrable (c n) (adaptiveKernelLaw μ K n) := by
      apply (integrable_const C).mono' (hm n).aestronglyMeasurable
      filter_upwards [] with h
      rw [Real.norm_of_nonneg (hc n h).1]
      exact (hc n h).2
    have hcost : (∫ h, (klDiv (K n h) (Q n h)).toReal ∂adaptiveKernelLaw μ K n) ≤
        ∫ h, c n h ∂adaptiveKernelLaw μ K n :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) hi
        (Filter.Eventually.of_forall (fun h => ENNReal.toReal_le_of_le_ofReal (hc n h).1 (hKL n h)))
    change klDiv (adaptiveKernelLaw μ K n ⊗ₘ K n) (adaptiveKernelLaw μ Q n ⊗ₘ Q n) ≤ _
    rw [klDiv_compProd_chain hfin hC hbound,adaptiveKernelLaw_cost_succ μ K c hm hc n,
      ENNReal.ofReal_add
        (integral_nonneg (adaptiveHistoryCost_nonneg c (fun n h => (hc n h).1) n))
        (integral_nonneg (fun h => (hc n h).1))]
    exact add_le_add ih (ENNReal.ofReal_le_ofReal hcost)

theorem adaptiveKernelLaw_kl_of_cap (μ : Measure S) [IsProbabilityMeasure μ]
    (K Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (c : ∀ n, FiniteHistory S A n → ℝ) (hm : ∀ n, Measurable (c n))
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ n h, 0 ≤ c n h ∧ c n h ≤ C)
    (hKL : ∀ n h, klDiv (K n h) (Q n h) ≤ ENNReal.ofReal (c n h))
    (n : ℕ) {B : ℝ} (hcap : ∀ h, finiteHistoryCost c n h ≤ B) :
    klDiv (adaptiveKernelLaw μ K n) (adaptiveKernelLaw μ Q n) ≤ ENNReal.ofReal B := by
  apply (adaptiveKernelLaw_kl_le μ K Q c hm hC hc hKL n).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ _ : FiniteHistory S A n, B ∂adaptiveKernelLaw μ K n :=
      integral_mono (finiteHistoryCost_integrable μ K c hm hc n) (integrable_const _) hcap
    _ = B := by simp

end
end SecondOrder
