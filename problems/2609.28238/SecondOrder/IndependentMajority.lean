import SecondOrder.RepeatedTrials
import Mathlib.Probability.Integration

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A finite product of independent real random variables; their laws may differ. -/
theorem independent_finiteProduct_integral {X : ι → Ω → ℝ}
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (hx : ∀ i, Integrable (X i) μ)
    (s : Finset ι) :
    Integrable (fun w => ∏ i ∈ s, X i w) μ ∧
      (∫ w, ∏ i ∈ s, X i w ∂μ)=∏ i ∈ s, ∫ w, X i w ∂μ := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨integrable_const _,by simp⟩
  | cons i s his ih =>
    have hind := (hi.indepFun_finset_prod_of_not_mem hm his).symm
    have he : (∏ j ∈ s, X j)=(fun w => ∏ j ∈ s, X j w) := by
      funext w
      simp only [Finset.prod_apply]
    rw [he] at hind
    simp only [Finset.prod_cons]
    refine ⟨hind.integrable_mul (hx i) ih.1,?_⟩
    have hh := hind.integral_mul_of_integrable (hx i) ih.1
    change (∫ w, X i w*(∏ j ∈ s, X j w) ∂μ)=_ at hh
    rw [hh,ih.2]

def eventCount [Fintype ι] (B : ι → Set Ω) (w : Ω) : ℕ :=
  (Finset.univ.filter (fun i => w ∈ B i)).card

theorem eventCount_measurable [Fintype ι] {B : ι → Set Ω}
    (hB : ∀ i, MeasurableSet (B i)) : Measurable (eventCount B) := by
  unfold eventCount
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.measurable_sum _ (fun i _ => Measurable.ite (hB i) measurable_const measurable_const)

theorem trialWeight_product [Fintype ι] (B : ι → Set Ω) (w : Ω) :
    (∏ i, trialWeight (B i) w)=(4:ℝ)^eventCount B w := by
  simp [trialWeight,Finset.prod_ite,eventCount]

/-- Independence alone gives the same exponential majority bound as iid
sampling. Each bad event may have its own probability below one quarter. -/
theorem independent_eventCount_majority [Fintype ι] {B : ι → Set Ω}
    (hB : ∀ i, MeasurableSet (B i))
    (hi : iIndepFun (fun i => trialWeight (B i)) μ)
    (hp : ∀ i, μ (B i)≤ENNReal.ofReal (1/4:ℝ)) :
    μ {w | Fintype.card ι≤2*eventCount B w}≤ENNReal.ofReal ((7/8:ℝ)^Fintype.card ι) := by
  have hm : ∀ i, Measurable (trialWeight (B i)) :=
    fun i => Measurable.ite (hB i) measurable_const measurable_const
  have hpR : ∀ i, μ.real (B i)≤(1/4:ℝ) := by
    intro i
    have hh := ENNReal.toReal_mono (by finiteness) (hp i)
    simpa using hh
  have hprod := independent_finiteProduct_integral hi hm
    (fun i => trialWeight_integrable (hB i)) Finset.univ
  have htwo : 0<(2:ℝ)^Fintype.card ι := pow_pos (by norm_num) _
  have hbound := (hprod.1.div_const ((2:ℝ)^Fintype.card ι)).measure_le_integral
    (Eventually.of_forall (fun w => div_nonneg
      (Finset.prod_nonneg (fun i _ => by unfold trialWeight; split_ifs <;> norm_num)) htwo.le))
    (s := {w | Fintype.card ι≤2*eventCount B w}) (fun w hw => by
      apply (le_div_iff₀ htwo).mpr
      rw [one_mul,trialWeight_product]
      have ht := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hw
      simpa only [pow_mul,show (2:ℝ)^2=4 by norm_num] using ht)
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div,hprod.2]
  calc
    _ ≤ (∏ _ : ι, (7/4:ℝ))/(2:ℝ)^Fintype.card ι := by
      apply div_le_div_of_nonneg_right _ htwo.le
      apply Finset.prod_le_prod
      · intro i _
        rw [trialWeight_integral (hB i)]
        positivity
      · intro i _
        rw [trialWeight_integral (hB i)]
        linarith [hpR i]
    _ = (7/8:ℝ)^Fintype.card ι := by simp only [Finset.prod_const,Finset.card_univ,←div_pow]; norm_num

end
end SecondOrder
