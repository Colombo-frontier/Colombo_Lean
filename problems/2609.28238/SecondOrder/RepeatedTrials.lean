import SecondOrder.ContinuousBatch
import SecondOrder.RobustMeasurability

open MeasureTheory Filter
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

def drawsVector {Ω E : Type*} (X : Ω → E) : (n : ℕ) → Draws Ω n → Fin n → E
  | 0, _ => Fin.elim0
  | n+1, w => Fin.snoc (drawsVector X n w.1) (X w.2)

theorem drawsVector_measurable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {X : Ω → E} (hX : Measurable X) (n : ℕ) : Measurable (drawsVector X n) := by
  induction n with
  | zero => exact measurable_pi_lambda _ (fun i => Fin.elim0 i)
  | succ n ih =>
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [drawsVector, Fin.snoc_last] using hX.comp measurable_snd
    · simpa only [drawsVector, Fin.snoc_castSucc] using ((measurable_pi_apply j).comp ih).comp measurable_fst

theorem drawsVector_apply {Ω E : Type*} (X : Ω → E) (n : ℕ)
    (w : Draws Ω n) (i : Fin n) : drawsVector X n w i = X (drawsVector id n w i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [drawsVector]
    · simpa only [drawsVector, Fin.snoc_castSucc] using ih w.1 j

def drawsCount {Ω : Type*} (B : Set Ω) : (n : ℕ) → Draws Ω n → ℕ
  | 0, _ => 0
  | n+1, w => drawsCount B n w.1+if w.2 ∈ B then 1 else 0

theorem drawsCount_eq_card {Ω : Type*} (B : Set Ω) (n : ℕ) (w : Draws Ω n) :
    drawsCount B n w = (Finset.univ.filter (fun i => drawsVector id n w i ∈ B)).card := by
  induction n with
  | zero => simp [drawsCount]
  | succ n ih =>
    simp only [drawsCount, drawsVector, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, id_eq]
    rw [ih]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem drawsCount_compl {Ω : Type*} (B : Set Ω) (n : ℕ) (w : Draws Ω n) :
    drawsCount B n w+drawsCount Bᶜ n w = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [drawsCount, Set.mem_compl_iff]
    have hh := ih w.1
    split_ifs <;> omega

def trialWeight {Ω : Type*} (B : Set Ω) (z : Ω) : ℝ := if z ∈ B then 4 else 1

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : Set Ω}

theorem trialWeight_integrable (hB : MeasurableSet B) : Integrable (trialWeight B) μ :=
  Integrable.piecewise hB (integrable_const (4 : ℝ)) (integrable_const (1 : ℝ))

theorem trialWeight_integral (hB : MeasurableSet B) :
    (∫ z, trialWeight B z ∂μ) = 1+3*μ.real B := by
  have he : trialWeight B = fun z => 1+3*B.indicator (fun _ => (1:ℝ)) z := by
    funext z
    by_cases hz : z ∈ B <;> norm_num [trialWeight, hz]
  rw [he, integral_add (integrable_const _) (((integrable_const (1:ℝ)).indicator hB).const_mul 3),
    integral_const_mul, integral_indicator_const (1 : ℝ) hB]
  simp

theorem drawsCount_exp_succ (n : ℕ) (w : Draws Ω (n+1)) :
    (4 : ℝ)^drawsCount B (n+1) w = (4 : ℝ)^drawsCount B n w.1*trialWeight B w.2 := by
  simp only [drawsCount, pow_add, trialWeight]
  split_ifs <;> simp

theorem drawsCount_exp_integrable (hB : MeasurableSet B) (n : ℕ) :
    Integrable (fun w => (4 : ℝ)^drawsCount B n w) (drawsLaw μ n) := by
  induction n with
  | zero => simpa [drawsCount] using (integrable_const (μ := drawsLaw μ 0) (1:ℝ))
  | succ n ih =>
    simpa only [drawsCount_exp_succ] using ih.mul_prod (trialWeight_integrable (μ := μ) hB)

theorem drawsCount_exp_integral (hB : MeasurableSet B) (n : ℕ) :
    (∫ w, (4 : ℝ)^drawsCount B n w ∂drawsLaw μ n) = (1+3*μ.real B)^n := by
  induction n with
  | zero => simp [drawsCount]
  | succ n ih =>
    simp only [drawsCount_exp_succ]
    change (∫ w : Draws Ω n × Ω, (4 : ℝ)^drawsCount B n w.1*trialWeight B w.2
      ∂(drawsLaw μ n).prod μ) = _
    calc
      _ = (∫ w, (4 : ℝ)^drawsCount B n w ∂drawsLaw μ n)*(∫ z, trialWeight B z ∂μ) :=
        integral_prod_mul _ _
      _ = _ := by rw [ih, trialWeight_integral hB, pow_succ]

/-- An explicit exponential majority bound. The proof integrates the
exponential of the bad-draw count over the fresh product law. -/
theorem drawsCount_majority_probability (hB : MeasurableSet B)
    (hp : μ B ≤ ENNReal.ofReal (1/4 : ℝ)) (n : ℕ) :
    drawsLaw μ n {w | n ≤ 2*drawsCount B n w} ≤ ENNReal.ofReal ((7/8 : ℝ)^n) := by
  have hpR : μ.real B ≤ (1/4 : ℝ) := by
    have := ENNReal.toReal_mono (by finiteness) hp
    simpa using this
  have htwo : 0 < (2:ℝ)^n := pow_pos (by norm_num) n
  have hm := ((drawsCount_exp_integrable (μ := μ) hB n).div_const ((2:ℝ)^n)).measure_le_integral
    (Eventually.of_forall (fun w => div_nonneg (by positivity) htwo.le))
    (s := {w | n ≤ 2*drawsCount B n w}) (fun w hw => by
      apply (le_div_iff₀ htwo).mpr
      rw [one_mul]
      have ht := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hw
      simpa only [pow_mul, show (2:ℝ)^2 = 4 by norm_num] using ht)
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div, drawsCount_exp_integral hB]
  calc
    _ ≤ (7/4 : ℝ)^n/(2:ℝ)^n := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith) n) htwo.le
    _ = (7/8 : ℝ)^n := by rw [← div_pow]; norm_num

/-- Exponential confidence amplification for arbitrary measurable iid
observations. The output is the concrete Borel selector above. -/
theorem repeated_robustCenter_failure {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {X : Ω → E} (hX : Measurable X) (a : E) (r : ℝ) {R : ℕ} (hR : 0 < R)
    (hp : μ {z | r < dist (X z) a} ≤ ENNReal.ofReal (1/4 : ℝ)) :
    drawsLaw μ R {w | 3*r < dist (robustCenter hR (drawsVector X R w) r) a} ≤
      ENNReal.ofReal ((7/8 : ℝ)^R) := by
  let B : Set Ω := {z | r < dist (X z) a}
  have hB : MeasurableSet B := measurableSet_lt measurable_const (hX.dist measurable_const)
  apply (measure_mono (t := {w | R ≤ 2*drawsCount B R w}) ?_).trans
    (drawsCount_majority_probability hB hp R)
  intro w hw
  by_contra hn
  change ¬ R ≤ 2*drawsCount B R w at hn
  have hc := drawsCount_compl B R w
  have he : (goodObservations (drawsVector X R w) a r).card = drawsCount Bᶜ R w := by
    rw [drawsCount_eq_card]
    congr 1
    ext i
    simp only [goodObservations, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_compl_iff, B, Set.mem_setOf_eq, not_lt, drawsVector_apply X]
  have hg : R < 2*(goodObservations (drawsVector X R w) a r).card := by rw [he]; omega
  exact (not_lt_of_ge (robustCenter_close hR (drawsVector X R w) a r hg)) hw

end
end SecondOrder
