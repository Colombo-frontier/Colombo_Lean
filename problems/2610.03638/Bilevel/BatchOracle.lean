import Bilevel.IndependentDraws

/-! An actual n-original-call sample mean, promoted to a fresh-seed oracle. -/
noncomputable section
open MeasureTheory
namespace Bilevel.BatchOracle

variable {Query Seed E : Type*} [MeasurableSpace Query] [MeasurableSpace Seed]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure Seed} [IsProbabilityMeasure ν] {σ : ℝ}
  (O : FreshOracle.Oracle (Query := Query) (E := E) ν σ)

open IndependentDraws

def sumSamples (q : Query) : (n : ℕ) → Draws Seed n → E
  | 0, _ => 0
  | n + 1, s => sumSamples q n s.1 + O.sample q s.2

def sumErrors (q : Query) : (n : ℕ) → Draws Seed n → E
  | 0, _ => 0
  | n + 1, s => sumErrors q n s.1 + O.error q s.2

def meanSample (n : ℕ) (q : Query) (s : Draws Seed n) : E :=
  (n : ℝ)⁻¹ • sumSamples O q n s

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure ν] in
theorem sumSamples_eq_run (q : Query) (n : ℕ) (s : Draws Seed n) :
    sumSamples O q n s = IndependentDraws.run (fun _ _ => q)
      (fun _ u observation => u + observation) O.sample (0 : E) n s := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumSamples, IndependentDraws.run, ih]

omit [CompleteSpace E] [IsProbabilityMeasure ν] in
theorem sumSamples_measurable (n : ℕ) :
    Measurable (fun qs : Query × Draws Seed n => sumSamples O qs.1 n qs.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
      (O.sample_measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

omit [CompleteSpace E] [IsProbabilityMeasure ν] in
theorem sumErrors_measurable (n : ℕ) :
    Measurable (fun qs : Query × Draws Seed n => sumErrors O qs.1 n qs.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
      (O.error_measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

omit [CompleteSpace E] in
theorem sumErrors_memLp (q : Query) (n : ℕ) : MemLp (sumErrors O q n) 2 (law ν n) := by
  induction n with
  | zero => exact memLp_const 0
  | succ n ih =>
    exact (ih.comp_measurePreserving (FreshOracle.Oracle.fst_preserves (ν := ν))).add
      (O.adaptiveError_memLp (μ := law ν n) (fun _ => q) measurable_const)

theorem sumErrors_mean (q : Query) (n : ℕ) : (∫ s, sumErrors O q n s ∂law ν n) = 0 := by
  induction n with
  | zero => simp [sumErrors]
  | succ n ih =>
    have hp : Integrable (fun s : Draws Seed n × Seed => sumErrors O q n s.1) ((law ν n).prod ν) :=
      ((sumErrors_memLp O q n).comp_measurePreserving (FreshOracle.Oracle.fst_preserves (ν := ν))).integrable (by norm_num)
    have he : Integrable (fun s : Draws Seed n × Seed => O.error q s.2) ((law ν n).prod ν) :=
      O.adaptiveError_integrable (μ := law ν n) (fun _ => q) measurable_const
    change (∫ s : Draws Seed n × Seed, sumErrors O q n s.1 + O.error q s.2 ∂(law ν n).prod ν) = 0
    rw [integral_add hp he]
    have hprod := integral_prod (fun s : Draws Seed n × Seed => sumErrors O q n s.1) hp
    have herr := integral_prod (fun s : Draws Seed n × Seed => O.error q s.2) he
    rw [hprod, herr]
    simp only [integral_const, measureReal_univ_eq_one, one_smul, FreshOracle.Oracle.error,
      O.mean, integral_zero, ih, zero_add]

theorem sumErrors_variance (q : Query) (n : ℕ) :
    (∫ s, ‖sumErrors O q n s‖ ^ 2 ∂law ν n) ≤ (n : ℝ) * σ ^ 2 := by
  induction n with
  | zero => simp [sumErrors]
  | succ n ih =>
    have h := O.update_risk_bound (μ := law ν n) (fun _ => q) measurable_const
      (sumErrors O q n) (sumErrors_memLp O q n) (-1)
    have hs : (∫ s, ‖sumErrors O q (n + 1) s‖ ^ 2 ∂law ν (n + 1)) ≤
        (∫ s, ‖sumErrors O q n s‖ ^ 2 ∂law ν n) + σ ^ 2 := by
      simpa only [sumErrors, law, FreshOracle.Oracle.adaptiveError, neg_smul, one_smul,
        sub_neg_eq_add, neg_one_sq, one_mul] using h
    push_cast
    nlinarith only [ih, hs]

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure ν] in
theorem sumSamples_signal (q : Query) (n : ℕ) (s : Draws Seed n) :
    sumSamples O q n s - (n : ℝ) • O.truth q = sumErrors O q n s := by
  induction n with
  | zero => simp [sumSamples, sumErrors]
  | succ n ih =>
    simp only [sumSamples, sumErrors, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    rw [← ih s.1]
    dsimp [FreshOracle.Oracle.error]
    module

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure ν] in
theorem meanSample_error (n : ℕ) (hn : 0 < n) (q : Query) (s : Draws Seed n) :
    meanSample O n q s - O.truth q = (n : ℝ)⁻¹ • sumErrors O q n s := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [← sumSamples_signal O q n s, smul_sub, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  rfl

theorem meanSample_variance (n : ℕ) (hn : 0 < n) (q : Query) :
    (∫ s, ‖meanSample O n q s - O.truth q‖ ^ 2 ∂law ν n) ≤ σ ^ 2 / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp_rw [meanSample_error O n hn, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul]
  calc
    _ ≤ ((n : ℝ)⁻¹) ^ 2 * ((n : ℝ) * σ ^ 2) :=
      mul_le_mul_of_nonneg_left (sumErrors_variance O q n) (sq_nonneg _)
    _ = _ := by field_simp; ring

/-- The new seed consists of exactly n fresh original seeds. Every mean,
variance and measurability field is proved from the pointwise original SFO. -/
def oracle (n : ℕ) (hn : 0 < n) :
    FreshOracle.Oracle (Query := Query) (E := E) (law ν n) (σ / Real.sqrt n) where
  truth := O.truth
  sample := meanSample O n
  truth_measurable := O.truth_measurable
  sample_measurable := (sumSamples_measurable O n).const_smul ((n : ℝ)⁻¹)
  square_integrable q := by
    have hm : MemLp (fun s => meanSample O n q s - O.truth q) 2 (law ν n) := by
      simpa only [meanSample_error O n hn] using (sumErrors_memLp O q n).const_smul ((n : ℝ)⁻¹)
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  mean q := by simp_rw [meanSample_error O n hn]; rw [integral_smul, sumErrors_mean, smul_zero]
  variance q := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    exact meanSample_variance O n hn q

end Bilevel.BatchOracle
