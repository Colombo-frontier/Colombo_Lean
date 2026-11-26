import HeavyTail.AdaptiveKernelExecution
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Product concentration directly on the actual finite adaptive execution.
The only probabilistic input is a one-step integral against the actual reply
kernel. All path integrability and product moment estimates are derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace HeavyTail.AdaptiveKernel
universe u v w
variable {Seed Reply : Type u} {Query : Type v} {Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace Reply] [MeasurableSpace Query] [MeasurableSpace Output]

def historyProduct (F : (n : ℕ) → History Seed Reply n × Reply → ℝ) :
    (n : ℕ) → History Seed Reply n → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun h => historyProduct F n h.1 * F n h

def historySum (F : (n : ℕ) → History Seed Reply n × Reply → ℝ) :
    (n : ℕ) → History Seed Reply n → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun h => historySum F n h.1 + F n h

theorem historyProduct_measurable {F : (n : ℕ) → History Seed Reply n × Reply → ℝ}
    (hF : ∀ n, Measurable (F n)) (n : ℕ) : Measurable (historyProduct F n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).mul (hF n)

theorem historySum_measurable {F : (n : ℕ) → History Seed Reply n × Reply → ℝ}
    (hF : ∀ n, Measurable (F n)) (n : ℕ) : Measurable (historySum F n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).add (hF n)

theorem historySum_mono {F G : (n : ℕ) → History Seed Reply n × Reply → ℝ}
    (hFG : ∀ n h, F n h ≤ G n h) (n : ℕ) (h : History Seed Reply n) :
    historySum F n h ≤ historySum G n h := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact add_le_add (ih h.1) (hFG n h)

theorem historySum_add (F G : (n : ℕ) → History Seed Reply n × Reply → ℝ)
    (n : ℕ) (h : History Seed Reply n) :
    historySum (fun t h => F t h + G t h) n h = historySum F n h + historySum G n h := by
  induction n with
  | zero => simp [historySum]
  | succ n ih =>
      simp only [historySum, ih]
      ring

theorem historySum_const (C : ℝ) (n : ℕ) (h : History Seed Reply n) :
    historySum (fun _ _ => C) n h = n * C := by
  induction n with
  | zero => simp [historySum]
  | succ n ih =>
      simp only [historySum, ih, Nat.cast_add, Nat.cast_one]
      ring

theorem historyProduct_nonneg {F : (n : ℕ) → History Seed Reply n × Reply → ℝ}
    (hF : ∀ n h, 0 ≤ F n h) (n : ℕ) (h : History Seed Reply n) :
    0 ≤ historyProduct F n h := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (ih h.1) (hF n h)

theorem historyProduct_pos {F : (n : ℕ) → History Seed Reply n × Reply → ℝ}
    (hF : ∀ n h, 0 < F n h) (n : ℕ) (h : History Seed Reply n) :
    0 < historyProduct F n h := by
  induction n with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (ih h.1) (hF n h)

theorem historyProduct_le {F : (n : ℕ) → History Seed Reply n × Reply → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hF : ∀ n h, 0 ≤ F n h) (hb : ∀ n h, F n h ≤ B)
    (n : ℕ) (h : History Seed Reply n) : historyProduct F n h ≤ B ^ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (mul_le_mul (ih h.1) (hb n h) (hF n h) (pow_nonneg hB n)).trans_eq (pow_succ B n).symm

theorem historyProduct_integrable {T : ℕ} (A : Policy Seed Query Reply Output T)
    (P : Measure Seed) [IsProbabilityMeasure P] (K : Kernel Query Reply) [IsMarkovKernel K]
    {F : (n : ℕ) → History Seed Reply n × Reply → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hm : ∀ n, Measurable (F n))
    (hF : ∀ n h, 0 ≤ F n h) (hb : ∀ n h, F n h ≤ B) (n : ℕ) :
    Integrable (historyProduct F n) (A.historyLaw P K n) := by
  apply (integrable_const (B ^ n)).mono' (historyProduct_measurable hm n).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun h => by
    rw [Real.norm_eq_abs, abs_of_nonneg (historyProduct_nonneg hF n h)]
    exact historyProduct_le hB hF hb n h

theorem historyProduct_integral_le {T : ℕ} (A : Policy Seed Query Reply Output T)
    (P : Measure Seed) [IsProbabilityMeasure P] (K : Kernel Query Reply) [IsMarkovKernel K]
    {F : (n : ℕ) → History Seed Reply n × Reply → ℝ} {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hm : ∀ n, Measurable (F n))
    (hF : ∀ n h, 0 ≤ F n h) (hb : ∀ n h, F n h ≤ B)
    (hstep : ∀ n h, (∫ r, F n (h, r) ∂K (A.query n h)) ≤ C) (n : ℕ) :
    (∫ h, historyProduct F n h ∂A.historyLaw P K n) ≤ C ^ n := by
  induction n with
  | zero => simp [historyProduct, Policy.historyLaw_zero]
  | succ n ih =>
      have hip := historyProduct_integrable A P K hB hm hF hb (n + 1)
      rw [Policy.historyLaw_succ] at hip ⊢
      change (∫ h : History Seed Reply n × Reply, historyProduct F (n + 1) h
        ∂(A.historyLaw P K n).compProd (A.replyKernel K n)) ≤ C ^ (n + 1)
      rw [Measure.integral_compProd hip]
      simp only [historyProduct, integral_const_mul, Policy.replyKernel_apply]
      have hi := historyProduct_integrable A P K hB hm hF hb n
      have hil := hip.integral_compProd
      simp only [Kernel.prodMkLeft_apply, Kernel.const_apply, historyProduct,
        integral_const_mul, Policy.replyKernel_apply] at hil
      calc
        _ ≤ ∫ h, historyProduct F n h * C ∂A.historyLaw P K n := by
          apply integral_mono hil (hi.mul_const C)
          intro h
          exact mul_le_mul_of_nonneg_left (hstep n h) (historyProduct_nonneg hF n h)
        _ = (∫ h, historyProduct F n h ∂A.historyLaw P K n) * C := integral_mul_const _ _
        _ ≤ C ^ n * C := mul_le_mul_of_nonneg_right ih hC
        _ = C ^ (n + 1) := (pow_succ C n).symm

theorem historyProduct_tail {T : ℕ} (A : Policy Seed Query Reply Output T)
    (P : Measure Seed) [IsProbabilityMeasure P] (K : Kernel Query Reply) [IsMarkovKernel K]
    {F : (n : ℕ) → History Seed Reply n × Reply → ℝ} {B C δ : ℝ}
    (hB : 0 ≤ B) (hC : 0 < C) (hδ : 0 < δ) (hm : ∀ n, Measurable (F n))
    (hF : ∀ n h, 0 ≤ F n h) (hb : ∀ n h, F n h ≤ B)
    (hstep : ∀ n h, (∫ r, F n (h, r) ∂K (A.query n h)) ≤ C) (n : ℕ) :
    (A.historyLaw P K n).real {h | C ^ n / δ ≤ historyProduct F n h} ≤ δ := by
  have hi := historyProduct_integrable A P K hB hm hF hb n
  have he := historyProduct_integral_le A P K hB hC.le hm hF hb hstep n
  have ht := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (historyProduct_nonneg hF n)) hi (C ^ n / δ)
  have hpos : 0 < C ^ n / δ := div_pos (pow_pos hC n) hδ
  have hid : C ^ n / δ * δ = C ^ n := div_mul_cancel₀ _ hδ.ne'
  nlinarith only [he, ht, hpos, hid]

theorem historyProduct_exp (F : (n : ℕ) → History Seed Reply n × Reply → ℝ)
    (n : ℕ) (h : History Seed Reply n) :
    historyProduct (fun n h => Real.exp (F n h)) n h = Real.exp (historySum F n h) := by
  induction n with
  | zero => simp [historyProduct, historySum]
  | succ n ih => simp only [historyProduct, historySum, ih, Real.exp_add]

theorem historyProduct_log {F : (n : ℕ) → History Seed Reply n × Reply → ℝ}
    (hF : ∀ n h, 0 < F n h) (n : ℕ) (h : History Seed Reply n) :
    Real.log (historyProduct F n h) = historySum (fun n h => Real.log (F n h)) n h := by
  induction n with
  | zero => simp [historyProduct, historySum]
  | succ n ih =>
      rw [historyProduct, Real.log_mul (historyProduct_pos hF n h.1).ne' (hF n h).ne',
        ih, historySum]

theorem history_log_sum_tail {T : ℕ} (A : Policy Seed Query Reply Output T)
    (P : Measure Seed) [IsProbabilityMeasure P] (K : Kernel Query Reply) [IsMarkovKernel K]
    {F : (n : ℕ) → History Seed Reply n × Reply → ℝ} {B ν δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 < δ) (hm : ∀ n, Measurable (F n))
    (hF : ∀ n h, 0 < F n h) (hb : ∀ n h, F n h ≤ B)
    (hstep : ∀ n h, (∫ r, F n (h, r) ∂K (A.query n h)) ≤ Real.exp ν) (n : ℕ) :
    (A.historyLaw P K n).real {h | (n : ℝ) * ν + Real.log (1 / δ) <
      historySum (fun n h => Real.log (F n h)) n h} ≤ δ := by
  apply le_trans (measureReal_mono (s₂ :=
    {h | (Real.exp ν) ^ n / δ ≤ historyProduct F n h}) ?_)
    (historyProduct_tail A P K hB (Real.exp_pos ν) hδ hm (fun n h => (hF n h).le) hb hstep n)
  intro h hh
  have he := Real.exp_lt_exp.mpr hh
  rw [← historyProduct_log hF, Real.exp_log (historyProduct_pos hF n h), Real.exp_add,
    Real.exp_log (one_div_pos.mpr hδ), Real.exp_nat_mul] at he
  simpa only [div_eq_mul_inv, one_mul] using he.le

end HeavyTail.AdaptiveKernel
