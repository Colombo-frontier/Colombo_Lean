import SecondOrder.RepeatedTrials
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory Filter

namespace SecondOrder
noncomputable section

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E}

theorem drawsSum_measurable (hX : Measurable X) (n : ℕ) : Measurable (drawsSum X n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).add (hX.comp measurable_snd)

theorem drawsMean_measurable (hX : Measurable X) (n : ℕ) : Measurable (drawsMean X n) :=
  (drawsSum_measurable hX n).const_smul _

/-- Repeated fresh batches followed by the Borel robust-center rule. -/
def robustBatch (X : Ω → E) (m : ℕ) {R : ℕ} (hR : 0 < R) (ρ : ℝ)
    (w : Draws (Draws Ω m) R) : E :=
  robustCenter hR (drawsVector (drawsMean X m) R w) (ρ/3)

theorem robustBatch_measurable (hX : Measurable X) (m : ℕ) {R : ℕ} (hR : 0 < R) (ρ : ℝ) :
    Measurable (robustBatch X m hR ρ) :=
  (robustCenter_measurable hR (ρ/3)).comp (drawsVector_measurable (drawsMean_measurable hX m) R)

theorem robustBatch_failure (hX : Measurable X) (hXi : Integrable X μ) {a : E}
    (he : Integrable (fun z => ‖X z-a‖^2) μ) (hmean : (∫ z, X z ∂μ) = a)
    {V ρ : ℝ} (hV : (∫ z, ‖X z-a‖^2 ∂μ) ≤ V) (hρ : 0 < ρ)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) (hsize : 36*V ≤ (m : ℝ)*ρ^2) :
    drawsLaw (drawsLaw μ m) R {w | ρ < ‖robustBatch X m hR ρ w-a‖} ≤
      ENNReal.ofReal ((7/8 : ℝ)^R) := by
  have hr : 0 < ρ/3 := by positivity
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hp : drawsLaw μ m {w | ρ/3 < dist (drawsMean X m w) a} ≤
      ENNReal.ofReal (1/4 : ℝ) := by
    apply (measure_mono (t := {w | ρ/3 ≤ ‖drawsMean X m w-a‖}) ?_).trans
      ((drawsMean_failure_probability hXi he hmean hm hr hV).trans ?_)
    · intro w hw
      exact (show ρ/3 < ‖drawsMean X m w-a‖ by simpa only [dist_eq_norm] using hw).le
    · apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (mul_pos hmR (sq_pos_of_pos hr))).mpr
      nlinarith
  have h := repeated_robustCenter_failure (drawsMean_measurable hX m) a (ρ/3) hR hp
  simpa only [robustBatch, dist_eq_norm, show 3*(ρ/3) = ρ by ring] using h

def localBatchSize (V ρ : ℝ) : ℕ := ⌈36*V/ρ^2⌉₊+1
def confidenceRepeats (δ : ℝ) : ℕ := ⌈8*Real.log (1/δ)⌉₊+1

theorem localBatchSize_pos (V ρ : ℝ) : 0 < localBatchSize V ρ := Nat.succ_pos _
theorem confidenceRepeats_pos (δ : ℝ) : 0 < confidenceRepeats δ := Nat.succ_pos _

theorem localBatchSize_sufficient (V : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    36*V ≤ (localBatchSize V ρ : ℝ)*ρ^2 := by
  have hc := Nat.le_ceil (36*V/ρ^2)
  have hr : 0 < ρ^2 := sq_pos_of_pos hρ
  have h := (div_le_iff₀ hr).mp hc
  dsimp [localBatchSize]
  push_cast
  nlinarith

theorem confidenceRepeats_sufficient {δ : ℝ} (hδ : 0 < δ) :
    (7/8 : ℝ)^(confidenceRepeats δ) ≤ δ := by
  have hc := Nat.le_ceil (8*Real.log (1/δ))
  have hn : 8*Real.log (1/δ) ≤ (confidenceRepeats δ : ℝ) := by
    dsimp [confidenceRepeats]
    push_cast
    linarith
  have hlog : Real.log (1/δ) = -Real.log δ := by
    rw [Real.log_div (by norm_num) hδ.ne', Real.log_one]; ring
  rw [hlog] at hn
  have he : (7/8 : ℝ) ≤ Real.exp (-(1/8 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1/8 : ℝ))]
  calc
    _ ≤ Real.exp (-(1/8 : ℝ))^(confidenceRepeats δ) := pow_le_pow_left₀ (by norm_num) he _
    _ = Real.exp ((confidenceRepeats δ : ℝ)*(-(1/8 : ℝ))) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr (by linarith)
    _ = δ := Real.exp_log hδ

theorem robustBatch_confidence (hX : Measurable X) (hXi : Integrable X μ) {a : E}
    (he : Integrable (fun z => ‖X z-a‖^2) μ) (hmean : (∫ z, X z ∂μ) = a)
    {V ρ δ : ℝ} (hV : (∫ z, ‖X z-a‖^2 ∂μ) ≤ V) (hρ : 0 < ρ) (hδ : 0 < δ) :
    drawsLaw (drawsLaw μ (localBatchSize V ρ)) (confidenceRepeats δ)
      {w | ρ < ‖robustBatch X (localBatchSize V ρ) (confidenceRepeats_pos δ) ρ w-a‖} ≤
      ENNReal.ofReal δ :=
  (robustBatch_failure hX hXi he hmean hV hρ (localBatchSize_pos V ρ)
    (confidenceRepeats_pos δ) (localBatchSize_sufficient V hρ)).trans
      (ENNReal.ofReal_le_ofReal (confidenceRepeats_sufficient hδ))

/-- Explicit sample-count bound; each factor corresponds to a concrete loop
length in the iterated product sampling space. -/
theorem robustBatch_query_count {V ρ δ : ℝ} (hV : 0 ≤ V) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((localBatchSize V ρ*confidenceRepeats δ : ℕ) : ℝ) ≤
      (36*V/ρ^2+2)*(8*Real.log (1/δ)+2) := by
  have hx : 0 ≤ 36*V/ρ^2 := by positivity
  have hy : 0 ≤ 8*Real.log (1/δ) := by
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    exact (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hm := Nat.ceil_lt_add_one hx
  have hR := Nat.ceil_lt_add_one hy
  have hmb : (localBatchSize V ρ : ℝ) ≤ 36*V/ρ^2+2 := by dsimp [localBatchSize]; push_cast; linarith
  have hRb : (confidenceRepeats δ : ℝ) ≤ 8*Real.log (1/δ)+2 := by
    dsimp [confidenceRepeats]; push_cast; linarith
  rw [Nat.cast_mul]
  exact mul_le_mul hmb hRb (Nat.cast_nonneg _) (by linarith)

end
end SecondOrder
