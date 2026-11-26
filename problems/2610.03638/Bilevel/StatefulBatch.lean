import Bilevel.HistoryStep
import Bilevel.FreshBatchKernel

/-! A genuine batch whose successive original calls thread the full history.
The conditional law may change at every call; no independence or common
stationary sampling distribution is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.Stateful.HistoryOracle
variable {Query History Obs E : Type*} [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)

def sumStep : Procedure (Query × E) History E :=
  O.step Prod.fst measurable_fst Prod.snd measurable_snd (fun _ => -1) measurable_const

def sum : ℕ → Procedure Query History E
  | 0 => Procedure.pure (fun _ => 0) measurable_const
  | n+1 => (sum n).bind O.sumStep

omit [CompleteSpace E] in
theorem sum_calls (n : ℕ) : (O.sum n).CallsEq (fun _ => n) := by
  induction n with
  | zero => exact Procedure.calls_pure _ _
  | succ n ih =>
    exact Procedure.CallsEq.bind _ _ _ _ ih (O.step_calls _ _ _ _ _ _)

theorem sum_error (n : ℕ) (q : Query) (h : History) :
    Integrable (fun z => ‖z.1 - (n : ℝ) • O.truth q‖ ^ 2) ((O.sum n).law (q,h)) ∧
      (∫ z, ‖z.1 - (n : ℝ) • O.truth q‖ ^ 2 ∂(O.sum n).law (q,h)) ≤ (n : ℝ) * σ ^ 2 := by
  induction n with
  | zero =>
    simp only [sum, Procedure.pure_law, Nat.cast_zero, zero_smul, sub_zero]
    have hm : StronglyMeasurable (fun z : Outcome E History => ‖z.1‖ ^ 2) :=
      (by fun_prop : Measurable (fun z : Outcome E History => ‖z.1‖ ^ 2)).stronglyMeasurable
    exact ⟨integrable_dirac' hm, by rw [integral_dirac' _ _ hm]; simp⟩
  | succ n ih =>
    have hb : Integrable (fun z : Outcome E History => ‖z.1 - (n : ℝ) • O.truth q‖ ^ 2 + σ ^ 2)
        ((O.sum n).law (q,h)) := ih.1.add (integrable_const _)
    have hs (z : Outcome E History) := O.step_error Prod.fst measurable_fst Prod.snd measurable_snd
      (fun _ => -1) measurable_const (q,z.1) z.2.1 (((n+1 : ℕ) : ℝ) • O.truth q)
    have he (u : E) : u - (-1 : ℝ) • O.truth q - ((n+1 : ℕ) : ℝ) • O.truth q =
        u - (n : ℝ) • O.truth q := by
      simp only [neg_smul, one_smul, sub_neg_eq_add, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel
    have hbound := Procedure.bind_output_bound (O.sum n) O.sumStep q h
      (fun v => ‖v - ((n+1 : ℕ) : ℝ) • O.truth q‖ ^ 2) (by fun_prop) (fun _ => sq_nonneg _)
      (fun v => ‖v - (n : ℝ) • O.truth q‖ ^ 2 + σ ^ 2) hb
      (fun z => (hs z).1) (fun z => by simpa only [he, neg_one_sq, one_mul] using (hs z).2)
    refine ⟨hbound.1, hbound.2.trans ?_⟩
    rw [integral_add ih.1 (integrable_const (σ ^ 2))]
    simp only [integral_const, measureReal_univ_eq_one, one_smul, Nat.cast_add, Nat.cast_one]
    nlinarith [ih.2]

def batch (n : ℕ) : Procedure Query History E :=
  (O.sum n).map (fun z => (n : ℝ)⁻¹ • z.2) (by fun_prop)

omit [CompleteSpace E] in
theorem batch_calls (n : ℕ) : (O.batch n).CallsEq (fun _ => n) :=
  Procedure.CallsEq.map _ _ (O.sum_calls n) _ _

theorem batch_error (n : ℕ) (hn : 0 < n) (q : Query) (h : History) :
    Integrable (fun z => ‖z.1 - O.truth q‖ ^ 2) ((O.batch n).law (q,h)) ∧
      (∫ z, ‖z.1 - O.truth q‖ ^ 2 ∂(O.batch n).law (q,h)) ≤ σ ^ 2 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have he (u : E) : ‖(n : ℝ)⁻¹ • u - O.truth q‖ ^ 2 =
      ((n : ℝ)⁻¹)^2 * ‖u - (n : ℝ) • O.truth q‖ ^ 2 := by
    have hvec : (n : ℝ)⁻¹ • u - O.truth q = (n : ℝ)⁻¹ • (u - (n : ℝ) • O.truth q) := by
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ hn', one_smul]
    rw [hvec, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hg : StronglyMeasurable (fun v : E => ‖v-O.truth q‖ ^ 2) :=
    (by fun_prop : Measurable (fun v : E => ‖v-O.truth q‖ ^ 2)).stronglyMeasurable
  have hs := O.sum_error n q h
  constructor
  · rw [batch, Procedure.map_output_integrable_iff _ _ _ _ _ _ hg]
    simp_rw [he]
    exact hs.1.const_mul _
  · rw [batch, Procedure.map_output_integral _ _ _ _ _ _ hg]
    simp_rw [he]
    rw [integral_const_mul]
    calc
      _ ≤ ((n : ℝ)⁻¹)^2 * ((n : ℝ) * σ ^ 2) :=
        mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _)
      _ = _ := by field_simp; ring

def batchAtRadius (radius : ℝ) : Procedure Query History E :=
  O.batch (FreshBatchKernel.count σ radius)

theorem batchAtRadius_mse (radius : ℝ) (hr : 0 < radius) :
    (O.batchAtRadius radius).MSEBound O.truth (fun _ => radius) := by
  intro q h
  have hh := O.batch_error _ (FreshBatchKernel.count_pos σ radius) q h
  exact ⟨hh.1, hh.2.trans (FreshBatchKernel.variance_bound σ hr)⟩

omit [CompleteSpace E] in
theorem batchAtRadius_calls (radius : ℝ) :
    (O.batchAtRadius radius).CallsEq (fun _ => FreshBatchKernel.count σ radius) :=
  O.batch_calls _

end Bilevel.Stateful.HistoryOracle
