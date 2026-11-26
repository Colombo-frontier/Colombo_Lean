import Bilevel.StatefulBatch
import Bilevel.AcceleratedSchedule

/-! Accelerated updates implemented by actual history-threading oracle kernels.
Every batch uses the original oracle and carries its complete terminal history.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Bilevel.Stateful.HistoryOracle

variable {Query History Obs E : Type*} [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)

theorem sum_centered_integrable (n : ℕ) (q : Query) (h : History) :
    Integrable (fun z => z.1 - (n : ℝ) • O.truth q) ((O.sum n).law (q, h)) := by
  have hm : MemLp (fun z : Outcome E History => z.1 - (n : ℝ) • O.truth q) 2
      ((O.sum n).law (q, h)) :=
    (memLp_two_iff_integrable_sq_norm
      (by fun_prop : Measurable (fun z : Outcome E History => z.1 - (n : ℝ) • O.truth q)).aestronglyMeasurable).mpr
      (O.sum_error n q h).1
  exact hm.integrable (by norm_num)

theorem sumStep_center_mean (n : ℕ) (q : Query) (u : E) (h : History) :
    (∫ z, z.1 - ((n + 1 : ℕ) : ℝ) • O.truth q ∂O.sumStep.law ((q, u), h)) =
      u - (n : ℝ) • O.truth q := by
  have hf : StronglyMeasurable (fun v : E => v - ((n + 1 : ℕ) : ℝ) • O.truth q) :=
    (by fun_prop : Measurable (fun v : E => v - ((n + 1 : ℕ) : ℝ) • O.truth q)).stronglyMeasurable
  rw [sumStep, step, Procedure.map_output_integral _ _ _ _ _ _ hf]
  change (∫ z, u - (-1 : ℝ) • z.1 - ((n + 1 : ℕ) : ℝ) • O.truth q
    ∂O.call.law (q, h)) = _
  have hid (z : Outcome E History) :
      u - (-1 : ℝ) • z.1 - ((n + 1 : ℕ) : ℝ) • O.truth q =
        (u - (n : ℝ) • O.truth q) + (z.1 - O.truth q) := by
    simp only [neg_smul, one_smul, sub_neg_eq_add, Nat.cast_add, Nat.cast_one, add_smul]
    abel
  simp_rw [hid]
  rw [integral_add (integrable_const _) (O.call_mean q h).1,
    (O.call_mean q h).2, integral_const, measureReal_univ_eq_one, one_smul, add_zero]

/-- Finite history-dependent batching retains exact unbiasedness. -/
theorem sum_mean (n : ℕ) : (O.sum n).Mean (fun q => (n : ℝ) • O.truth q) := by
  intro q h
  refine ⟨O.sum_centered_integrable n q h, ?_⟩
  induction n with
  | zero =>
    rw [sum, Procedure.pure_law]
    simp only [Nat.cast_zero, zero_smul, sub_zero]
    exact integral_dirac' _ _ measurable_fst.stronglyMeasurable
  | succ n ih =>
    have hm : StronglyMeasurable (fun z : Outcome E History => z.1 - ((n + 1 : ℕ) : ℝ) • O.truth q) :=
      (by fun_prop : Measurable (fun z : Outcome E History => z.1 - ((n + 1 : ℕ) : ℝ) • O.truth q)).stronglyMeasurable
    have hi := O.sum_centered_integrable (n + 1) q h
    change Integrable _ (((O.sum n).bind O.sumStep).law (q, h)) at hi
    rw [sum, Procedure.integral_bind _ _ _ _ _ hm hi]
    have hid (z : Outcome E History) :
        (∫ w, (Procedure.combine (z, w)).1 - ((n + 1 : ℕ) : ℝ) • O.truth q
          ∂O.sumStep.law ((q, z.1), z.2.1)) = z.1 - (n : ℝ) • O.truth q :=
      O.sumStep_center_mean n q z.1 z.2.1
    simp_rw [hid]
    exact ih

theorem batch_mean (n : ℕ) (hn : 0 < n) : (O.batch n).Mean O.truth := by
  intro q h
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hf : StronglyMeasurable (fun v : E => v - O.truth q) :=
    (by fun_prop : Measurable (fun v : E => v - O.truth q)).stronglyMeasurable
  have hid (z : Outcome E History) :
      (n : ℝ)⁻¹ • z.1 - O.truth q = (n : ℝ)⁻¹ • (z.1 - (n : ℝ) • O.truth q) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hn', one_smul]
  constructor
  · rw [batch, Procedure.map_output_integrable_iff _ _ _ _ _ _ hf]
    simp_rw [hid]
    exact (O.sum_mean n q h).1.smul _
  · rw [batch, Procedure.map_output_integral _ _ _ _ _ _ hf]
    simp_rw [hid]
    rw [integral_smul, (O.sum_mean n q h).2, smul_zero]

end Bilevel.Stateful.HistoryOracle

namespace Bilevel.StatefulAccelerated

open Stateful AcceleratedInner
variable {History Obs E : Type*} [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := E) (History := History) (Obs := Obs) (E := E) σ)

def stateQuery (α : ℝ) (s : E × E) : E := query α s.1 s.2

omit [CompleteSpace E] in
theorem stateQuery_measurable (α : ℝ) : Measurable (stateQuery (E := E) α) := by
  unfold stateQuery query
  fun_prop

/-- Both coordinates use the same returned batch vector. A fixed linear
tilt is added after the original oracle responses are averaged. -/
def update (μ M α : ℝ) (shift : E) (z : (E × E) × E) : E × E :=
  (nextU M (stateQuery α z.1) (z.2 + shift),
    nextV μ α z.1.2 (stateQuery α z.1) (z.2 + shift))

omit [CompleteSpace E] in
theorem update_measurable (μ M α : ℝ) (shift : E) : Measurable (update μ M α shift) := by
  unfold update nextU nextV stateQuery query
  fun_prop

def step (μ M α : ℝ) (shift : E) (B : ℕ) : Procedure (E × E) History (E × E) :=
  ((O.batch B).reparam (stateQuery α) (stateQuery_measurable α)).map
    (update μ M α shift) (update_measurable μ M α shift)

omit [CompleteSpace E] in
theorem step_calls (μ M α : ℝ) (shift : E) (B : ℕ) :
    (step O μ M α shift B).CallsEq (fun _ => B) :=
  Procedure.CallsEq.map _ _
    (Procedure.CallsEq.reparam _ _ (O.batch_calls B) _ (stateQuery_measurable α)) _ _

/-- Expected potential contraction of the implemented original-SFO batch
step, valid separately for every entering full history. -/
theorem step_potential (F : E → ℝ) (g : E → E) {μ M α : ℝ} (shift : E)
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hrel : α ^ 2 * M = μ) (htruth : ∀ y, O.truth y + shift = g y)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (B : ℕ) (hB : 0 < B) (ys : E) (hmin : ∀ y, F ys ≤ F y)
    (s : E × E) (h : History) :
    Integrable (fun z => potential F μ ys z.1.1 z.1.2) ((step O μ M α shift B).law (s, h)) ∧
      (∫ z, potential F μ ys z.1.1 z.1.2 ∂(step O μ M α shift B).law (s, h)) ≤
        (1 - α) * potential F μ ys s.1 s.2 + σ ^ 2 / ((B : ℝ) * M) := by
  let w := stateQuery α s
  have hmean := O.batch_mean B hB w h
  have herror := O.batch_error B hB w h
  have hh := expected_potential_step F g hM hμ hα hα1 hrel hg hlip hstrong
    s.1 s.2 ys hmin (fun z : Outcome E History => z.1 - O.truth w)
    hmean.1 herror.1 hmean.2 (σ ^ 2 / (B : ℝ)) herror.2
  dsimp only at hh
  have hid (z : Outcome E History) : g (query α s.1 s.2) + (z.1 - O.truth w) = z.1 + shift := by
    change g w + (z.1 - O.truth w) = _
    rw [← htruth w]
    abel
  simp_rw [hid] at hh
  have hF : Continuous F := continuous_iff_continuousAt.mpr
    (fun y => (hg y).differentiableAt.continuousAt)
  have hp : StronglyMeasurable (fun z : E × E => potential F μ ys z.1 z.2) := by
    apply Measurable.stronglyMeasurable
    unfold potential
    fun_prop
  constructor
  · rw [step, Procedure.map_output_integrable_iff _ _ _ _ _ _ hp]
    exact hh.1
  · rw [step, Procedure.map_output_integral _ _ _ _ _ _ hp]
    convert hh.2 using 1
    simp only [div_div]

def run (μ M α : ℝ) (shift : E) (B : ℕ) : ℕ → Procedure (E × E) History (E × E)
  | 0 => Procedure.pure id measurable_id
  | n + 1 => (run μ M α shift B n).bind
      ((step O μ M α shift B).reparam Prod.snd measurable_snd)

omit [CompleteSpace E] in
theorem run_calls (μ M α : ℝ) (shift : E) (B n : ℕ) :
    (run O μ M α shift B n).CallsEq (fun _ => n * B) := by
  induction n with
  | zero =>
    simpa only [run, Nat.zero_mul] using
      (Procedure.calls_pure (History := History) (id : E × E → E × E) measurable_id)
  | succ n ih =>
    have hc := Procedure.CallsEq.bind (run O μ M α shift B n)
      ((step O μ M α shift B).reparam Prod.snd measurable_snd)
      (fun _ => n * B) (fun _ => B) ih
      (Procedure.CallsEq.reparam _ _ (step_calls O μ M α shift B) _ measurable_snd)
    simpa only [Nat.succ_mul] using hc

theorem run_potential (F : E → ℝ) (g : E → E) {μ M α : ℝ} (shift : E)
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hrel : α ^ 2 * M = μ) (htruth : ∀ y, O.truth y + shift = g y)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (B : ℕ) (hB : 0 < B) (ys : E) (hmin : ∀ y, F ys ≤ F y)
    (s : E × E) (h : History) (n : ℕ) :
    Integrable (fun z => potential F μ ys z.1.1 z.1.2) ((run O μ M α shift B n).law (s, h)) ∧
      (∫ z, potential F μ ys z.1.1 z.1.2 ∂(run O μ M α shift B n).law (s, h)) ≤
        (1 - α) ^ n * potential F μ ys s.1 s.2 +
          (σ ^ 2 / ((B : ℝ) * M * α)) * (1 - (1 - α) ^ n) := by
  have hF : Continuous F := continuous_iff_continuousAt.mpr
    (fun y => (hg y).differentiableAt.continuousAt)
  let V : E × E → ℝ := fun z => potential F μ ys z.1 z.2
  have hV : Measurable V := by dsimp [V, potential]; fun_prop
  have hn (z : E × E) : 0 ≤ V z :=
    add_nonneg (sub_nonneg.mpr (hmin z.1)) (by positivity)
  have hbpos : 0 < (B : ℝ) := Nat.cast_pos.mpr hB
  have hnoise : σ ^ 2 / ((B : ℝ) * M) =
      α * (σ ^ 2 / ((B : ℝ) * M * α)) := by field_simp; ring
  induction n with
  | zero =>
    rw [run, Procedure.pure_law]
    have hm : StronglyMeasurable (fun z : Outcome (E × E) History => V z.1) :=
      (hV.comp measurable_fst).stronglyMeasurable
    refine ⟨integrable_dirac' hm, ?_⟩
    rw [integral_dirac' _ _ hm]
    simp only [id_eq, pow_zero, one_mul, sub_self, mul_zero, add_zero, V, le_refl]
  | succ n ih =>
    have hbound := Procedure.bind_output_bound (run O μ M α shift B n)
      ((step O μ M α shift B).reparam Prod.snd measurable_snd) s h V hV hn
      (fun z => (1 - α) * V z + σ ^ 2 / ((B : ℝ) * M))
      ((ih.1.const_mul (1 - α)).add (integrable_const _))
      (fun z => (step_potential O F g shift hM hμ hα.le hα1 hrel htruth hg hlip hstrong
        B hB ys hmin z.1 z.2.1).1)
      (fun z => (step_potential O F g shift hM hμ hα.le hα1 hrel htruth hg hlip hstrong
        B hB ys hmin z.1 z.2.1).2)
    refine ⟨hbound.1, hbound.2.trans ?_⟩
    rw [integral_add (ih.1.const_mul (1 - α)) (integrable_const _), integral_const_mul,
      integral_const, measureReal_univ_eq_one, one_smul]
    calc
      _ ≤ (1 - α) * ((1 - α) ^ n * V s +
          (σ ^ 2 / ((B : ℝ) * M * α)) * (1 - (1 - α) ^ n)) + σ ^ 2 / ((B : ℝ) * M) :=
        add_le_add_right (mul_le_mul_of_nonneg_left ih.2 (sub_nonneg.mpr hα1)) _
      _ = _ := by rw [hnoise, pow_succ]; dsimp [V]; ring

end Bilevel.StatefulAccelerated
