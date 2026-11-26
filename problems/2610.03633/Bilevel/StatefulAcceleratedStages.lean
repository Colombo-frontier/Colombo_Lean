import Bilevel.StatefulAccelerated

/-! The actual accelerated stage composition. The two states and complete
oracle history are carried across stage boundaries, and call counters sum
the original batch sizes exactly. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators

namespace Bilevel.StatefulAccelerated
open Stateful AcceleratedInner

variable {History Obs E : Type*} [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := E) (History := History) (Obs := Obs) (E := E) σ)

def stages (μ M α : ℝ) (shift : E) (U : ℝ) : ℕ → Procedure (E × E) History (E × E)
  | 0 => Procedure.pure id measurable_id
  | s + 1 => (stages μ M α shift U s).bind
      ((run O μ M α shift (stageBatch M α σ (stageBudget U (s + 1))) (stageLength α)).reparam
        Prod.snd measurable_snd)

omit [CompleteSpace E] in
theorem stages_calls (μ M α : ℝ) (shift : E) (U : ℝ) (S : ℕ) :
    (stages O μ M α shift U S).CallsEq (fun _ =>
      stageLength α * ∑ s ∈ Finset.range S, stageBatch M α σ (stageBudget U (s + 1))) := by
  induction S with
  | zero =>
    simpa only [stages, Finset.sum_range_zero, Nat.mul_zero] using
      (Procedure.calls_pure (History := History) (id : E × E → E × E) measurable_id)
  | succ S ih =>
    have hc := Procedure.CallsEq.bind (stages O μ M α shift U S)
      ((run O μ M α shift (stageBatch M α σ (stageBudget U (S + 1))) (stageLength α)).reparam
        Prod.snd measurable_snd)
      (fun _ => stageLength α * ∑ s ∈ Finset.range S, stageBatch M α σ (stageBudget U (s + 1)))
      (fun _ => stageLength α * stageBatch M α σ (stageBudget U (S + 1))) ih
      (Procedure.CallsEq.reparam _ _ (run_calls O μ M α shift _ _) _ measurable_snd)
    simpa only [Finset.sum_range_succ, Nat.mul_add] using hc

theorem stages_potential (F : E → ℝ) (g : E → E) {μ M α U : ℝ} (shift : E)
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 < α) (hα1 : α ≤ 1) (hU : 0 < U)
    (hrel : α ^ 2 * M = μ) (htruth : ∀ y, O.truth y + shift = g y)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (ys : E) (hmin : ∀ y, F ys ≤ F y) (s : E × E)
    (hinit : potential F μ ys s.1 s.2 ≤ U) (h : History) (S : ℕ) :
    Integrable (fun z => potential F μ ys z.1.1 z.1.2) ((stages O μ M α shift U S).law (s, h)) ∧
      (∫ z, potential F μ ys z.1.1 z.1.2 ∂(stages O μ M α shift U S).law (s, h)) ≤
        stageBudget U S := by
  have hF : Continuous F := continuous_iff_continuousAt.mpr
    (fun y => (hg y).differentiableAt.continuousAt)
  let V : E × E → ℝ := fun z => potential F μ ys z.1 z.2
  have hV : Measurable V := by dsimp [V, potential]; fun_prop
  have hn (z : E × E) : 0 ≤ V z :=
    add_nonneg (sub_nonneg.mpr (hmin z.1)) (by positivity)
  induction S with
  | zero =>
    rw [stages, Procedure.pure_law]
    have hm : StronglyMeasurable (fun z : Outcome (E × E) History => V z.1) :=
      (hV.comp measurable_fst).stronglyMeasurable
    refine ⟨integrable_dirac' hm, ?_⟩
    rw [integral_dirac' _ _ hm]
    simpa only [V, id_eq, stageBudget, pow_zero, div_one] using hinit
  | succ S ih =>
    let B := stageBatch M α σ (stageBudget U (S + 1))
    have hB : 0 < B := stageBatch_pos _ _ _ _
    have hnext (z : E × E) (hz : History) := run_potential O F g shift hM hμ hα hα1 hrel
      htruth hg hlip hstrong B hB ys hmin z hz (stageLength α)
    have hquarter (z : E × E) (hz : History) :
        (∫ w, V w.1 ∂(run O μ M α shift B (stageLength α)).law (z, hz)) ≤
          (1 / 4) * V z + stageBudget U (S + 1) / 2 := by
      have hr := (hnext z hz).2
      have hfloor := stageBatch_floor (σ := σ) hM hα (stageBudget_pos hU (S + 1))
      have hf0 : 0 ≤ σ ^ 2 / ((B : ℝ) * M * α) := by positivity
      have hpow : 0 ≤ (1 - α) ^ stageLength α := pow_nonneg (sub_nonneg.mpr hα1) _
      have hfactor := mul_le_mul_of_nonneg_right (stageLength_contracts hα hα1) (hn z)
      dsimp [B] at hr hf0
      change _ ≤ _ at hr
      dsimp [V] at hfactor ⊢
      nlinarith
    have hb := Procedure.bind_output_bound (stages O μ M α shift U S)
      ((run O μ M α shift B (stageLength α)).reparam Prod.snd measurable_snd) s h V hV hn
      (fun z => (1 / 4) * V z + stageBudget U (S + 1) / 2)
      ((ih.1.const_mul (1 / 4)).add (integrable_const _))
      (fun z => (hnext z.1 z.2.1).1) (fun z => hquarter z.1 z.2.1)
    refine ⟨hb.1, hb.2.trans ?_⟩
    rw [integral_add (ih.1.const_mul (1 / 4)) (integrable_const _), integral_const_mul,
      integral_const, measureReal_univ_eq_one, one_smul]
    have hhalf := stageBudget_half U S
    linarith [ih.2]

theorem stages_distance (F : E → ℝ) (g : E → E) {μ M α U : ℝ} (shift : E)
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 < α) (hα1 : α ≤ 1) (hU : 0 < U)
    (hrel : α ^ 2 * M = μ) (htruth : ∀ y, O.truth y + shift = g y)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (ys : E) (hmin : ∀ y, F ys ≤ F y) (hstationary : g ys = 0) (s : E × E)
    (hinit : potential F μ ys s.1 s.2 ≤ U) (h : History) (S : ℕ) :
    Integrable (fun z => ‖z.1.1 - ys‖ ^ 2) ((stages O μ M α shift U S).law (s, h)) ∧
      (∫ z, ‖z.1.1 - ys‖ ^ 2 ∂(stages O μ M α shift U S).law (s, h)) ≤
        (2 / μ) * stageBudget U S := by
  have hp := stages_potential O F g shift hM hμ hα hα1 hU hrel htruth hg hlip hstrong
    ys hmin s hinit h S
  have hcoef : 0 ≤ 2 / μ := by positivity
  have hb (z : Outcome (E × E) History) :
      ‖z.1.1 - ys‖ ^ 2 ≤ (2 / μ) * potential F μ ys z.1.1 z.1.2 := by
    have hc := potential_controls_distance F g hμ.le hstrong z.1.1 z.1.2 ys hstationary
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hμ).mpr
    nlinarith
  have hm : Measurable (fun z : Outcome (E × E) History => ‖z.1.1 - ys‖ ^ 2) := by fun_prop
  have hi : Integrable (fun z => ‖z.1.1 - ys‖ ^ 2) ((stages O μ M α shift U S).law (s, h)) := by
    apply (hp.1.const_mul (2 / μ)).mono' hm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hb z
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi (hp.1.const_mul (2 / μ)) hb
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hp.2 hcoef)

end Bilevel.StatefulAccelerated
