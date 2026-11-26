import Bilevel.StatefulAcceleratedPrimitive

/-! Jointly measurable accelerated execution with frozen adaptive parameters.
The parameter travels unchanged through every batch and stage; only the
two accelerated states and the complete original oracle history evolve. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators

namespace Bilevel.ParameterizedStatefulAccelerated
open Stateful AcceleratedInner

variable {Param Query History Obs E : Type*}
  [MeasurableSpace Param] [MeasurableSpace Query] [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)
  (loc : Param × E → Query) (hloc : Measurable loc)
  (shift : Param → E) (hshift : Measurable shift)

def queryAt (α : ℝ) (z : Param × (E × E)) : Query :=
  loc (z.1, query α z.2.1 z.2.2)

include hloc in
omit [CompleteSpace E] in
theorem queryAt_measurable (α : ℝ) : Measurable (queryAt loc α) := by
  unfold queryAt
  apply hloc.comp
  unfold query
  fun_prop

def update (μ M α : ℝ) (z : (Param × (E × E)) × E) : E × E :=
  (nextU M (query α z.1.2.1 z.1.2.2) (z.2 + shift z.1.1),
    nextV μ α z.1.2.2 (query α z.1.2.1 z.1.2.2) (z.2 + shift z.1.1))

include hshift in
omit [CompleteSpace E] in
theorem update_measurable (μ M α : ℝ) : Measurable (update shift μ M α) := by
  unfold update nextU nextV query
  fun_prop

def step (μ M α : ℝ) (B : ℕ) : Procedure (Param × (E × E)) History (E × E) :=
  ((O.batch B).reparam (queryAt loc α) (queryAt_measurable loc hloc α)).map
    (update shift μ M α) (update_measurable shift hshift μ M α)

omit [CompleteSpace E] in
theorem step_calls (μ M α : ℝ) (B : ℕ) :
    (step O loc hloc shift hshift μ M α B).CallsEq (fun _ => B) :=
  Procedure.CallsEq.map _ _
    (Procedure.CallsEq.reparam _ _ (O.batch_calls B) _ (queryAt_measurable loc hloc α)) _ _

theorem step_potential (F : E → ℝ) (g : E → E) {μ M α : ℝ}
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hrel : α ^ 2 * M = μ) (p : Param) (htruth : ∀ y, O.truth (loc (p, y)) + shift p = g y)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (B : ℕ) (hB : 0 < B) (ys : E) (hmin : ∀ y, F ys ≤ F y)
    (s : E × E) (h : History) :
    Integrable (fun z => potential F μ ys z.1.1 z.1.2)
      ((step O loc hloc shift hshift μ M α B).law ((p, s), h)) ∧
      (∫ z, potential F μ ys z.1.1 z.1.2
        ∂(step O loc hloc shift hshift μ M α B).law ((p, s), h)) ≤
        (1 - α) * potential F μ ys s.1 s.2 + σ ^ 2 / ((B : ℝ) * M) := by
  let w := query α s.1 s.2
  have hmean := O.batch_mean B hB (loc (p, w)) h
  have herror := O.batch_error B hB (loc (p, w)) h
  have hh := expected_potential_step F g hM hμ hα hα1 hrel hg hlip hstrong
    s.1 s.2 ys hmin (fun z : Outcome E History => z.1 - O.truth (loc (p, w)))
    hmean.1 herror.1 hmean.2 (σ ^ 2 / (B : ℝ)) herror.2
  dsimp only at hh
  have hid (z : Outcome E History) : g (query α s.1 s.2) +
      (z.1 - O.truth (loc (p, w))) = z.1 + shift p := by
    change g w + (z.1 - O.truth (loc (p, w))) = _
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

def continueInput (z : (Param × (E × E)) × (E × E)) : Param × (E × E) := (z.1.1, z.2)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem continueInput_measurable : Measurable (continueInput (Param := Param) (E := E)) :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

def run (μ M α : ℝ) (B : ℕ) : ℕ → Procedure (Param × (E × E)) History (E × E)
  | 0 => Procedure.pure Prod.snd measurable_snd
  | n + 1 => (run μ M α B n).bind
      ((step O loc hloc shift hshift μ M α B).reparam continueInput continueInput_measurable)

omit [CompleteSpace E] in
theorem run_calls (μ M α : ℝ) (B n : ℕ) :
    (run O loc hloc shift hshift μ M α B n).CallsEq (fun _ => n * B) := by
  induction n with
  | zero =>
    simpa only [run, Nat.zero_mul] using
      (Procedure.calls_pure (History := History) (Prod.snd : Param × (E × E) → E × E) measurable_snd)
  | succ n ih =>
    have hc := Procedure.CallsEq.bind (run O loc hloc shift hshift μ M α B n)
      ((step O loc hloc shift hshift μ M α B).reparam continueInput continueInput_measurable)
      (fun _ => n * B) (fun _ => B) ih
      (Procedure.CallsEq.reparam _ _ (step_calls O loc hloc shift hshift μ M α B) _ continueInput_measurable)
    simpa only [Nat.succ_mul] using hc

theorem run_potential (F : E → ℝ) (g : E → E) {μ M α : ℝ}
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hrel : α ^ 2 * M = μ) (p : Param) (htruth : ∀ y, O.truth (loc (p, y)) + shift p = g y)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (B : ℕ) (hB : 0 < B) (ys : E) (hmin : ∀ y, F ys ≤ F y)
    (s : E × E) (h : History) (n : ℕ) :
    Integrable (fun z => potential F μ ys z.1.1 z.1.2)
      ((run O loc hloc shift hshift μ M α B n).law ((p, s), h)) ∧
      (∫ z, potential F μ ys z.1.1 z.1.2
        ∂(run O loc hloc shift hshift μ M α B n).law ((p, s), h)) ≤
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
    simp only [pow_zero, one_mul, sub_self, mul_zero, add_zero, V, le_refl]
  | succ n ih =>
    have hbound := Procedure.bind_output_bound (run O loc hloc shift hshift μ M α B n)
      ((step O loc hloc shift hshift μ M α B).reparam continueInput continueInput_measurable)
      (p, s) h V hV hn (fun z => (1 - α) * V z + σ ^ 2 / ((B : ℝ) * M))
      ((ih.1.const_mul (1 - α)).add (integrable_const _))
      (fun z => (step_potential O loc hloc shift hshift F g hM hμ hα.le hα1 hrel p htruth
        hg hlip hstrong B hB ys hmin z.1 z.2.1).1)
      (fun z => (step_potential O loc hloc shift hshift F g hM hμ hα.le hα1 hrel p htruth
        hg hlip hstrong B hB ys hmin z.1 z.2.1).2)
    refine ⟨hbound.1, hbound.2.trans ?_⟩
    rw [integral_add (ih.1.const_mul (1 - α)) (integrable_const _), integral_const_mul,
      integral_const, measureReal_univ_eq_one, one_smul]
    calc
      _ ≤ (1 - α) * ((1 - α) ^ n * V s +
          (σ ^ 2 / ((B : ℝ) * M * α)) * (1 - (1 - α) ^ n)) + σ ^ 2 / ((B : ℝ) * M) :=
        add_le_add_right (mul_le_mul_of_nonneg_left ih.2 (sub_nonneg.mpr hα1)) _
      _ = _ := by rw [hnoise, pow_succ]; dsimp [V]; ring

end Bilevel.ParameterizedStatefulAccelerated
