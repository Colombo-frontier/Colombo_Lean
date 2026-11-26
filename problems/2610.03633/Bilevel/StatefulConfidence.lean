import Bilevel.StatefulProcedureLaws
import Bilevel.ConditionalConfidenceFinite

/-!
# Executed history-dependent confidence amplification

`amplify` runs the supplied Markov-kernel procedure repeatedly at a fixed
parameter, threads its actual terminal history, retains all candidates,
and applies the actual measurable median-distance selector. Its proof uses
kernel composition directly, so no iid representation is introduced.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.StatefulConfidence
open Stateful


variable {Param History E : Type*} [MeasurableSpace Param] [MeasurableSpace History]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def append (n : ℕ) (z : (Param × (Fin n → E)) × E) : Fin (n+1) → E :=
  Fin.snoc z.1.2 z.2

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
theorem append_measurable (n : ℕ) : Measurable (append (Param := Param) (E := E) n) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [append, Fin.snoc_last]
    exact measurable_snd
  · simp only [append, Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)

def step (A : Procedure Param History E) (n : ℕ) :
    Procedure (Param × (Fin n → E)) History (Fin (n+1) → E) :=
  (A.reparam Prod.fst measurable_fst).map (append n) (append_measurable n)

def collect (A : Procedure Param History E) : (n : ℕ) → Procedure Param History (Fin n → E)
  | 0 => Procedure.pure (fun _ => Fin.elim0) (by fun_prop)
  | n+1 => (collect A n).bind (step A n)

def amplify (A : Procedure Param History E) (q : ℕ) [NeZero q] : Procedure Param History E :=
  (collect A q).map (fun z => Bilevel.ConditionalConfidence.select z.2)
    (Bilevel.ConditionalConfidence.select_measurable (fun z : Param × (Fin q → E) => z.2)
      (fun i => (measurable_pi_apply i).comp measurable_snd))

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
theorem step_calls (A : Procedure Param History E) (c : Param → ℕ)
    (hc : A.CallsEq c) (n : ℕ) : (step A n).CallsEq (fun z => c z.1) :=
  Procedure.CallsEq.map _ _ (Procedure.CallsEq.reparam _ _ hc Prod.fst measurable_fst) _ _

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
theorem collect_calls (A : Procedure Param History E) (c : Param → ℕ)
    (hc : A.CallsEq c) (n : ℕ) : (collect A n).CallsEq (fun p => n * c p) := by
  induction n with
  | zero => simpa only [Nat.zero_mul] using Procedure.calls_pure (fun _ : Param => (Fin.elim0 : Fin 0 → E)) (by fun_prop)
  | succ n ih =>
    simpa only [Nat.succ_mul] using
      Procedure.CallsEq.bind (collect A n) (step A n) (fun p => n * c p) c ih (step_calls A c hc n)

/-- Exact original-call accounting for the executed amplifier. -/
theorem amplify_calls (A : Procedure Param History E) (c : Param → ℕ)
    (hc : A.CallsEq c) (q : ℕ) [NeZero q] :
    (amplify A q).CallsEq (fun p => q * c p) :=
  Procedure.CallsEq.map _ _ (collect_calls A c hc q) _ _

def badFlag (target : E) (a : ℝ) : E → ℝ := Bilevel.ConditionalConfidence.flag {v | a / 3 < ‖v - target‖}

omit [SecondCountableTopology E] in
theorem badFlag_measurable (target : E) (a : ℝ) : Measurable (badFlag target a) :=
  measurable_const.indicator (measurableSet_lt measurable_const (measurable_id.sub_const target).norm)

def count {n : ℕ} (target : E) (a : ℝ) (v : Fin n → E) : ℝ :=
  ∑ i, badFlag target a (v i)

def weight {n : ℕ} (target : E) (a : ℝ) (v : Fin n → E) : ℝ := Real.exp (count target a v)

omit [SecondCountableTopology E] in
theorem count_measurable (n : ℕ) (target : E) (a : ℝ) :
    Measurable (count (n := n) target a) := by
  apply Finset.measurable_sum
  intro i _
  exact (badFlag_measurable target a).comp (measurable_pi_apply i)

omit [SecondCountableTopology E] in
theorem weight_measurable (n : ℕ) (target : E) (a : ℝ) :
    Measurable (weight (n := n) target a) := (count_measurable n target a).exp

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem count_le (n : ℕ) (target : E) (a : ℝ) (v : Fin n → E) : count target a v ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (Bilevel.ConditionalConfidence.flag_bounds _ (v i)).2
    _ = _ := by simp

omit [SecondCountableTopology E] in
theorem weight_integrable {n : ℕ} (target : E) (a : ℝ)
    (μ : Measure (Outcome (Fin n → E) History)) [IsFiniteMeasure μ] :
    Integrable (fun z => weight target a z.1) μ := by
  apply (integrable_const (Real.exp n)).mono'
    ((weight_measurable n target a).comp measurable_fst).aestronglyMeasurable
  filter_upwards [] with z
  change ‖Real.exp (count target a z.1)‖ ≤ Real.exp n
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (count_le n target a z.1)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem weight_snoc {n : ℕ} (target : E) (a : ℝ) (v : Fin n → E) (w : E) :
    weight target a (Fin.snoc v w) = weight target a v +
      (Real.exp 1 - 1) * weight target a v * badFlag target a w := by
  have hc : count target a (Fin.snoc v w) = count target a v + badFlag target a w := by
    simp [count, Fin.sum_univ_castSucc]
  unfold weight
  rw [hc, Real.exp_add]
  classical
  by_cases h : a / 3 < ‖w - target‖
  · simp [badFlag, Bilevel.ConditionalConfidence.flag, Set.indicator_apply, h]
    ring
  · simp [badFlag, Bilevel.ConditionalConfidence.flag, Set.indicator_apply, h]

omit [SecondCountableTopology E] in
theorem candidate_flag_bound (A : Procedure Param History E) (target : Param → E)
    (a : Param → ℝ) (ha : ∀ p, 0 < a p)
    (hmse : A.MSEBound target (fun p => a p / 12)) (p : Param) (h : History) :
    (∫ z, badFlag (target p) (a p) z.1 ∂A.law (p,h)) ≤ 1 / 16 := by
  have hi : Integrable (fun z : Outcome E History => badFlag (target p) (a p) z.1)
      (A.law (p,h)) := by
    exact (integrable_const 1).indicator
      (measurableSet_lt measurable_const ((measurable_fst.sub_const (target p)).norm))
  have hpoint : ∀ z : Outcome E History,
      badFlag (target p) (a p) z.1 ≤ (9 / (a p) ^ 2) * ‖z.1 - target p‖ ^ 2 := by
    intro z
    classical
    by_cases hz : a p / 3 < ‖z.1 - target p‖
    · simp only [badFlag, Bilevel.ConditionalConfidence.flag, Set.indicator_apply, Set.mem_setOf_eq, hz, if_true]
      have hb : (a p) ^ 2 ≤ 9 * ‖z.1 - target p‖ ^ 2 := by have := ha p; nlinarith
      calc
        (1 : ℝ) ≤ 9 * ‖z.1 - target p‖ ^ 2 / (a p) ^ 2 :=
          (one_le_div (sq_pos_of_pos (ha p))).mpr hb
        _ = _ := by ring
    · simp only [badFlag, Bilevel.ConditionalConfidence.flag, Set.indicator_apply, Set.mem_setOf_eq, hz, if_false]
      positivity
  calc
    _ ≤ ∫ z, (9 / (a p) ^ 2) * ‖z.1 - target p‖ ^ 2 ∂A.law (p,h) :=
      integral_mono hi ((hmse p h).1.const_mul _) hpoint
    _ = (9 / (a p) ^ 2) * ∫ z, ‖z.1 - target p‖ ^ 2 ∂A.law (p,h) := integral_const_mul _ _
    _ ≤ (9 / (a p) ^ 2) * (a p / 12) ^ 2 :=
      mul_le_mul_of_nonneg_left (hmse p h).2 (by positivity)
    _ = 1 / 16 := by have := (ha p).ne'; field_simp; ring

omit [SecondCountableTopology E] in
theorem step_weight_bound (A : Procedure Param History E) (target : Param → E)
    (a : Param → ℝ) (ha : ∀ p, 0 < a p)
    (hmse : A.MSEBound target (fun p => a p / 12)) (n : ℕ)
    (p : Param) (v : Fin n → E) (h : History) :
    (∫ z, weight (target p) (a p) z.1 ∂(step A n).law ((p,v),h)) ≤
      Real.exp (1 / 8) * weight (target p) (a p) v := by
  rw [step, Procedure.map_output_integral _ _ _ _ _ _ (weight_measurable _ _ _).stronglyMeasurable]
  change (∫ z, weight (target p) (a p) (Fin.snoc v z.1) ∂A.law (p,h)) ≤ _
  simp_rw [weight_snoc]
  have hi : Integrable (fun z : Outcome E History => badFlag (target p) (a p) z.1)
      (A.law (p,h)) :=
    (integrable_const 1).indicator
      (measurableSet_lt measurable_const ((measurable_fst.sub_const (target p)).norm))
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul, integral_const,
    measureReal_univ_eq_one, one_smul]
  have hb := candidate_flag_bound A target a ha hmse p h
  have hW : 0 ≤ weight (target p) (a p) v := (Real.exp_pos _).le
  have he0 : 0 ≤ Real.exp 1 - 1 := by have := Real.add_one_le_exp 1; linarith
  have he3 : Real.exp 1 ≤ 3 := le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
  have hmul := mul_le_mul_of_nonneg_left hb (mul_nonneg he0 hW)
  have hbound : weight (target p) (a p) v +
      (Real.exp 1 - 1) * weight (target p) (a p) v *
        (∫ z, badFlag (target p) (a p) z.1 ∂A.law (p,h)) ≤
      (9 / 8) * weight (target p) (a p) v := by
    nlinarith [mul_le_mul_of_nonneg_right he3 hW]
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ hW
  have := Real.add_one_le_exp (1 / 8)
  linarith

omit [SecondCountableTopology E] in
/-- Exponential moment of the candidates generated by the actual kernel
composition, uniformly for every fixed initial parameter and history. -/
theorem collect_weight_bound (A : Procedure Param History E) (target : Param → E)
    (a : Param → ℝ) (ha : ∀ p, 0 < a p)
    (hmse : A.MSEBound target (fun p => a p / 12)) (n : ℕ) (p : Param) (h : History) :
    (∫ z, weight (target p) (a p) z.1 ∂(collect A n).law (p,h)) ≤ Real.exp ((n : ℝ) / 8) := by
  induction n with
  | zero =>
    rw [collect, Procedure.pure_law]
    rw [integral_dirac'
      (fun z : Outcome (Fin 0 → E) History => weight (target p) (a p) z.1) (Fin.elim0, h, 0)
      ((weight_measurable 0 (target p) (a p)).comp measurable_fst).stronglyMeasurable]
    simp [weight, count]
  | succ n ih =>
    have hb := Procedure.bind_output_bound (collect A n) (step A n) p h
      (weight (target p) (a p)) (weight_measurable _ _ _) (fun _ => (Real.exp_pos _).le)
      (fun v => Real.exp (1/8) * weight (target p) (a p) v)
      ((weight_integrable _ _ _).const_mul _)
      (fun z => weight_integrable _ _ _)
      (fun z => step_weight_bound A target a ha hmse n p z.1 z.2.1)
    apply hb.2.trans
    rw [integral_const_mul]
    calc
      _ ≤ Real.exp (1/8) * Real.exp ((n : ℝ)/8) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem count_eq_bad_card {n : ℕ} (target : E) (a : ℝ) (v : Fin n → E) :
    count target a v = ((Bilevel.ConditionalConfidence.bad v target (a / 3)).card : ℝ) := by
  classical
  simp [count, badFlag, Bilevel.ConditionalConfidence.flag,
    Bilevel.ConditionalConfidence.bad, Set.indicator_apply, dist_eq_norm]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem failure_implies_weight {q : ℕ} [NeZero q] (target : E) (a : ℝ) (v : Fin q → E)
    (hf : a < ‖Bilevel.ConditionalConfidence.select v - target‖) :
    Real.exp ((q : ℝ) / 4) ≤ weight target a v := by
  have hb : q ≤ 4 * (Bilevel.ConditionalConfidence.bad v target (a / 3)).card := by
    by_contra h
    have hh := Bilevel.ConditionalConfidence.select_distance_le v target a (lt_of_not_ge h)
    rw [dist_eq_norm] at hh
    exact (not_lt_of_ge hh) hf
  have hb' : (q : ℝ) ≤ 4 * ((Bilevel.ConditionalConfidence.bad v target (a / 3)).card : ℝ) :=
    by exact_mod_cast hb
  apply Real.exp_le_exp.mpr
  rw [count_eq_bad_card]
  linarith

set_option maxHeartbeats 800000 in
omit [SecondCountableTopology E] in
theorem collect_failure_bound (A : Procedure Param History E) (target : Param → E)
    (a : Param → ℝ) (ha : ∀ p, 0 < a p)
    (hmse : A.MSEBound target (fun p => a p / 12)) (q : ℕ) [NeZero q]
    (p : Param) (h : History) :
    ((collect A q).law (p,h)).real
      {z | a p < ‖Bilevel.ConditionalConfidence.select z.1 - target p‖} ≤
      Real.exp (-(q : ℝ) / 8) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := (collect A q).law (p,h))
    (f := fun z : Outcome (Fin q → E) History => weight (target p) (a p) z.1)
    (Filter.Eventually.of_forall (fun z : Outcome (Fin q → E) History =>
      (show 0 ≤ weight (target p) (a p) z.1 from (Real.exp_pos _).le)))
    (weight_integrable (target p) (a p) ((collect A q).law (p,h)))
    (Real.exp ((q : ℝ) / 4))
  have hm := hmarkov.trans (collect_weight_bound A target a ha hmse q p h)
  have htail : ((collect A q).law (p,h)).real
      {z | Real.exp ((q : ℝ) / 4) ≤ weight (target p) (a p) z.1} ≤
      Real.exp (-(q : ℝ) / 8) := by
    apply (mul_le_mul_iff_of_pos_right (Real.exp_pos ((q : ℝ) / 4))).mp
    have he : Real.exp (-(q : ℝ) / 8) * Real.exp ((q : ℝ) / 4) =
        Real.exp ((q : ℝ) / 8) := by rw [← Real.exp_add]; congr 1; ring
    rw [he]
    simpa only [mul_comm] using hm
  apply (measureReal_mono (μ := (collect A q).law (p,h)) (s₂ :=
    {z : Outcome (Fin q → E) History | Real.exp ((q : ℝ) / 4) ≤ weight (target p) (a p) z.1}) ?_).trans htail
  intro z hz
  exact failure_implies_weight (target p) (a p) z.1 hz

/-- Confidence of the actually executed amplifier at every entering
history. The base procedure may have arbitrary history-dependent laws. -/
theorem amplify_confidence (A : Procedure Param History E) (target : Param → E)
    (a : Param → ℝ) (ha : ∀ p, 0 < a p)
    (hmse : A.MSEBound target (fun p => a p / 12)) (q : ℕ) [NeZero q]
    (p : Param) (h : History) :
    ((amplify A q).law (p,h)).real {z | a p < ‖z.1 - target p‖} ≤
      Real.exp (-(q : ℝ) / 8) := by
  have hm : Measurable (fun z : Outcome (Fin q → E) History =>
      (Bilevel.ConditionalConfidence.select z.1, z.2)) :=
    (Bilevel.ConditionalConfidence.select_measurable (fun z => z.1)
      (fun i => (measurable_pi_apply i).comp measurable_fst)).prodMk measurable_snd
  have hs : MeasurableSet {z : Outcome E History | a p < ‖z.1 - target p‖} :=
    measurableSet_lt measurable_const (measurable_fst.sub_const (target p)).norm
  rw [amplify, Procedure.map_law, measureReal_def, Measure.map_apply hm hs]
  exact collect_failure_bound A target a ha hmse q p h

end Bilevel.StatefulConfidence
