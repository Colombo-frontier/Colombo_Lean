import Bilevel.StatefulConfidence

/-! Local-input confidence guarantees for the unchanged global amplifier.
Only the fixed valid input needs a per-history MSE certificate. The procedure
does not query the target or test certificate membership. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.StatefulConfidence
open Stateful

variable {Param History E : Type*} [MeasurableSpace Param] [MeasurableSpace History]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
theorem step_weight_bound_at (A : Procedure Param History E) (p : Param) (target : E)
    (a : ℝ) (ha : 0 < a)
    (hmse : ∀ h, Integrable (fun z => ‖z.1-target‖^2) (A.law (p,h)) ∧
      (∫ z, ‖z.1-target‖^2 ∂A.law (p,h)) ≤ (a/12)^2)
    (n : ℕ) (v : Fin n → E) (h : History) :
    (∫ z, weight target a z.1 ∂(step A n).law ((p,v),h)) ≤ Real.exp (1/8) * weight target a v := by
  let A₀ := A.reparam (fun _ : Unit => p) measurable_const
  have hlocal : A₀.MSEBound (fun _ => target) (fun _ => a / 12) := fun _ h => hmse h
  have hb := step_weight_bound A₀ (fun _ => target) (fun _ => a) (fun _ => ha) hlocal n () v h
  rw [step, Procedure.map_output_integral _ _ _ _ _ _ (weight_measurable _ _ _).stronglyMeasurable] at hb ⊢
  exact hb

omit [SecondCountableTopology E] in
theorem collect_weight_bound_at (A : Procedure Param History E) (p : Param) (target : E)
    (a : ℝ) (ha : 0 < a)
    (hmse : ∀ h, Integrable (fun z => ‖z.1-target‖^2) (A.law (p,h)) ∧
      (∫ z, ‖z.1-target‖^2 ∂A.law (p,h)) ≤ (a/12)^2)
    (n : ℕ) (h : History) :
    (∫ z, weight target a z.1 ∂(collect A n).law (p,h)) ≤ Real.exp ((n : ℝ)/8) := by
  induction n with
  | zero =>
    rw [collect, Procedure.pure_law]
    rw [integral_dirac' (fun z : Outcome (Fin 0 → E) History => weight target a z.1)
      (Fin.elim0,h,0) ((weight_measurable 0 target a).comp measurable_fst).stronglyMeasurable]
    simp [weight,count]
  | succ n ih =>
    have hb := Procedure.bind_output_bound (collect A n) (step A n) p h
      (weight target a) (weight_measurable _ _ _) (fun _ => (Real.exp_pos _).le)
      (fun v => Real.exp (1/8) * weight target a v)
      ((weight_integrable _ _ _).const_mul _) (fun z => weight_integrable _ _ _)
      (fun z => step_weight_bound_at A p target a ha hmse n z.1 z.2.1)
    apply hb.2.trans
    rw [integral_const_mul]
    calc
      _ ≤ Real.exp (1/8) * Real.exp ((n:ℝ)/8) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

set_option maxHeartbeats 800000 in
omit [SecondCountableTopology E] in
theorem collect_failure_bound_at (A : Procedure Param History E) (p : Param) (target : E)
    (a : ℝ) (ha : 0 < a)
    (hmse : ∀ h, Integrable (fun z => ‖z.1-target‖^2) (A.law (p,h)) ∧
      (∫ z, ‖z.1-target‖^2 ∂A.law (p,h)) ≤ (a/12)^2)
    (q : ℕ) [NeZero q] (h : History) :
    ((collect A q).law (p,h)).real
      {z | a < ‖Bilevel.ConditionalConfidence.select z.1-target‖} ≤ Real.exp (-(q:ℝ)/8) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := (collect A q).law (p,h))
    (f := fun z : Outcome (Fin q → E) History => weight target a z.1)
    (Filter.Eventually.of_forall fun z => (show 0 ≤ weight target a z.1 from (Real.exp_pos _).le))
    (weight_integrable target a ((collect A q).law (p,h))) (Real.exp ((q:ℝ)/4))
  have hm := hmarkov.trans (collect_weight_bound_at A p target a ha hmse q h)
  have htail : ((collect A q).law (p,h)).real
      {z | Real.exp ((q:ℝ)/4) ≤ weight target a z.1} ≤ Real.exp (-(q:ℝ)/8) := by
    apply (mul_le_mul_iff_of_pos_right (Real.exp_pos ((q:ℝ)/4))).mp
    have he : Real.exp (-(q:ℝ)/8) * Real.exp ((q:ℝ)/4) = Real.exp ((q:ℝ)/8) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he]
    simpa only [mul_comm] using hm
  apply (measureReal_mono (μ := (collect A q).law (p,h)) (s₂ :=
    {z : Outcome (Fin q → E) History | Real.exp ((q:ℝ)/4) ≤ weight target a z.1}) ?_).trans htail
  intro z hz
  exact failure_implies_weight target a z.1 hz

/-- Confidence at one valid parameter of the original, unchanged amplifier.
No MSE assumption is imposed at other inputs. -/
theorem amplify_confidence_at (A : Procedure Param History E) (p : Param) (target : E)
    (a : ℝ) (ha : 0 < a)
    (hmse : ∀ h, Integrable (fun z => ‖z.1-target‖^2) (A.law (p,h)) ∧
      (∫ z, ‖z.1-target‖^2 ∂A.law (p,h)) ≤ (a/12)^2)
    (q : ℕ) [NeZero q] (h : History) :
    ((amplify A q).law (p,h)).real {z | a < ‖z.1-target‖} ≤ Real.exp (-(q:ℝ)/8) := by
  have hm : Measurable (fun z : Outcome (Fin q → E) History =>
      (Bilevel.ConditionalConfidence.select z.1,z.2)) :=
    (Bilevel.ConditionalConfidence.select_measurable (fun z => z.1)
      (fun i => (measurable_pi_apply i).comp measurable_fst)).prodMk measurable_snd
  have hs : MeasurableSet {z : Outcome E History | a < ‖z.1-target‖} :=
    measurableSet_lt measurable_const (measurable_fst.sub_const target).norm
  rw [amplify,Procedure.map_law,measureReal_def,Measure.map_apply hm hs]
  exact collect_failure_bound_at A p target a ha hmse q h

end Bilevel.StatefulConfidence
