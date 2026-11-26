import Smoothness2601.StochasticNormalizedOuter
import Bilevel.StatefulProcedureLaws

/-! Actual normalized outer paths. Each estimator receives current x and the
supplied restart y0; the hidden oracle history and fixed counter are threaded. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Smoothness2601.NormalizedExecution
open Bilevel.Stateful

variable {X Y History : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [MeasurableSpace History]

abbrev Path (X : Type*) (n : ℕ) := Fin (n+1) → X

def append (η : ℝ) (n : ℕ) (z : ((X × Y) × Path X n) × X) : Path X (n+1) :=
  Fin.snoc z.1.2 (NormalizedOuter.step (z.1.2 (Fin.last n)) z.2 η)

omit [SecondCountableTopology X] in
theorem direction_measurable : Measurable (NormalizedOuter.direction (X := X)) :=
  measurable_id.norm.inv.smul measurable_id

theorem append_measurable (η : ℝ) (n : ℕ) : Measurable (append (X := X) (Y := Y) η n) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [append,Fin.snoc_last,NormalizedOuter.step]
    exact ((measurable_pi_apply (Fin.last n)).comp (measurable_snd.comp measurable_fst)).sub
      ((direction_measurable.comp measurable_snd).const_smul η)
  · simp only [append,Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)

def step (A : Procedure (X × Y) History X) (η : ℝ) (n : ℕ) :
    Procedure ((X × Y) × Path X n) History (Path X (n+1)) :=
  (A.reparam (fun z => (z.2 (Fin.last n),z.1.2))
    (((measurable_pi_apply (Fin.last n)).comp measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))).map (append η n) (append_measurable η n)

def run (A : Procedure (X × Y) History X) (η : ℝ) : (n : ℕ) → Procedure (X × Y) History (Path X n)
  | 0 => Procedure.pure (fun p _ => p.1) (measurable_pi_lambda _ (fun _ => measurable_fst))
  | n+1 => (run A η n).bind (step A η n)

theorem step_calls (A : Procedure (X × Y) History X) (N : ℕ) (hA : A.CallsEq (fun _ => N))
    (η : ℝ) (n : ℕ) : (step A η n).CallsEq (fun _ => N) :=
  Procedure.CallsEq.map _ _ (Procedure.CallsEq.reparam _ _ hA _ _) _ _

theorem run_calls (A : Procedure (X × Y) History X) (N : ℕ) (hA : A.CallsEq (fun _ => N))
    (η : ℝ) (n : ℕ) : (run A η n).CallsEq (fun _ => n*N) := by
  induction n with
  | zero =>
    simpa only [run,Nat.zero_mul] using (Procedure.calls_pure (History := History)
      (fun p : X × Y => fun _ : Fin 1 => p.1) (measurable_pi_lambda _ (fun _ => measurable_fst)))
  | succ n ih =>
    simpa only [Nat.succ_mul] using
      (Procedure.CallsEq.bind (run A η n) (step A η n) (fun _ => n*N) (fun _ => N)
        ih (step_calls A N hA η n))

theorem run_travel (A : Procedure (X × Y) History X) {η : ℝ} (hη : 0 ≤ η)
    (n : ℕ) (p : X × Y) (history : History) :
    ∀ᵐ z ∂(run A η n).law (p,history), ‖z.1 (Fin.last n)-p.1‖ ≤ (n:ℝ)*η := by
  have hp (m : ℕ) : MeasurableSet {z : Outcome (Path X m) History |
      ‖z.1 (Fin.last m)-p.1‖ ≤ (m:ℝ)*η} := by
    have hm : Measurable (fun z : Outcome (Path X m) History => ‖z.1 (Fin.last m)-p.1‖) := by fun_prop
    exact measurableSet_le hm measurable_const
  induction n with
  | zero =>
    rw [run,Procedure.pure_law]
    apply (ae_dirac_iff (hp 0)).mpr
    simp
  | succ n ih =>
    apply (Procedure.ae_bind_iff (run A η n) (step A η n) p history _ (hp (n+1))).mpr
    filter_upwards [ih] with z hz
    rw [step,Procedure.map_law]
    have hm : Measurable (fun w : Outcome X History => (append η n ((p,z.1),w.1),w.2)) :=
      ((append_measurable η n).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
    apply (ae_map_iff hm.aemeasurable (hp (n+1))).mpr
    filter_upwards with w
    simp only [append,Fin.snoc_last]
    calc
      _ ≤ ‖NormalizedOuter.step (z.1 (Fin.last n)) w.1 η-z.1 (Fin.last n)‖+
          ‖z.1 (Fin.last n)-p.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η+(n:ℝ)*η := add_le_add (NormalizedOuter.step_distance _ _ hη) hz
      _ = _ := by push_cast; ring

def selected {n : ℕ} (z : Fin n × Outcome (Path X n) History) : X := z.2.1 z.1.castSucc

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [BorelSpace X] [SecondCountableTopology X] in
theorem selected_measurable (n : ℕ) : Measurable (selected (X := X) (History := History) (n := n)) := by
  have hh : Measurable (fun z : Outcome (Path X n) History × Fin n => z.1.1 z.2.castSucc) :=
    measurable_from_prod_countable (fun i => (measurable_pi_apply i.castSucc).comp measurable_fst)
  exact hh.comp measurable_swap

def outputLaw (A : Procedure (X × Y) History X) (η : ℝ) (n : ℕ) [NeZero n]
    (p : X × Y) (history : History) : Measure (Fin n × Outcome (Path X n) History) :=
  (Bilevel.StochasticOuter.uniformLaw n).prod ((run A η n).law (p,history))

instance outputLaw_probability (A : Procedure (X × Y) History X) (η : ℝ) (n : ℕ) [NeZero n]
    (p : X × Y) (history : History) : IsProbabilityMeasure (outputLaw A η n p history) := by
  unfold outputLaw
  infer_instance

end Smoothness2601.NormalizedExecution
