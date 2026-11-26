import RandomizedFO2003.Model

namespace RandomizedFO2003.Model

open MeasureTheory

/-- A measurable state machine using only the current first-order response.
Its compilation below gives the full-history algorithm required by the model. -/
structure DeterministicMachine (d : ℕ) (State : Type*) [MeasurableSpace State] where
  initial : State
  query : ℕ → State → Space d
  step : ℕ → State × Response d → State
  output : ℕ → State → Space d
  measurable_query : ∀ t, Measurable (query t)
  measurable_step : ∀ t, Measurable (step t)
  measurable_output : ∀ t, Measurable (output t)

namespace DeterministicMachine

variable {d : ℕ} {State : Type*} [MeasurableSpace State]
variable (P : DeterministicMachine d State)

def fold : (t : ℕ) → (Fin t → Response d) → State
  | 0, _ => P.initial
  | t + 1, h => P.step t (fold t (Fin.init h), h (Fin.last t))

theorem measurable_fold (t : ℕ) : Measurable (P.fold t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hi : Measurable (fun h : Fin (t + 1) → Response d => Fin.init h) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc)
    exact (P.measurable_step t).comp ((ih.comp hi).prodMk (measurable_pi_apply (Fin.last t)))

@[simp] theorem fold_snoc (t : ℕ) (h : Fin t → Response d) (r : Response d) :
    P.fold (t + 1) (Fin.snoc h r) = P.step t (P.fold t h, r) := by
  simp [fold]

def algorithm : Algorithm d Unit where
  query t _ h := P.query t (P.fold t h)
  output t _ h := P.output t (P.fold t h)
  query_measurable t := ((P.measurable_query t).comp (P.measurable_fold t)).comp measurable_snd
  output_measurable t := ((P.measurable_output t).comp (P.measurable_fold t)).comp measurable_snd

noncomputable def run (f : Space d → ℝ) : ℕ → State
  | 0 => P.initial
  | t + 1 => P.step t (run f t, oracle f (P.query t (run f t)))

/-- Exact closed-loop simulation of the compiled first-order algorithm. -/
theorem fold_transcript (f : Space d → ℝ) (t : ℕ) :
    P.fold t (transcript P.algorithm f () t) = P.run f t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [transcript, fold_snoc]
    change P.step t (P.fold t (transcript P.algorithm f () t),
      oracle f (P.query t (P.fold t (transcript P.algorithm f () t)))) = _
    rw [ih]
    rfl

theorem output_transcript (f : Space d → ℝ) (t : ℕ) :
    P.algorithm.output t () (transcript P.algorithm f () t) = P.output t (P.run f t) := by
  change P.output t (P.fold t _) = _
  rw [fold_transcript]

end DeterministicMachine

end RandomizedFO2003.Model
