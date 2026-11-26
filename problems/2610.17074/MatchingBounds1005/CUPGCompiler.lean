import MatchingBounds1005.Model
import RandomizedFO2003.DeterministicMachine

/-! Exact transfer of the verified finite-state compiler to the present paper's
algorithm model. The objectives/classes of the two papers are not identified. -/
namespace MatchingBounds1005.CUPG

open MeasureTheory

def compileMachine {d : ℕ} {S : Type*} [MeasurableSpace S]
    (P : RandomizedFO2003.Model.DeterministicMachine d S) : Model.Algorithm d Unit where
  query := P.algorithm.query
  output := P.algorithm.output
  query_measurable := P.algorithm.query_measurable
  output_measurable := P.algorithm.output_measurable

theorem compileMachine_transcript {d : ℕ} {S : Type*} [MeasurableSpace S]
    (P : RandomizedFO2003.Model.DeterministicMachine d S) (f : Model.Space d → ℝ) (t : ℕ) :
    Model.transcript (compileMachine P) f () t =
      RandomizedFO2003.Model.transcript P.algorithm f () t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Model.transcript, RandomizedFO2003.Model.transcript]
    rw [ih]
    rfl

theorem compileMachine_output {d : ℕ} {S : Type*} [MeasurableSpace S]
    (P : RandomizedFO2003.Model.DeterministicMachine d S) (f : Model.Space d → ℝ) (t : ℕ) :
    (compileMachine P).output t () (Model.transcript (compileMachine P) f () t) =
      P.output t (P.run f t) := by
  rw [compileMachine_transcript]
  exact P.output_transcript f t

end MatchingBounds1005.CUPG
