import Task003Base
import Nonsmooth.MeasurableSimulation
import Task003Integration.ProtasovCoordinates

namespace Task003Integration
open Set MeasureTheory Task003.OracleModel Task003.OracleStateMachine

/-- A known-body state machine, transported by the public linear coordinate map.
The query, transition and output maps have no objective argument. -/
noncomputable def protasovMachine {d : ℕ} {S : Type} [MeasurableSpace S]
    (p : Nonsmooth.Policy Unit S (protasovBody d)) (hp : p.IsMeasurable) :
    Machine d 1 Unit S where
  initial := p.initial
  initial_measurable := hp.initial
  step n z := p.update n z.1 z.2.1 z.2.2
  step_measurable := hp.update
  query n z := protasovCoordinates d (p.query n z.1 z.2).val
  query_measurable n := (protasovCoordinates d).continuous.measurable.comp
    (measurable_subtype_coe.comp (hp.query n))
  output _ z := protasovCoordinates d (p.output z.1 z.2).val
  output_measurable _ := (protasovCoordinates d).continuous.measurable.comp
    (measurable_subtype_coe.comp hp.output)
  output_feasible _ z := (mem_protasovBody _).mp (p.output z.1 z.2).property

/-- The same real oracle response drives both states at every recursive step. -/
theorem protasovMachine_evolution {d : ℕ} {S : Type} [MeasurableSpace S]
    (p : Nonsmooth.Policy Unit S (protasovBody d)) (hp : p.IsMeasurable)
    (f : Point d → ℝ) (k n : ℕ) :
    evolution (protasovMachine p hp) f () n
      (p.run (fun x => f (protasovCoordinates d x.val)) () n) k =
      p.run (fun x => f (protasovCoordinates d x.val)) () (n + k) := by
  induction k generalizing n with
  | zero => simp only [evolution, Nat.add_zero]
  | succ k ih =>
    change evolution (protasovMachine p hp) f () (n + 1)
      (p.run (fun x => f (protasovCoordinates d x.val)) () (n + 1)) k = _
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1)

/-- Transport preserves the actual output at the same pathwise query cap. -/
theorem protasovPolicy_output_exact {d : ℕ} {S : Type} [MeasurableSpace S]
    (p : Nonsmooth.Policy Unit S (protasovBody d)) (hp : p.IsMeasurable)
    (f : Point d → ℝ) (T : ℕ) :
    run (toPolicy (protasovMachine p hp)) f T () =
      protasovCoordinates d (p.result (fun x => f (protasovCoordinates d x.val)) () T).val := by
  rw [run_toPolicy]
  change protasovCoordinates d (p.output ()
    (evolution (protasovMachine p hp) f () 0 (p.initial ()) T)).val = _
  have hs := protasovMachine_evolution p hp f T 0
  simp only [Nonsmooth.Policy.run, Nat.zero_add] at hs
  rw [hs]
  rfl

theorem protasov_source_value_image (d : ℕ) (f : Point d → ℝ) :
    (fun x => f (protasovCoordinates d x)) '' protasovBody d =
      f '' {x : Point d | Feasible 1 x} := by
  rw [protasovBody_value_image]
  congr 1
  ext x
  simp [Feasible, Metric.mem_closedBall, dist_zero_right]

end Task003Integration
