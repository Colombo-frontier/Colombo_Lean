import Task003Base
import Nonsmooth.GeneralBodyProtasov
import Task003Integration.ProtasovPolicyTransport

namespace Task003Integration
open Set MeasureTheory Task003.OracleModel Task003.OracleStateMachine

/-- The known-body Protasov algorithm gives the exact Task003 oracle interface.
The l1 ball is used as the known body in Euclidean coordinates, so its shape
causes no loss in dimension, accuracy or query count. -/
theorem protasovOpenPrinciple_proved :
    Task003.ProtasovEndpoint.ProtasovOpenPrinciple 10488 := by
  intro d hd δ hδ hδhalf
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨T, S, mS, hS, p, hp, hT, hcert⟩ :=
    Nonsmooth.general_body_protasov (protasovBody d) (protasovBody_convex d)
      (protasovBody_compact d) (protasovBody_interior_nonempty d)
      (by simpa using hd) δ hδ hδhalf
  letI : MeasurableSpace S := mS
  letI : StandardBorelSpace S := hS
  refine ⟨T, toPolicy (protasovMachine p hp), ?_, ?_⟩
  · simpa only [finrank_euclideanSpace_fin] using hT
  · intro f ω
    have hcont : ContinuousOn (fun x => f (protasovCoordinates d x)) (protasovBody d) :=
      (f.continuous.comp (protasovCoordinates d).continuous).continuousOn
    have hconv := protasovBody_objective_convex d f f.convex
    have hh := hcert (fun x => f (protasovCoordinates d x)) hcont hconv
    have himage := protasov_source_value_image d f
    unfold Nonsmooth.bodyMinimum Nonsmooth.bodyMaximum at hh
    rw [himage] at hh
    cases ω
    rw [protasovPolicy_output_exact]
    exact hh

/-- This proof supplies the previously external Protasov literature input. -/
theorem protasovLiteratureInput_proved : Task003.LiteratureMain.ProtasovLiteratureInput :=
  ⟨10488, by norm_num, protasovOpenPrinciple_proved⟩

end Task003Integration
