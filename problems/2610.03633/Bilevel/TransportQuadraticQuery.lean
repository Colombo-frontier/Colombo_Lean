import Bilevel.TransportPhysicalBatchLower
import Bilevel.TransportProgramController

/-! The full physical query is frozen before the edge batch. Its physical
lower point supplies one query at each network layer, and its macro point
supplies one auxiliary query. Terminal endpoints are observed separately. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportHierarchy
open PrimitiveGeometry PartialLegendre EndpointTransportResponse TransportRound
set_option autoImplicit false
set_option maxHeartbeats 800000

abbrev QuadraticOutput (D : ℕ) := Joint (Block D) (Block D)
abbrev QuadraticQuery (n D : ℕ) := Joint (QuadraticOutput D) (Physical n D)
abbrev QuadraticReply (n D : ℕ) := QuadraticQuery n D × QuadraticQuery n D

def quadraticNetworkQueries {n D : ℕ} (w : QuadraticQuery n D) : Queries (n+1) D 1 :=
  fun v _ => w.snd v

def quadraticAuxiliaryQueries {n D : ℕ} (w : QuadraticQuery n D) : Fin 1 → Block D :=
  fun _ => w.fst.fst

def quadraticNetworkOutput {n D : ℕ} (x : QuadraticOutput D) : Queries (n+1) D 1 :=
  fun _ _ => x.snd

def quadraticAuxiliaryOutput {D : ℕ} (x : QuadraticOutput D) : Block D := x.fst

theorem quadraticNetworkQueries_physical {n D : ℕ} (w : QuadraticQuery n D) :
    physical (fun v => quadraticNetworkQueries w v 0)=w.snd := rfl

section Measurable
variable {n D : ℕ} [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)]
  [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)]

omit [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)] in
theorem quadraticNetworkQueries_measurable : Measurable (quadraticNetworkQueries (n:=n) (D:=D)) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro a
  exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : EndpointTransportMatrix.Index n => Block D) v).continuous.measurable.comp
    ((jointSndLinear (A:=QuadraticOutput D) (B:=Physical n D)).continuous.measurable)

omit [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)] in
theorem quadraticAuxiliaryQueries_measurable : Measurable (quadraticAuxiliaryQueries (n:=n) (D:=D)) := by
  apply measurable_pi_lambda
  intro a
  exact (jointFstLinear (A:=Block D) (B:=Block D)).continuous.measurable.comp
    (jointFstLinear (A:=QuadraticOutput D) (B:=Physical n D)).continuous.measurable

omit [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)] in
theorem quadraticNetworkOutput_measurable : Measurable (quadraticNetworkOutput (n:=n) (D:=D)) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro a
  exact (jointSndLinear (A:=Block D) (B:=Block D)).continuous.measurable

omit [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)] in
theorem quadraticAuxiliaryOutput_measurable : Measurable (quadraticAuxiliaryOutput (D:=D)) :=
  (jointFstLinear (A:=Block D) (B:=Block D)).continuous.measurable

end Measurable
end Bilevel.TransportHierarchy
