import GradientHessian.MachineTransport
import GradientHessian.JetPullback

/-! Measurable oracle policies for actual linearly transformed objectives.
The simulator uses one reply of the same kind for every original query. -/

noncomputable section
namespace GradientHessian.Machine
open Model MeasureTheory Set

variable {Seed State : Type*} [MeasurableSpace Seed] [MeasurableSpace State] {d N : ℕ}

def Policy.linearTransport (P : Policy Seed State (Point d) (OrdinaryReply d) (RichReply d))
    (a : ℝ) (L : Point d →L[ℝ] Point N) : Policy Seed State (Point N) (OrdinaryReply N) (RichReply N) :=
  P.transport L (fun z => JetPullback.ordinary a L z.2) (fun z => JetPullback.rich a L z.2)
    L.continuous.measurable ((JetPullback.ordinary_continuous a L).measurable.comp measurable_snd)
    ((JetPullback.rich_continuous a L).measurable.comp measurable_snd)

variable (P : Policy Seed State (Point d) (OrdinaryReply d) (RichReply d))
    (a : ℝ) (L : Point d →L[ℝ] Point N) {f : Point N → ℝ} (hf : ContDiff ℝ 2 f)

include hf

theorem Policy.linearTransport_run (n : ℕ) (seed : Seed) :
    (P.linearTransport a L).run (ordinaryOracle f) (richOracle f) n seed =
      P.run (ordinaryOracle (JetPullback.scalar a L f)) (richOracle (JetPullback.scalar a L f)) n seed :=
  P.transport_run L _ _ _ _ _ _ _ _ _
    (fun x => (JetPullback.ordinary_exact a L (hf.differentiable (by norm_num)) x).symm)
    (fun x => (JetPullback.rich_exact a L hf x).symm) n seed

theorem Policy.linearTransport_ordinaryCount (n : ℕ) (seed : Seed) :
    (P.linearTransport a L).ordinaryCount (ordinaryOracle f) (richOracle f) n seed =
      P.ordinaryCount (ordinaryOracle (JetPullback.scalar a L f)) (richOracle (JetPullback.scalar a L f)) n seed := by
  simp only [Policy.ordinaryCount, P.linearTransport_run a L hf]
  rfl

theorem Policy.linearTransport_richCount (n : ℕ) (seed : Seed) :
    (P.linearTransport a L).richCount (ordinaryOracle f) (richOracle f) n seed =
      P.richCount (ordinaryOracle (JetPullback.scalar a L f)) (richOracle (JetPullback.scalar a L f)) n seed := by
  simp only [Policy.richCount, P.linearTransport_run a L hf]
  rfl

theorem Policy.linearTransport_hasCaps (G H : ℕ) :
    (P.linearTransport a L).HasCaps (ordinaryOracle f) (richOracle f) G H ↔
      P.HasCaps (ordinaryOracle (JetPullback.scalar a L f)) (richOracle (JetPullback.scalar a L f)) G H := by
  simp only [Policy.HasCaps, P.linearTransport_ordinaryCount a L hf, P.linearTransport_richCount a L hf]

theorem Policy.linearTransport_terminatesAlmostSurely (μ : Measure Seed) :
    (P.linearTransport a L).TerminatesAlmostSurely (ordinaryOracle f) (richOracle f) μ ↔
      P.TerminatesAlmostSurely (ordinaryOracle (JetPullback.scalar a L f))
        (richOracle (JetPullback.scalar a L f)) μ := by
  simp only [Policy.TerminatesAlmostSurely, P.linearTransport_run a L hf]
  rfl

theorem Policy.linearTransport_success (good : Set (Point N)) :
    (P.linearTransport a L).success (ordinaryOracle f) (richOracle f) good =
      P.success (ordinaryOracle (JetPullback.scalar a L f)) (richOracle (JetPullback.scalar a L f)) (L ⁻¹' good) := by
  ext seed
  simp only [Policy.success, Set.mem_setOf_eq, P.linearTransport_run a L hf]
  rfl

theorem Policy.linearTransport_successBy (good : Set (Point N)) (n : ℕ) :
    (P.linearTransport a L).successBy (ordinaryOracle f) (richOracle f) good n =
      P.successBy (ordinaryOracle (JetPullback.scalar a L f)) (richOracle (JetPullback.scalar a L f)) (L ⁻¹' good) n := by
  ext seed
  simp only [Policy.successBy, Set.mem_setOf_eq, P.linearTransport_run a L hf]
  rfl

end GradientHessian.Machine

namespace GradientHessian.Model

def Algorithm.linearTransport {d N : ℕ} (A : Algorithm d) (a : ℝ) (L : Point d →L[ℝ] Point N) : Algorithm N where
  Seed := A.Seed
  State := A.State
  seedSpace := A.seedSpace
  stateSpace := A.stateSpace
  seedLaw := A.seedLaw
  probability := A.probability
  policy := by
    letI := A.seedSpace
    letI := A.stateSpace
    exact A.policy.linearTransport a L

end GradientHessian.Model
