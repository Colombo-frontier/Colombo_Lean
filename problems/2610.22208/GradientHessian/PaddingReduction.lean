import GradientHessian.LinearPolicyTransport
import GradientHessian.EuclideanPadding

/-! Exact dimension reduction for arbitrary measurable randomized algorithms.
The seed law and state space are preserved; both query caps remain pathwise. -/

noncomputable section
namespace GradientHessian.Model
open EuclideanPadding
open scoped ENNReal

def Algorithm.paddingReduction {N d : ℕ} (A : Algorithm d) (h : N ≤ d) : Algorithm N :=
  A.linearTransport 1 (projection h)

theorem Algorithm.paddingReduction_guarantees {N d G H : ℕ} {T : ℝ}
    (A : Algorithm d) (h : N ≤ d) (hA : A.Guarantees T G H) :
    (A.paddingReduction h).Guarantees T G H := by
  letI := A.seedSpace
  letI := A.stateSpace
  intro f hf
  obtain ⟨ht, hc, hs⟩ := hA (objective h f) (objective_admissible h hf)
  rw [objective_eq_scalar] at ht hc hs
  refine ⟨?_, ?_, ?_⟩
  · exact (A.policy.linearTransport_terminatesAlmostSurely 1 (projection h) hf.smooth A.seedLaw).mpr ht
  · exact (A.policy.linearTransport_hasCaps 1 (projection h) hf.smooth G H).mpr hc
  · have he := A.policy.linearTransport_success 1 (projection h) hf.smooth (stationary f)
    have hgood : projection h ⁻¹' stationary f = stationary (JetPullback.scalar 1 (projection h) f) := by
      rw [← objective_eq_scalar, objective_stationary h (hf.smooth.differentiable (by norm_num))]
    rw [hgood] at he
    change (2/3 : ℝ≥0∞) ≤ A.seedLaw
      ((A.policy.linearTransport 1 (projection h)).success (ordinaryOracle f) (richOracle f) (stationary f))
    rw [he]
    exact hs

/-- Increasing the ambient dimension cannot decrease the mixed-query
minimax complexity, for the full measurable adaptive algorithm class. -/
theorem complexity_mono_dimension {N d : ℕ} (h : N ≤ d) (H : ℕ) (T : ℝ) :
    complexity H N T ≤ complexity H d T := by
  apply le_iInf
  intro G
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  exact complexity_le (A.paddingReduction h) (A.paddingReduction_guarantees h hA)

end GradientHessian.Model

namespace GradientHessian.Machine
open Model EuclideanPadding

variable {Seed State : Type*} [MeasurableSpace Seed] [MeasurableSpace State] {N d : ℕ}

theorem Policy.padding_run (P : Policy Seed State (Point d) (OrdinaryReply d) (RichReply d))
    (h : N ≤ d) {f : Point N → ℝ} (hf : ContDiff ℝ 2 f) (n : ℕ) (seed : Seed) :
    (P.linearTransport 1 (projection h)).run (ordinaryOracle f) (richOracle f) n seed =
      P.run (ordinaryOracle (objective h f)) (richOracle (objective h f)) n seed := by
  rw [objective_eq_scalar]
  exact P.linearTransport_run 1 (projection h) hf n seed

theorem Policy.padding_output (P : Policy Seed State (Point d) (OrdinaryReply d) (RichReply d))
    (h : N ≤ d) {f : Point N → ℝ} (hf : ContDiff ℝ 2 f) (n : ℕ) (seed : Seed) :
    (P.linearTransport 1 (projection h)).output
        ((P.linearTransport 1 (projection h)).run (ordinaryOracle f) (richOracle f) n seed) =
      projection h (P.output (P.run (ordinaryOracle (objective h f)) (richOracle (objective h f)) n seed)) := by
  rw [P.padding_run h hf n seed]
  rfl

end GradientHessian.Machine
