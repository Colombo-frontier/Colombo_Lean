import MinimaxAudit.MainLower
import MinimaxAudit.RevisedModel

/-! The actual hard-instance lower theorem restricted to the revision's
Borel deterministic policy model. The original unrestricted-map proof is
retained as a stronger reusable theorem. -/
namespace MinimaxAudit
open MeasureTheory
universe u

/-- Revised source main: common p-only constants, exact hard dimensions and
diameter, global smoothness/convexity and true Borel fixed-instance errors. -/
theorem revised_main_lower_source (p : ℕ) (hp : 2 ≤ p) :
    ∃ a b C : ℝ, 0 < a ∧ 0 < b ∧ 0 < C ∧
      ∀ N : ℕ, 1 ≤ N → ∀ L D : ℝ, 0 < L → 0 < D →
      (∀ A : BorelDeterministicScalarPolicy p (2*N+2) (2*N+2) N
        (Metric.closedBall 0 (publicHardRadius D)) (Metric.closedBall 0 (publicHardRadius D)),
        DeterministicLowerConclusion p N L D a b A.policy) ∧
      (∀ (Seed : Type u) [MeasurableSpace Seed] (mu : Measure Seed)
        (A : RandomizedScalarPolicy p (randomHardDimension N) (randomHardDimension N) N
          (Metric.closedBall 0 (publicHardRadius D)) (Metric.closedBall 0 (publicHardRadius D)) Seed mu),
        RandomizedLowerConclusion p N L D a b C Seed mu A) := by
  obtain ⟨a,b,C,ha,hb,hC,h⟩ := main_lower_source.{u} p hp
  refine ⟨a,b,C,ha,hb,hC,?_⟩
  intro N hN L D hL hD
  exact ⟨fun A => (h N hN L D hL hD).1 A.policy, (h N hN L D hL hD).2⟩
end MinimaxAudit
