import LeanArticleAudit.Pilot.DeterministicComplexity
import LeanArticleAudit.Pilot.RandomTheorem
import LeanArticleAudit.Pilot.ZeroQuery
import LeanArticleAudit.Pilot.ComplexityOrder

/-!
# Closed lower-bound package

The positive-budget deterministic and randomized obstructions, the zero-query
edge case, and the inclusion of deterministic methods among randomized ones
are bundled here for the final theorem.
-/

namespace LeanArticleAudit.Pilot

/-- All lower-bound clauses needed by `thm:main`, including `N = 0`. -/
def LowerBoundClosureClaim : Prop :=
  DeterministicTheoremClaim.{0} ∧
  RandomTheoremClaim ∧
  ZeroQueryLowerClaim ∧
  RandomizedLeDeterministicClaim.{0}

theorem lowerBoundClosureClaim_proof : LowerBoundClosureClaim :=
  ⟨deterministicTheoremClaim_proof,
    randomTheoremClaim_proof,
    zeroQueryLowerClaim_proof,
    randomizedLeDeterministicClaim_proof⟩

end LeanArticleAudit.Pilot
