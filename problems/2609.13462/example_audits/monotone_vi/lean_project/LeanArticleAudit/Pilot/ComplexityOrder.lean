import LeanArticleAudit.Pilot.Model

/-!
# Deterministic algorithms as randomized algorithms

This is the formal content of the middle inequality
`T_rand ≤ T_det`: a deterministic policy is the singleton-seed special case
of a randomized one, with exactly the same query cap and output.
-/

open Set MeasureTheory
open scoped ENNReal

namespace LeanArticleAudit.Pilot

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Promote a deterministic policy without changing its strategy tree. -/
def DeterministicPolicy.asRandomized (data : VIPublicData E) (budget : ℕ)
    (policy : DeterministicPolicy data.X (ExactJet E data.p) budget) :
    RandomizedPolicy.{u, 0} data budget where
  Seed := PUnit
  seedMeasurable := ⊤
  seedMeasure := Measure.dirac PUnit.unit
  seedProbability := by simp
  choose := fun _ ↦ policy

theorem deterministicUniformSuccess_to_randomized
    (data : VIPublicData E) (budget : ℕ)
    (policy : DeterministicPolicy data.X (ExactJet E data.p) budget)
    (epsilon : ℝ)
    (hsuccess : DeterministicUniformSuccess data budget policy epsilon) :
    RandomizedUniformSuccess data budget
      (policy.asRandomized data budget) epsilon := by
  intro F hF
  have hpoint := hsuccess F hF
  let randomized := policy.asRandomized data budget
  letI : MeasurableSpace randomized.Seed := randomized.seedMeasurable
  have hevent :
      {xi : randomized.Seed | tangentResidual data F
        ((randomized.choose xi).run (exactJet data.p F) : E) ≤ epsilon} =
        Set.univ := by
    ext xi
    simp [randomized, DeterministicPolicy.asRandomized, hpoint]
  constructor
  · change MeasurableSet
      {xi : randomized.Seed | tangentResidual data F
        ((randomized.choose xi).run (exactJet data.p F) : E) ≤ epsilon}
    rw [hevent]
    exact MeasurableSet.univ
  · change (2 / 3 : ENNReal) ≤ randomized.seedMeasure
      {xi : randomized.Seed | tangentResidual data F
        ((randomized.choose xi).run (exactJet data.p F) : E) ≤ epsilon}
    rw [hevent, randomized.seedProbability]
    calc
      (2 / 3 : ENNReal) ≤ 3 / 3 :=
        ENNReal.div_le_div_right (by norm_num : (2 : ENNReal) ≤ 3) 3
      _ = 1 := ENNReal.div_self (by norm_num) (by norm_num)

/-- Audit-facing operational form of `T_rand ≤ T_det`. -/
def RandomizedLeDeterministicClaim : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (budget : ℕ)
    (policy : DeterministicPolicy data.X (ExactJet E data.p) budget)
    (epsilon : ℝ),
    DeterministicUniformSuccess data budget policy epsilon →
    RandomizedUniformSuccess data budget
      (policy.asRandomized data budget) epsilon

theorem randomizedLeDeterministicClaim_proof : RandomizedLeDeterministicClaim := by
  intro E _ _ _ data budget policy epsilon hsuccess
  exact deterministicUniformSuccess_to_randomized data budget policy epsilon hsuccess

end

end LeanArticleAudit.Pilot
