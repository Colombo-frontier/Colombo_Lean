import NCConcave16991.ConditionalHaarConeBadCorrectness
import NCConcave16991.ConeHaarFamily
import NCConcave16991.LowerYao
import NCConcave16991.TheoremStatements

/-! # The unrestricted randomized normalized cone lower bound

The finite ambient dimension is chosen before the uniform policy, while the
static independent Haar matrices are sampled afterwards. Every law and every
problem in the product-law contradiction is the actual constructed object.
-/

open Set MeasureTheory
open scoped ENNReal

namespace NCConcave16991.ConeLower

noncomputable section

open Haar Haar.ConeMachine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem normalized_randomized_lower (n : ℕ) (hn : 0 < n) (M : ℕ) (R q : ℝ)
    (hR : 1 ≤ R) (hq : 16 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R)
    (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2) :
    LowerBudgetBound (normalizedParameters n hn M R (by linarith) q (by linarith))
      .individual ((n : ℝ) * (M + 1 : ℕ) / 4096) := by
  intro T hvalid
  by_contra hT
  have hbudget : (T : ℝ) < (n : ℝ) * (M + 1 : ℕ) / 4096 := lt_of_not_ge hT
  let k := hardDimension n M T
  let e : Fin n ↪ Fin k := hardEmbedding n M T
  have hR0 : 0 < R := by linarith
  obtain ⟨A, hA⟩ := hvalid (ConeProblem.primalDimension (FrameSpace k) M)
    (ConeProblem.dualDimension (FrameSpace k) M) (Domain (FrameSpace k) M R hR0) 0
  letI : MeasurableSpace A.Seed := A.seedSpace
  letI : IsProbabilityMeasure A.law := A.law_probability
  let family := fun Q : Fin (M + 1) → OrthogonalGroup k ↦ actualProblem k n M R hR0 hn q hq e Q
  let success := fun Q : Fin (M + 1) → OrthogonalGroup k ↦
    {seed : A.Seed | StationaryOutput (family Q)
      (OraclePolicy.run (Domain (FrameSpace k) M R hR0) A.policy (oracleResponse (family Q)) seed T).1}
  have hsuccess (Q : Fin (M + 1) → OrthogonalGroup k) :
      (2 / 3 : ℝ≥0∞) ≤ A.law (success Q) := by
    apply (hA (family Q) rfl ?_).2
    exact ConeSmooth.problem_individualSmooth hn hR hq hrel hq2
      (fun i j ↦ frameRows k n M e Q j i) (frameRows_orthonormal k n M e Q)
  let B := badEvent k n M R hR0 A.policy hn q e T
  have hB : MeasurableSet B := badEvent_measurable k n M R hR0 A.policy hn q e T
  have hsub (Q : Fin (M + 1) → OrthogonalGroup k) :
      success Q ⊆ {seed | (seed, Q) ∈ B} := by
    intro seed hs
    exact stationary_implies_badEvent k n M R hR0 A.policy seed hn q hR hq hrel hq2 e Q T hbudget hs
  have hlarge := seed_prior_bad_mass_lower (rotationLaw k (M + 1)) A.law B hB success hsuccess hsub
  have hsmall : (A.law.prod (rotationLaw k (M + 1))).real B ≤ 1 / 6 :=
    badEvent_mass_le_one_sixth k n M R hR0 A.policy A.law hn q e T
      (hardDimension_gt_budget n M T) (hardDimension_gap n M T)
  have hlargeR := ENNReal.toReal_mono (measure_ne_top (A.law.prod (rotationLaw k (M + 1))) B) hlarge
  change (2 / 3 : ℝ≥0∞).toReal ≤ (A.law.prod (rotationLaw k (M + 1))).real B at hlargeR
  norm_num at hlargeR
  linarith

end

end NCConcave16991.ConeLower
