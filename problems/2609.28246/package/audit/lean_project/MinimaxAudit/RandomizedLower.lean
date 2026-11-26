import MinimaxAudit.Randomized
import MinimaxAudit.RandomDimension
import MinimaxAudit.LowerScaling
import MinimaxAudit.SourceGap

/-!
# Actual randomized scalar minimax lower bound

The frame is fixed independently of the realized seed. Admissibility,
product-ball geometry, full-jet replay, measurable adapted execution, and both
error obstructions are proved for the same concrete scalar potential.
-/
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace MinimaxAudit
open Deterministic Randomized
noncomputable section
set_option maxHeartbeats 1000000

variable {N d p : ℕ} {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}

/-- Finite-budget random lower bound at any explicitly sufficient ambient
dimension. No oracle, transcript, error, or admissibility certificate is a
hypothesis: only source public parameters and the actual randomized policy. -/
theorem randomized_scalar_lower_sufficient_dimension
    (profile : GateProfile) (hp : 2 ≤ p) {L R : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hnd : N + 1 < d)
    (A : RandomizedScalarPolicy p d d N (Metric.closedBall 0 R) (Metric.closedBall 0 R) Seed mu)
    (hdim : 2 * R ^ 2 / (hardGateWidth N R / (8 * Real.sqrt 2)) ^ 2 *
      Real.log (8 * (((N + 1) * (N + 2) : ℕ) : ℝ)) ≤ ((d - (N + 1) : ℕ) : ℝ)) :
    ∃ (U : Fin (N + 1) → Primal d) (V : Fin (N + 1) → Dual d),
      ∃ (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V),
      let phi := minimaxHardPotential profile (hardGateWidth N R) (hardAmplitude profile p N L R)
        (balancedQ N) (hardSeed N R) hU hV
      AdmissibleScalar p L (2 * Real.sqrt 2 * R)
        (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R) phi ∧
      (3 / 4 : ℝ≥0∞) ≤ mu {seed |
        let output := runScalarPolicy (A.policy seed) (exactScalarJet p phi) N []
        hardAmplitude profile p N L R * hardSeed N R / (2 * Real.sqrt (N + 1)) ≤
          auditedTangentResidual
            (productDomain (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R))
            (scalarSaddleOperator phi) output ∧
        hardAmplitude profile p N L R * hardSeed N R ^ 2 / 16 ≤
          auditedSaddleGap (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R)
            (fun x y => phi (joinBlocks x y)) (primalBlock output) (dualBlock output)} := by
  let fill : productDomain (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R) :=
    ⟨0, source_inner_zero_feasible hR.le (by simp; positivity)⟩
  let tau := hardGateWidth N R
  let lam := hardAmplitude profile p N L R
  let c := hardSeed N R
  have htau : 0 < tau := hardGateWidth_pos N hR
  have hlam : 0 < lam := hardAmplitude_pos profile p N hL hR
  obtain ⟨U, V, hU, hV, hprob⟩ := exists_randomized_fixed_pair_output_slabs hnd hR
    A fill profile htau lam c (balancedQ N) hdim
  let phi := minimaxHardPotential profile tau lam (balancedQ N) c hU hV
  have hphi : hardPotential profile tau lam c (balancedQ N) U V = phi :=
    deterministic_potential_eq profile tau lam c (balancedQ N) hU hV
  rw [hphi] at hprob
  refine ⟨U, V, hU, hV, hardInstance_admissible profile hp hL hR hU hV, ?_⟩
  apply hprob.trans
  apply measure_mono
  intro seed hseed
  let output := runScalarPolicy (A.policy seed) (exactScalarJet p phi) N []
  have hcoord : |pairedA U V (Fin.last N) output| ≤ tau := by
    have hsmall : |pairedA U V (Fin.last N) output| ≤ tau / 8 := hseed.1
    exact hsmall.trans (by linarith)
  have hfeasible := runScalarPolicy_feasible (A.policy seed) (exactScalarJet p phi) N []
  exact ⟨source_tangent_residual_lower hU hV profile htau hlam hR rfl rfl output hfeasible hcoord,
    source_product_gap_lower hU hV profile htau hlam hR rfl rfl output hfeasible hcoord⟩

/-- Main randomized scalar minimax lower bound with the public diameter D,
a concrete integer dimension O((N+1)^3 log(N+2)), and constants depending only
on p through a fixed concrete smooth cutoff. Both criteria hold on the same
fixed instance with probability at least 3/4. -/
theorem randomized_scalar_lower_bound
    (hp : 2 ≤ p) {L D : ℝ} (hL : 0 < L) (hD : 0 < D)
    (A : RandomizedScalarPolicy p (randomHardDimension N) (randomHardDimension N) N
      (Metric.closedBall 0 (D / (2 * Real.sqrt 2)))
      (Metric.closedBall 0 (D / (2 * Real.sqrt 2))) Seed mu) :
    ∃ (U : Fin (N + 1) → Primal (randomHardDimension N))
      (V : Fin (N + 1) → Dual (randomHardDimension N)),
      ∃ (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V),
      let R := D / (2 * Real.sqrt 2)
      let phi := minimaxHardPotential standardGateProfile (hardGateWidth N R)
        (hardAmplitude standardGateProfile p N L R) (balancedQ N) (hardSeed N R) hU hV
      AdmissibleScalar p L D
        (Metric.closedBall (0 : Primal (randomHardDimension N)) R)
        (Metric.closedBall (0 : Dual (randomHardDimension N)) R) phi ∧
      Metric.diam (productDomain
        (Metric.closedBall (0 : Primal (randomHardDimension N)) R)
        (Metric.closedBall (0 : Dual (randomHardDimension N)) R)) = D ∧
      (randomHardDimension N : ℝ) ≤
        (randomDimensionCoefficient + 8) * (N + 1 : ℝ) ^ 3 * Real.log (N + 2 : ℝ) ∧
      (3 / 4 : ℝ≥0∞) ≤ mu {seed |
        let output := runScalarPolicy (A.policy seed) (exactScalarJet p phi) N []
        tangentRateConstant standardGateProfile p * L * D ^ p /
          (N + 1 : ℝ) ^ oracleRateExponent p ≤
          auditedTangentResidual
            (productDomain (Metric.closedBall (0 : Primal (randomHardDimension N)) R)
              (Metric.closedBall (0 : Dual (randomHardDimension N)) R))
            (scalarSaddleOperator phi) output ∧
        gapRateConstant standardGateProfile p * L * D ^ (p + 1) /
          (N + 1 : ℝ) ^ oracleRateExponent p ≤
          auditedSaddleGap
            (Metric.closedBall (0 : Primal (randomHardDimension N)) R)
            (Metric.closedBall (0 : Dual (randomHardDimension N)) R)
            (fun x y => phi (joinBlocks x y)) (primalBlock output) (dualBlock output)} := by
  let R := D / (2 * Real.sqrt 2)
  have hR : 0 < R := by dsimp [R]; positivity
  have hdiam : 2 * Real.sqrt 2 * R = D := by
    dsimp [R]
    have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  obtain ⟨U, V, hU, hV, hadmissible, hprob⟩ :=
    randomized_scalar_lower_sufficient_dimension standardGateProfile hp hL hR
      (randomHardDimension_gt N) A (randomHardDimension_source_sufficient N hR)
  refine ⟨U, V, hU, hV, ?_, ?_, randomHardDimension_upper N, ?_⟩
  · simpa only [hdiam] using hadmissible
  · simpa only [hdiam] using productBall_diameter_exact hR.le hU hV
  · simpa only [R, hard_tangent_scale standardGateProfile hp N L D,
      hard_gap_scale standardGateProfile hp N L D] using hprob

end
end MinimaxAudit
