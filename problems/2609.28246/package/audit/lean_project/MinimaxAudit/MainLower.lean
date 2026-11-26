import MinimaxAudit.DeterministicLower
import MinimaxAudit.RandomizedLower
import MinimaxAudit.ErrorMeasurability

/-! The complete lower theorem, with one set of p-only constants for both
criteria and both policy classes. Scalar functions are chosen after the
policy and before the randomized seed is realized. -/
namespace MinimaxAudit
open MeasureTheory
open scoped ENNReal ContDiff
universe u

noncomputable def publicHardRadius (D : ℝ) : ℝ := D / (2 * Real.sqrt 2)

def DeterministicLowerConclusion (p N : ℕ) (L D a b : ℝ)
    (A : DeterministicScalarPolicy p (2*N+2) (2*N+2) N
      (Metric.closedBall 0 (publicHardRadius D)) (Metric.closedBall 0 (publicHardRadius D))) : Prop :=
  ∃ phi : SaddleSpace (2*N+2) (2*N+2) → ℝ,
    AdmissibleScalar p L D (Metric.closedBall 0 (publicHardRadius D))
      (Metric.closedBall 0 (publicHardRadius D)) phi ∧
    ContDiff ℝ ∞ phi ∧
    (∀ y : Dual (2*N+2), ConvexOn ℝ Set.univ (fun x => phi (joinBlocks x y))) ∧
    (∀ x : Primal (2*N+2), ConcaveOn ℝ Set.univ (fun y => phi (joinBlocks x y))) ∧
    (∀ z w, ‖iteratedFDeriv ℝ p phi z - iteratedFDeriv ℝ p phi w‖ ≤ L * ‖z-w‖) ∧
    Metric.diam (productDomain (Metric.closedBall (0 : Primal (2*N+2)) (publicHardRadius D))
      (Metric.closedBall (0 : Dual (2*N+2)) (publicHardRadius D))) = D ∧
    let output := Deterministic.runScalarPolicy A (exactScalarJet p phi) N []
    a * L * D ^ p / (N+1 : ℝ) ^ oracleRateExponent p ≤
      auditedTangentResidual (productDomain (Metric.closedBall 0 (publicHardRadius D))
        (Metric.closedBall 0 (publicHardRadius D))) (scalarSaddleOperator phi) output ∧
    b * L * D ^ (p+1) / (N+1 : ℝ) ^ oracleRateExponent p ≤
      auditedSaddleGap (Metric.closedBall 0 (publicHardRadius D))
        (Metric.closedBall 0 (publicHardRadius D)) (fun x y => phi (joinBlocks x y))
        (primalBlock output) (dualBlock output)

def RandomizedLowerConclusion (p N : ℕ) (L D a b C : ℝ)
    (Seed : Type u) [MeasurableSpace Seed] (mu : Measure Seed)
    (A : RandomizedScalarPolicy p (randomHardDimension N) (randomHardDimension N) N
      (Metric.closedBall 0 (publicHardRadius D)) (Metric.closedBall 0 (publicHardRadius D)) Seed mu) : Prop :=
  ∃ phi : SaddleSpace (randomHardDimension N) (randomHardDimension N) → ℝ,
    AdmissibleScalar p L D (Metric.closedBall 0 (publicHardRadius D))
      (Metric.closedBall 0 (publicHardRadius D)) phi ∧
    ContDiff ℝ ∞ phi ∧
    Metric.diam (productDomain (Metric.closedBall (0 : Primal (randomHardDimension N)) (publicHardRadius D))
      (Metric.closedBall (0 : Dual (randomHardDimension N)) (publicHardRadius D))) = D ∧
    (randomHardDimension N : ℝ) ≤ C * (N+1 : ℝ) ^ 3 * Real.log (N+2 : ℝ) ∧
    MeasurableSet {seed |
      let output := Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) N []
      a * L * D ^ p / (N+1 : ℝ) ^ oracleRateExponent p ≤
        auditedTangentResidual (productDomain (Metric.closedBall 0 (publicHardRadius D))
          (Metric.closedBall 0 (publicHardRadius D))) (scalarSaddleOperator phi) output ∧
      b * L * D ^ (p+1) / (N+1 : ℝ) ^ oracleRateExponent p ≤
        auditedSaddleGap (Metric.closedBall 0 (publicHardRadius D))
          (Metric.closedBall 0 (publicHardRadius D)) (fun x y => phi (joinBlocks x y))
          (primalBlock output) (dualBlock output)} ∧
    (3 / 4 : ℝ≥0∞) ≤ mu {seed |
      let output := Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) N []
      a * L * D ^ p / (N+1 : ℝ) ^ oracleRateExponent p ≤
        auditedTangentResidual (productDomain (Metric.closedBall 0 (publicHardRadius D))
          (Metric.closedBall 0 (publicHardRadius D))) (scalarSaddleOperator phi) output ∧
      b * L * D ^ (p+1) / (N+1 : ℝ) ^ oracleRateExponent p ≤
        auditedSaddleGap (Metric.closedBall 0 (publicHardRadius D))
          (Metric.closedBall 0 (publicHardRadius D)) (fun x y => phi (joinBlocks x y))
          (primalBlock output) (dualBlock output)}

/-- Both parts of the source main theorem. In the random part the same
fixed scalar potential even witnesses both criteria on one event. -/
theorem main_lower_source (p : ℕ) (hp : 2 ≤ p) :
    ∃ a b C : ℝ, 0 < a ∧ 0 < b ∧ 0 < C ∧
      ∀ N : ℕ, 1 ≤ N → ∀ L D : ℝ, 0 < L → 0 < D →
      (∀ A : DeterministicScalarPolicy p (2*N+2) (2*N+2) N
        (Metric.closedBall 0 (publicHardRadius D)) (Metric.closedBall 0 (publicHardRadius D)),
        DeterministicLowerConclusion p N L D a b A) ∧
      (∀ (Seed : Type u) [MeasurableSpace Seed] (mu : Measure Seed)
        (A : RandomizedScalarPolicy p (randomHardDimension N) (randomHardDimension N) N
          (Metric.closedBall 0 (publicHardRadius D)) (Metric.closedBall 0 (publicHardRadius D)) Seed mu),
        RandomizedLowerConclusion p N L D a b C Seed mu A) := by
  refine ⟨tangentRateConstant standardGateProfile p, gapRateConstant standardGateProfile p,
    randomDimensionCoefficient + 8, tangentRateConstant_pos standardGateProfile p,
    gapRateConstant_pos standardGateProfile p, ?_, ?_⟩
  · have h : 0 < randomDimensionCoefficient := by norm_num [randomDimensionCoefficient, geometryEta, geometryKappa]
    linarith
  intro N _ L D hL hD
  constructor
  · intro A
    exact deterministic_lower_global_standard hp hL hD A
  · intro Seed _ mu A
    obtain ⟨U,V,hU,hV,hadm,hdiam,hdim,hprob⟩ := randomized_scalar_lower_bound hp hL hD A
    let R := publicHardRadius D
    let phi := minimaxHardPotential standardGateProfile (hardGateWidth N R)
      (hardAmplitude standardGateProfile p N L R) (balancedQ N) (hardSeed N R) hU hV
    have hR : 0 < R := by dsimp [R, publicHardRadius]; positivity
    have hreg : ContDiff ℝ ∞ phi := (hardInstance_global standardGateProfile hp hL hR hU hV).1
    refine ⟨phi,hadm,hreg,hdiam,hdim,?_,hprob⟩
    let fill : productDomain (Metric.closedBall (0 : Primal (randomHardDimension N)) R)
        (Metric.closedBall (0 : Dual (randomHardDimension N)) R) :=
      ⟨0, source_inner_zero_feasible hR.le (by simp; positivity)⟩
    exact source_joint_error_event_measurable A fill (isCompact_closedBall 0 R)
      (isCompact_closedBall 0 R) ⟨0, by simpa using hR.le⟩ ⟨0, by simpa using hR.le⟩ hreg _ _
end MinimaxAudit
