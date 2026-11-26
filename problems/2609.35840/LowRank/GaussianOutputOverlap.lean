import LowRank.GaussianPosteriorTrace

/-! Connect the posterior trace bound to a measurable output of the real
oracle record. The output is an ambient projector; its query coordinates
are proved adapted almost surely using the visible-factor replay theorem. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

theorem trace_coordinates {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    (B : Matrix a b ℝ) (hB : B * Bᵀ = 1) (P : Matrix a a ℝ) :
    (Bᵀ * P * B).trace = P.trace := by
  rw [Matrix.trace_mul_cycle, hB, Matrix.one_mul]

theorem trace_mul_coordinates {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
    (B : Matrix a b ℝ) (hB : B * Bᵀ = 1) (P K : Matrix a a ℝ) :
    ((Bᵀ * P * B) * (Bᵀ * K * B)).trace = (P * K).trace := by
  have he : (Bᵀ * P * B) * (Bᵀ * K * B) = Bᵀ * (P * K) * B := by
    calc
      _ = Bᵀ * P * (B * Bᵀ) * K * B := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hB]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [he]
  exact trace_coordinates B hB (P * K)

def gramOracleOutputCoordinates (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (O : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) :=
  (gramOracleFactors r s n policy p).2.1ᵀ * O (runGramOracle r s n policy p).1 *
    (gramOracleFactors r s n policy p).2.1

theorem gramOracleOutputCoordinates_adapted (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hO : Measurable O) :
    ∀ i j, AEStronglyMeasurable[
      MeasurableSpace.comap (fun p => (runGramOracle r s n policy p).1) inferInstance]
        (fun p => gramOracleOutputCoordinates r s n policy O p i j)
        (ν.prod (iidMatrixLaw (r + n) (s + n) v)) := by
  let T := fun p => (runGramOracle r s n policy p).1
  let B := fun p => (runGramOracle r s n policy p).2.2
  have hB : Measurable[MeasurableSpace.comap T inferInstance] B :=
    (gramOracle_visible_measurable_transcript r s n policy).snd
  have ho : Measurable[MeasurableSpace.comap T inferInstance] (O ∘ T) :=
    hO.comp (comap_measurable T)
  have he : gramOracleOutputCoordinates r s n policy O =ᵐ[ν.prod (iidMatrixLaw (r + n) (s + n) v)]
      (fun p => (B p)ᵀ * O (T p) * B p) := by
    filter_upwards [gramOracle_factorization_ae r s n ν policy hunit hv] with p hp
    have hb := congrArg Prod.snd hp.2.2.2
    change (gramOracleFactors r s n policy p).2.1 = B p at hb
    simp only [gramOracleOutputCoordinates, hb, T]
  intro i j
  have hc : Measurable[MeasurableSpace.comap T inferInstance]
      (fun p => ((B p)ᵀ * O (T p) * B p) i j) := by
    change Measurable[MeasurableSpace.comap T inferInstance]
      (fun p => ((B p)ᵀ * (O ∘ T) p * B p) i j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.measurable_sum
    intro x _
    apply Measurable.mul
    · apply Finset.measurable_sum
      intro y _
      exact ((measurable_pi_apply i).comp ((measurable_pi_apply y).comp hB)).mul
        ((measurable_pi_apply x).comp ((measurable_pi_apply y).comp ho))
    · exact (measurable_pi_apply j).comp ((measurable_pi_apply x).comp hB)
  apply hc.stronglyMeasurable.aestronglyMeasurable.congr
  filter_upwards [he] with p hp
  exact (congrFun (congrFun hp i) j).symm

theorem gramOracle_conditional_output_overlap (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hO : Measurable O) (hOproj : ∀ h, IsOrthogonalProjector (O h)) :
    let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
    let T := fun p => (runGramOracle r s n policy p).1
    ∀ᵐ p ∂μ,
      μ[fun z => (O (T z) * leftKernelProjector z.2).trace |
        MeasurableSpace.comap T inferInstance] p ≤
          2 * μ[gramOracleQueryMass r s n policy | MeasurableSpace.comap T inferInstance] p +
            2 * (((r : ℝ) - s) / r) * (O (T p)).trace := by
  have hP : ∀ p, IsOrthogonalProjector (gramOracleOutputCoordinates r s n policy O p) :=
    fun p => (hOproj _).coordinates _ (gramOracleFactors_orthogonal r s n policy p).2.1
  have he : (fun p => (gramOracleOutputCoordinates r s n policy O p *
      gramOracleKernelCoordinates r s n policy p).trace) =
      (fun p => (O (runGramOracle r s n policy p).1 * leftKernelProjector p.2).trace) := by
    funext p
    exact trace_mul_coordinates _ (gramOracleFactors_orthogonal r s n policy p).2.1 _ _
  have hb := gramOracle_conditional_overlap_coordinates r s n ν policy hunit hs hv
    (gramOracleOutputCoordinates r s n policy O)
    (gramOracleOutputCoordinates_adapted r s n ν policy hunit hv O hO)
    (Filter.Eventually.of_forall hP)
  dsimp only at hb ⊢
  rw [he] at hb
  filter_upwards [hb] with p hp
  have ht : (gramOracleOutputCoordinates r s n policy O p).trace =
      (O (runGramOracle r s n policy p).1).trace :=
    trace_coordinates _ (gramOracleFactors_orthogonal r s n policy p).2.1 _
  rwa [ht] at hp

end
end LowRank
