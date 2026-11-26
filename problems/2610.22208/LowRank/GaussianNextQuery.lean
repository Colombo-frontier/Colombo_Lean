import LowRank.GaussianOutputOverlap
import LowRank.AdaptedQuadratic

/-! After any completed visible-policy run, a new unit direction chosen
measurably from its real record has conditional nullspace mass at most
(r-s)/r. This proves the local query estimate with the actual input kernel. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators InnerProductSpace
noncomputable section

theorem basis_unit_dot {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r : ℕ}
    (b : OrthonormalBasis (Fin r) ℝ E) (u : Fin r → ℝ)
    (hu : ‖(basisCoordinates b).symm u‖ = 1) : u ⬝ᵥ u = 1 := by
  have h := basisCoordinates_dot b ((basisCoordinates b).symm u) ((basisCoordinates b).symm u)
  simpa only [ContinuousLinearEquiv.apply_symm_apply, real_inner_self_eq_norm_sq, hu, one_pow]
    using h

def gramOracleNextQuery (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (u : OracleHistory (r + n) n S → Fin r → ℝ)
    (p : S × Matrix (Fin (r + n)) (Fin (s + n)) ℝ) : Fin (r + n) → ℝ :=
  ambientQuery (runGramOracle r s n policy p).2 (u (runGramOracle r s n policy p).1)

theorem gramOracleNextQuery_quadratic_ae (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) {v : NNReal} (hv : v ≠ 0)
    (u : OracleHistory (r + n) n S → Fin r → ℝ) :
    ∀ᵐ p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      gramOracleNextQuery r s n policy u p ⬝ᵥ
          (leftKernelProjector p.2 *ᵥ gramOracleNextQuery r s n policy u p) =
        u (runGramOracle r s n policy p).1 ⬝ᵥ
          ((gramOracleKernelCoordinates r s n policy p).submatrix Sum.inr Sum.inr *ᵥ
            u (runGramOracle r s n policy p).1) := by
  filter_upwards [gramOracle_factorization_ae r s n ν policy hunit hv] with p hp
  have hb := congrArg Prod.snd hp.2.2.2
  change (gramOracleFactors r s n policy p).2.1 = (runGramOracle r s n policy p).2.2 at hb
  simp only [gramOracleNextQuery, ambientQuery, ← hb, quadratic_coordinates,
    bottom_quadratic, gramOracleKernelCoordinates]

theorem gramOracle_next_query_conditional_bound (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0)
    (u : OracleHistory (r + n) n S → Fin r → ℝ) (hu : Measurable u)
    (hunorm : ∀ h, ‖(basisCoordinates (EuclideanSpace.basisFun (Fin r) ℝ)).symm (u h)‖ = 1) :
    let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
    let T := fun p => (runGramOracle r s n policy p).1
    ∀ᵐ p ∂μ,
      μ[fun z => gramOracleNextQuery r s n policy u z ⬝ᵥ
        (leftKernelProjector z.2 *ᵥ gramOracleNextQuery r s n policy u z) |
          MeasurableSpace.comap T inferInstance] p ≤ ((r : ℝ) - s) / r := by
  let T := fun p => (runGramOracle r s n policy p).1
  have hm : Measurable[MeasurableSpace.comap T inferInstance] (u ∘ T) :=
    hu.comp (comap_measurable T)
  have hdot : ∀ p, u (T p) ⬝ᵥ u (T p) = 1 := fun p => basis_unit_dot _ _ (hunorm _)
  have he := condExp_adapted_unit_quadratic (MeasurableSpace.comap T inferInstance)
    (ν.prod (iidMatrixLaw (r + n) (s + n) v)) (measurable_runGramOracle r s n policy).fst.comap_le
    (u ∘ T) (fun i => ((measurable_pi_apply i).comp hm).stronglyMeasurable.aestronglyMeasurable)
    (Filter.Eventually.of_forall hdot)
    (fun p => (gramOracleKernelCoordinates r s n policy p).submatrix Sum.inr Sum.inr)
    (fun i j => gramOracleKernelCoordinates_entryIntegrable r s n policy _ (Sum.inr i) (Sum.inr j))
  have hsame := condExp_congr_ae (m := MeasurableSpace.comap T inferInstance)
    (gramOracleNextQuery_quadratic_ae r s n ν policy hunit hv u)
  dsimp only [Function.comp_def, T] at he
  filter_upwards [hsame, he, gramOracleKernelPosterior_bottom_le r s n ν policy hunit hs hv]
    with p hsame he hb
  rw [hsame, he]
  have h := loewner_quadratic_le hb (u (T p))
  simpa only [Matrix.smul_mulVec_assoc, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul, hdot, mul_one, Function.comp_apply] using h

theorem gramOracle_next_query_integrable (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy)
    {v : NNReal} (hv : v ≠ 0)
    (u : OracleHistory (r + n) n S → Fin r → ℝ) (hu : Measurable u)
    (hunorm : ∀ h, ‖(basisCoordinates (EuclideanSpace.basisFun (Fin r) ℝ)).symm (u h)‖ = 1) :
    Integrable (fun p => gramOracleNextQuery r s n policy u p ⬝ᵥ
      (leftKernelProjector p.2 *ᵥ gramOracleNextQuery r s n policy u p))
        (ν.prod (iidMatrixLaw (r + n) (s + n) v)) := by
  have hm := hu.comp (measurable_runGramOracle r s n policy).fst
  have hi := unit_quadratic_integrable (ν.prod (iidMatrixLaw (r + n) (s + n) v))
    (fun p => u (runGramOracle r s n policy p).1)
    (fun i => ((measurable_pi_apply i).comp hm).stronglyMeasurable.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun p => basis_unit_dot _ _ (hunorm _)))
    (fun p => (gramOracleKernelCoordinates r s n policy p).submatrix Sum.inr Sum.inr)
    (fun i j => gramOracleKernelCoordinates_entryIntegrable r s n policy _ (Sum.inr i) (Sum.inr j))
  apply hi.congr
  filter_upwards [gramOracleNextQuery_quadratic_ae r s n ν policy hunit hv u] with p hp
  exact hp.symm

theorem gramOracle_next_query_mean_bound (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0)
    (u : OracleHistory (r + n) n S → Fin r → ℝ) (hu : Measurable u)
    (hunorm : ∀ h, ‖(basisCoordinates (EuclideanSpace.basisFun (Fin r) ℝ)).symm (u h)‖ = 1) :
    (∫ p, gramOracleNextQuery r s n policy u p ⬝ᵥ
      (leftKernelProjector p.2 *ᵥ gramOracleNextQuery r s n policy u p)
        ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) ≤ ((r : ℝ) - s) / r := by
  have h := integral_mono_ae integrable_condExp (integrable_const _)
    (gramOracle_next_query_conditional_bound r s n ν policy hunit hs hv u hu hunorm)
  rw [integral_condExp (measurable_runGramOracle r s n policy).fst.comap_le] at h
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h

end
end LowRank
