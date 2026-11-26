import LowRank.GaussianOutputOverlap

/-! The expectation form of the posterior bound, for actual ambient
outputs. Its only remaining random term is the actual normalized query
span's kernel mass; a separate cumulative query estimate is still needed. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

theorem projector_kernel_overlap_integrable {Ω a b : Type*} [MeasurableSpace Ω]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Ω → Matrix a a ℝ) (X : Ω → Matrix a b ℝ)
    (hP : Measurable P) (hX : Measurable X) (hproj : ∀ ω, IsOrthogonalProjector (P ω))
    {ℓ : ℝ} (htrace : ∀ ω, (P ω).trace ≤ ℓ) :
    Integrable (fun ω => (P ω * leftKernelProjector (X ω)).trace) μ := by
  have hK : Measurable (fun ω => leftKernelProjector (X ω)) := measurable_leftKernelProjector.comp hX
  have hm : Measurable (fun ω => (P ω * leftKernelProjector (X ω)).trace) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    fun_prop
  apply (integrable_const ℓ).mono' hm.stronglyMeasurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (projector_overlap_nonneg (hproj ω)
    (leftKernelProjector_isProjector (X ω)))]
  exact (projector_overlap_le (hproj ω) (leftKernelProjector_isProjector (X ω))).trans (htrace ω)

theorem gramOracle_output_overlap_mean_le (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : VisibleOraclePolicy (r + n) r n 0 S)
    (hunit : VisibleOraclePolicy.IsUnit (r + n) r n 0 policy) (hs : s ≤ r)
    {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hO : Measurable O) (hOproj : ∀ h, IsOrthogonalProjector (O h))
    {ℓ : ℝ} (htrace : ∀ h, (O h).trace ≤ ℓ) :
    (∫ p, (O (runGramOracle r s n policy p).1 * leftKernelProjector p.2).trace
      ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) ≤
        2 * (∫ p, gramOracleQueryMass r s n policy p ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) +
          2 * (((r : ℝ) - s) / r) * ℓ := by
  let μ := ν.prod (iidMatrixLaw (r + n) (s + n) v)
  let T := fun p => (runGramOracle r s n policy p).1
  have hm := (measurable_runGramOracle r s n policy).fst.comap_le
  have hc : 0 ≤ 2 * (((r : ℝ) - s) / r) :=
    mul_nonneg (by norm_num) (div_nonneg (sub_nonneg.mpr (by exact_mod_cast hs)) (Nat.cast_nonneg r))
  have hb : ∀ᵐ p ∂μ,
      μ[fun z => (O (T z) * leftKernelProjector z.2).trace | MeasurableSpace.comap T inferInstance] p ≤
        2 * μ[gramOracleQueryMass r s n policy | MeasurableSpace.comap T inferInstance] p +
          2 * (((r : ℝ) - s) / r) * ℓ := by
    filter_upwards [gramOracle_conditional_output_overlap r s n ν policy hunit hs hv O hO hOproj]
      with p hp
    exact hp.trans (add_le_add_left (mul_le_mul_of_nonneg_left (htrace _) hc) _)
  have hi : Integrable (μ[gramOracleQueryMass r s n policy | MeasurableSpace.comap T inferInstance]) μ :=
    integrable_condExp
  have h := integral_mono_ae integrable_condExp ((hi.const_mul 2).add (integrable_const _)) hb
  simp only [Pi.add_apply] at h
  rw [integral_add (hi.const_mul 2) (integrable_const _), integral_const_mul,
    integral_condExp hm, integral_condExp hm] at h
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h

theorem ambientOracle_output_overlap_mean_le (r s n : ℕ) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (policy : AmbientOraclePolicy (r + n) n S)
    (hs : s ≤ r) {v : NNReal} (hv : v ≠ 0)
    (O : OracleHistory (r + n) n S → Matrix (Fin (r + n)) (Fin (r + n)) ℝ)
    (hO : Measurable O) (hOproj : ∀ h, IsOrthogonalProjector (O h))
    {ℓ : ℝ} (htrace : ∀ h, (O h).trace ≤ ℓ) :
    (∫ p, (O (runAmbientGram r s n policy p) * leftKernelProjector p.2).trace
      ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) ≤
        2 * (∫ p, gramOracleQueryMass r s n (normalizedAmbientPolicy r s n policy) p
          ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) +
          2 * (((r : ℝ) - s) / r) * ℓ := by
  have he := ambientOracle_output_recovery_ae r s n ν policy hv O hO
  have hb := gramOracle_output_overlap_mean_le r s n ν (normalizedAmbientPolicy r s n policy)
    (normalizedAmbientPolicy_unit r s n policy) hs hv (O ∘ decodeAmbientHistory r s n policy)
    he.1 (fun h => hOproj _) (fun h => htrace _)
  have hint : (∫ p, (O (runAmbientGram r s n policy p) * leftKernelProjector p.2).trace
      ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) =
      (∫ p, ((O ∘ decodeAmbientHistory r s n policy)
        (runGramOracle r s n (normalizedAmbientPolicy r s n policy) p).1 *
          leftKernelProjector p.2).trace ∂ν.prod (iidMatrixLaw (r + n) (s + n) v)) := by
    apply integral_congr_ae
    filter_upwards [he.2] with p hp
    rw [hp]
  rw [hint]
  exact hb

end
end LowRank
