import Matvec.SpectralHardness
import Matvec.GaussianLowAll
import Matvec.MeasurableOracleAdapter

/-! The adaptive spectral lower bound in every positive dimension. The
uniform small-core Gaussian estimate removes the dimension threshold in the
large-dimension proof without changing the N/8 query cap. -/
namespace Matvec
open Matrix MeasureTheory LowRank
open scoped Matrix
noncomputable section
universe u

theorem block_gaussian_leastStretch_low_all (q n : ℕ)
    (A : Matrix (Fin q) (Fin q) ℝ) (B : Matrix (Fin q) (Fin (q + (n + 1))) ℝ)
    (C : Matrix (Fin (q + (n + 1))) (Fin q) ℝ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    gaussianLowProbability a ≤
      (iidMatrixLaw (q + (n + 1)) (q + (n + 1)) 1).real
        {Z | leastStretch (blockEuclideanMap A B C Z) ≤ 2 * a / Real.sqrt (n + 1 : ℝ)} := by
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨δ, hδ, hδsmall, hinv, _⟩ := exists_small_pivot_with_inverse A (div_pos ha hs)
  let C' := C * (A + δ • 1)⁻¹
  let F := lowRankShiftCore C' B
  let μ := iidMatrixLaw (q + (n + 1)) (q + (n + 1)) 1
  haveI : IsProbabilityMeasure μ := iidMatrixLaw_probability _ _ _
  have hF : MeasurePreserving F μ (iidMatrixLaw (n + 1) (n + 1) 1) :=
    lowRankShiftCore_preserving C' B 1
  let E := {D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
    leastStretch (matrixEuclideanMap D) ≤ a / Real.sqrt (n + 1 : ℝ)}
  have hE : MeasurableSet E :=
    measurableSet_le (measurable_matrix_leastStretch _ _ (by omega)) measurable_const
  have hpre := hF.measureReal_preimage hE.nullMeasurableSet
  apply (gaussian_leastStretch_low_all n ha ha1).trans
  rw [← hpre]
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono
  intro Z hZ
  have hc := lowRankShiftCore_leastStretch (q := q) (ℓ := n + 1) (by omega) C' B Z
  have hschur := schur_leastStretch (by omega : 0 < q + (n + 1))
    (A + δ • 1) (A + δ • 1)⁻¹ B C Z hinv
  have hpert := block_leastStretch_perturbation (by omega : 0 < q + (n + 1)) A B C Z δ
  rw [abs_of_pos hδ] at hpert
  change leastStretch (matrixEuclideanMap (F Z)) ≤ a / Real.sqrt (n + 1 : ℝ) at hZ
  change leastStretch (matrixEuclideanMap (Z - C * (A + δ • 1)⁻¹ * B)) ≤
    leastStretch (matrixEuclideanMap (F Z)) at hc
  change leastStretch (blockEuclideanMap A B C Z) ≤ _
  have ht : 2 * a / Real.sqrt (n + 1 : ℝ) =
      a / Real.sqrt (n + 1 : ℝ) + a / Real.sqrt (n + 1 : ℝ) := by ring
  rw [ht]
  linarith

theorem representedTwoSided_gaussian_low_all (q n : ℕ)
    (st : TwoSidedState ((q + (n + 1)) + q) ((q + (n + 1)) + q)
      (q + (n + 1)) (q + (n + 1))) (ho : st.Orthogonal) (hc : st.Centered)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    gaussianLowProbability a ≤
      (iidMatrixLaw (q + (n + 1)) (q + (n + 1)) 1).real
        {D | leastStretch (matrixEuclideanMap (representedTwoSided st D)) ≤
          2 * a / Real.sqrt (n + 1 : ℝ)} := by
  apply (block_gaussian_leastStretch_low_all q n (posteriorVisibleBlocks st).1
    (posteriorVisibleBlocks st).2.1 (posteriorVisibleBlocks st).2.2 ha ha1).trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro D hD
  exact (representedTwoSided_leastStretch_block (by omega) st ho hc D).trans hD

theorem decodedAmbientScore_low_all (q n : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy ((q + (n + 1)) + q) ((q + (n + 1)) + q) q S)
    (h : GaussianHistory (q + (n + 1)) (q + (n + 1)) q S)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    gaussianLowProbability a ≤
      (iidMatrixLaw (q + (n + 1)) (q + (n + 1)) 1).real
        {D | decodedAmbientScore (q + (n + 1)) q policy (h, D) ≤
          2 * a / Real.sqrt (n + 1 : ℝ)} :=
  representedTwoSided_gaussian_low_all q n (decodedAmbientState _ _ _ policy h)
    (decodedAmbientState_orthogonal _ _ _ policy h) (decodedAmbientState_centered _ _ _ policy h)
    ha ha1

theorem spectral_failure_of_high_scale_all (q n : ℕ) (hq : 2 * q ≤ n + 1)
    {S : Type u} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : TwoSidedOraclePolicy ((q + (n + 1)) + q) ((q + (n + 1)) + q) q S)
    (output : TwoSidedOracleHistory ((q + (n + 1)) + q) ((q + (n + 1)) + q) q S → ℝ)
    (houtput : Measurable output) (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hhigh : ∀ N : ℕ, 0 < N → (1 / 2 : ℝ) ≤
      (iidMatrixLaw N N 1).real {G | b / Real.sqrt N ≤ leastStretch (matrixEuclideanMap G)}) :
    let p := gaussianLowProbability (b / 32)
    p * (1 / 2) / (1 + p) ≤
      (ν.prod (iidMatrixLaw ((q + (n + 1)) + q) ((q + (n + 1)) + q) 1)).real
        {x | output (runTwoSidedOracle _ _ q policy x.2 x.1) ∉
          Set.Icc (leastStretch (matrixEuclideanMap x.2) / 2)
            (2 * leastStretch (matrixEuclideanMap x.2))} := by
  let r := q + (n + 1)
  let N := r + q
  let μ := ν.prod (iidMatrixLaw N N 1)
  let νH := gaussianHistoryLaw r r q ν 1
  let ρ := iidMatrixLaw r r 1
  let T := runTwoSidedPolicy r r q (compiledAmbientPolicy r r q policy)
  let score := decodedAmbientScore r q policy
  let estimate := output ∘ decodeAmbientTwoSided r r q policy
  let a := b / 32
  let p := gaussianLowProbability a
  letI : IsProbabilityMeasure ρ := iidMatrixLaw_probability _ _ _
  letI : IsProbabilityMeasure (iidMatrixLaw N N 1) := iidMatrixLaw_probability _ _ _
  have hνH : IsProbabilityMeasure νH := by infer_instance
  letI := hνH
  have hN : 0 < N := by dsimp [N, r]; omega
  have ha : 0 < a := by dsimp [a]; positivity
  have hp : 0 < p := gaussianLowProbability_pos ha
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hscore : Measurable score := measurable_decodedAmbientScore r q hN policy
  have hestimate : Measurable estimate := houtput.comp
    (measurable_decodeTwoSidedHistory N N r r q policy
      (initialOracleState N N S) (initialOracleMemory S))
  have hT : MeasurePreserving T μ (νH.prod ρ) :=
    runTwoSidedPolicy_preserving r r q ν (compiledAmbientPolicy r r q policy) 1
  have hl : ∀ h, p ≤ ρ.real {D | score (h, D) ≤ 2 * a / Real.sqrt (n + 1 : ℝ)} :=
    fun h => decodedAmbientScore_low_all q n policy h ha ha1
  have hhigh' : (1 / 2 : ℝ) ≤ μ.real {x | b / Real.sqrt N ≤ score (T x)} := by
    have heq : {x : S × Matrix (Fin N) (Fin N) ℝ | b / Real.sqrt N ≤ score (T x)} =
        Set.univ ×ˢ {G | b / Real.sqrt N ≤ leastStretch (matrixEuclideanMap G)} := by
      ext x
      simp only [score, T, decodedAmbientScore_replay, Set.mem_setOf_eq, Set.mem_prod,
        Set.mem_univ, true_and]
    rw [heq, measureReal_prod_prod, measureReal_univ_eq_one, one_mul]
    exact hhigh N hN
  have hsL : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hratio : Real.sqrt (N : ℝ) ≤ 2 * Real.sqrt (n + 1 : ℝ) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hNR : (N : ℝ) ≤ 4 * (n + 1 : ℝ) := by
      have hqR : 2 * (q : ℝ) ≤ n + 1 := by exact_mod_cast hq
      dsimp [N, r]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)]
  have hsep : 2 * (2 * a / Real.sqrt (n + 1 : ℝ)) < (b / Real.sqrt N) / 2 := by
    have heq : 2 * (2 * a / Real.sqrt (n + 1 : ℝ)) = b / (8 * Real.sqrt (n + 1 : ℝ)) := by
      dsimp [a]; ring
    rw [heq, div_div]
    exact div_lt_div_of_pos_left hb (by positivity) (by nlinarith)
  have h := preserving_product_spectral_failure μ νH ρ T hT score estimate hscore hestimate
    (2 * a / Real.sqrt (n + 1 : ℝ)) (b / Real.sqrt N) ((b / Real.sqrt N) / 2)
    p (1 / 2) hp.le hsep le_rfl hl hhigh'
  simpa only [estimate, Function.comp_apply, T, score, decodedAmbientScore_replay,
    ambientTwoSided_replay, ambientTwoSidedRecord] using h

/-- The manuscript's spectral theorem with its full positive-dimension
quantifier and original one-eighth query cap. -/
theorem adaptive_gaussian_spectral_lower_bound_all_dimensions :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, 0 < N → ∀ t : ℕ, 8 * t ≤ N →
      ∀ (S : Type u) [MeasurableSpace S] (ν : Measure S), IsProbabilityMeasure ν →
      ∀ (policy : TwoSidedOraclePolicy N N t S)
        (output : TwoSidedOracleHistory N N t S → ℝ), Measurable output →
      γ ≤ (ν.prod (iidMatrixLaw N N 1)).real
        {x | output (runTwoSidedOracle N N t policy x.2 x.1) ∉
          Set.Icc (leastStretch (matrixEuclideanMap x.2) / 2)
            (2 * leastStretch (matrixEuclideanMap x.2))} := by
  obtain ⟨b, hb, hb1, hhigh⟩ := gaussian_reliable_high_scale (1 / 2) (by norm_num)
  have hhigh' : ∀ N : ℕ, 0 < N → (1 / 2 : ℝ) ≤
      (iidMatrixLaw N N 1).real {G | b / Real.sqrt N ≤ leastStretch (matrixEuclideanMap G)} := by
    intro N hN
    cases N with
    | zero => omega
    | succ n =>
      have h := hhigh n
      norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
      simpa only [Nat.cast_succ] using h
  let p := gaussianLowProbability (b / 32)
  have hp : 0 < p := gaussianLowProbability_pos (by positivity)
  refine ⟨p * (1 / 2) / (1 + p), by positivity, ?_⟩
  intro N hN t ht S inst ν hν policy output houtput
  letI := hν
  obtain ⟨n, hdim⟩ : ∃ n, N = (t + (n + 1)) + t := by
    refine ⟨N - 2 * t - 1, ?_⟩
    omega
  subst N
  have hq : 2 * t ≤ n + 1 := by omega
  exact spectral_failure_of_high_scale_all t n hq ν policy output houtput b hb hb1 hhigh'

/-- Equivalent ordinary finite-transcript interface, with exactly the same
query horizon and the same every-positive-dimension guarantee. -/
theorem adaptive_gaussian_policy_spectral_lower_bound_all_dimensions :
    ∃ γ : ℝ, 0 < γ ∧ ∀ N : ℕ, 0 < N → ∀ t : ℕ, 8 * t ≤ N →
      ∀ (S : Type u) [MeasurableSpace S] (ν : Measure S), IsProbabilityMeasure ν →
      ∀ (alg : MeasurableSimulation.Policy (AmbientQuery N N) (AmbientQuery N N) ℝ t S),
      γ ≤ (ν.prod (iidMatrixLaw N N 1)).real
        {x | alg.run (fun q => (x.2 *ᵥ q.2, x.2ᵀ *ᵥ q.1)) x.1 ∉
          Set.Icc (leastStretch (matrixEuclideanMap x.2) / 2)
            (2 * leastStretch (matrixEuclideanMap x.2))} := by
  obtain ⟨γ, hγ, h⟩ := adaptive_gaussian_spectral_lower_bound_all_dimensions.{u}
  refine ⟨γ, hγ, ?_⟩
  intro N hN t ht S inst ν hν alg
  have hh := h N hN t ht S ν hν (alg.toTwoSided t) (alg.nestedOutput t)
    (alg.measurable_nestedOutput t)
  simpa only [MeasurableSimulation.Policy.toTwoSided_replay] using hh

end
end Matvec
