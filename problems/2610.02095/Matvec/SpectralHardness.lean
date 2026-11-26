import Matvec.PosteriorLowEventBridge
import Matvec.ProductSeparation

/-! Main adaptive spectral-estimation lower bound. The oracle policy and
scalar output are arbitrary measurable maps, with an independent random seed.
The posterior, Gaussian low/high events, and replay are all proved inputs. -/
namespace Matvec
open MeasureTheory Matrix LowRank
noncomputable section
universe u

theorem spectral_failure_of_high_scale (q n : ℕ) (hn : lowEventRank ≤ n)
    (hq : 2 * q ≤ n + 1) {S : Type u} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : TwoSidedOraclePolicy ((q + (n + 1)) + q) ((q + (n + 1)) + q) q S)
    (output : TwoSidedOracleHistory ((q + (n + 1)) + q) ((q + (n + 1)) + q) q S → ℝ)
    (houtput : Measurable output) (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hhigh : ∀ N : ℕ, 0 < N → (1 / 2 : ℝ) ≤
      (iidMatrixLaw N N 1).real {G | b / Real.sqrt N ≤ leastStretch (matrixEuclideanMap G)}) :
    let p := smallBallDensity ^ 2 * (b / 32) ^ 2 / (64 * lowEventRank)
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
  let p := smallBallDensity ^ 2 * a ^ 2 / (64 * lowEventRank)
  letI : IsProbabilityMeasure ρ := iidMatrixLaw_probability _ _ _
  letI : IsProbabilityMeasure (iidMatrixLaw N N 1) := iidMatrixLaw_probability _ _ _
  have hνH : IsProbabilityMeasure νH := by infer_instance
  letI := hνH
  have hN : 0 < N := by dsimp [N, r]; omega
  have hp : 0 < p := by
    have hc := smallBallDensity_pos
    have hr : (0 : ℝ) < lowEventRank := by exact_mod_cast (by
      have := lowEventRank_ge_two; omega : 0 < lowEventRank)
    dsimp [p, a]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hscore : Measurable score := measurable_decodedAmbientScore r q hN policy
  have hestimate : Measurable estimate := houtput.comp
    (measurable_decodeTwoSidedHistory N N r r q policy
      (initialOracleState N N S) (initialOracleMemory S))
  have hT : MeasurePreserving T μ (νH.prod ρ) :=
    runTwoSidedPolicy_preserving r r q ν (compiledAmbientPolicy r r q policy) 1
  have hl : ∀ h, p ≤ ρ.real {D | score (h, D) ≤ 2 * a / Real.sqrt (n + 1 : ℝ)} :=
    fun h => decodedAmbientScore_low q n hn policy h ha ha1
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

/-- `thm:spectral-estimation`: a universal positive failure probability for
factor-two estimation after at most N/8 unrestricted adaptive two-sided
queries, for every sufficiently large square standard Gaussian dimension. -/
theorem adaptive_gaussian_spectral_lower_bound :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t : ℕ, 8 * t ≤ N →
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
  let p := smallBallDensity ^ 2 * (b / 32) ^ 2 / (64 * lowEventRank)
  have hp : 0 < p := by
    have hc := smallBallDensity_pos
    have hr : (0 : ℝ) < lowEventRank := by exact_mod_cast (by
      have := lowEventRank_ge_two; omega : 0 < lowEventRank)
    dsimp [p]; positivity
  refine ⟨p * (1 / 2) / (1 + p), by positivity, 2 * (lowEventRank + 1), ?_⟩
  intro N hN t ht S inst ν hν policy output houtput
  letI := hν
  obtain ⟨n, hdim⟩ : ∃ n, N = (t + (n + 1)) + t := by
    refine ⟨N - 2 * t - 1, ?_⟩
    have := lowEventRank_ge_two
    omega
  subst N
  have hn : lowEventRank ≤ n := by omega
  have hq : 2 * t ≤ n + 1 := by omega
  exact spectral_failure_of_high_scale t n hn hq ν policy output houtput b hb hb1 hhigh'

end
end Matvec
