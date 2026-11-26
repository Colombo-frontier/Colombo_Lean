import LowRank.GaussianStoppingRange
import LowRank.SchattenExactRecovery
import LowRank.GaussianFullRank

/-! Unconditional rank baseline: fewer than k queries cannot attain a
relative Schatten guarantee on every rank-k positive semidefinite input.
For each randomized policy a fixed rank-k input has success probability zero. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem stoppingGram_schatten_failure_ae (r s n : ℕ) (hs : 0 < s) (hk : s + n < r + n)
    {p ε : ℝ} (hp : 0 < p) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν]
    (policy : BoundedTwoSidedPolicy (r + n)
      (Matrix (Fin (r + n)) (Fin (r + n)) ℝ) n S)
    (hout : policy.Outputs (r + n) (fun P => IsOrthogonalProjector P ∧ P.rank = s + n) n)
    {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ z ∂ν.prod (iidMatrixLaw (r + n) (s + n) v),
      ¬ schattenNorm p ((z.2 * z.2ᵀ) * (1 - runBoundedTwoSided (r + n) n policy
        (z.2 * z.2ᵀ) z.1)) ≤ (1 + ε) * optimalSchattenNorm p (z.2 * z.2ᵀ) (s + n) := by
  filter_upwards [stoppingGram_no_exact_range_ae r s n (s + n) hs hk ν policy hout hv] with z hz
  exact fun he => hz (relative_gram_schatten_implies_exact hp z.2 hk.le _ he)

theorem exists_fixed_gram_input_zero_success (r s n : ℕ) (hs : 0 < s) (hk : s + n < r + n)
    {p ε : ℝ} (hp : 0 < p) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy (r + n)
      (Matrix (Fin (r + n)) (Fin (r + n)) ℝ) n S)
    (hout : policy.Outputs (r + n) (fun P => IsOrthogonalProjector P ∧ P.rank = s + n) n) :
    ∃ W : Matrix (Fin (r + n)) (Fin (r + n)) ℝ, W.PosSemidef ∧ W.rank = s + n ∧
      ν.real {seed | schattenNorm p (W * (1 - runBoundedTwoSided (r + n) n policy W seed)) ≤
        (1 + ε) * optimalSchattenNorm p W (s + n)} = 0 := by
  have hfail := stoppingGram_schatten_failure_ae r s n hs hk (ε := ε) hp ν policy hout
    (by norm_num : (1 : NNReal) ≠ 0)
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hfail
  have hsections := Measure.ae_ae_of_ae_prod hswap
  obtain ⟨X, hX, hrank⟩ := (hsections.and (iidMatrixLaw_wishart_rank_ae (r + n) (s + n)
    hk.le (by norm_num : (1 : NNReal) ≠ 0))).exists
  refine ⟨wishart X, wishart_posSemidef X, hrank, ?_⟩
  have hnull : ν {seed | schattenNorm p (wishart X *
      (1 - runBoundedTwoSided (r + n) n policy (wishart X) seed)) ≤
        (1 + ε) * optimalSchattenNorm p (wishart X) (s + n)} = 0 := by
    simpa only [ae_iff, not_not, wishart] using hX
  rw [measureReal_def, hnull, ENNReal.toReal_zero]

theorem exists_fixed_rank_input_zero_success {d k n : ℕ} (hk : k < d) (hn : n < k)
    {p ε : ℝ} (hp : 0 < p) {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy d (Matrix (Fin d) (Fin d) ℝ) n S)
    (hout : policy.Outputs d (fun P => IsOrthogonalProjector P ∧ P.rank = k) n) :
    ∃ W : Matrix (Fin d) (Fin d) ℝ, W.PosSemidef ∧ W.rank = k ∧
      ν.real {seed | schattenNorm p (W * (1 - runBoundedTwoSided d n policy W seed)) ≤
        (1 + ε) * optimalSchattenNorm p W k} = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hn.le
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' (hn.trans hk).le
  exact exists_fixed_gram_input_zero_success r s n (by omega) hk hp ν policy hout

end
end LowRank
