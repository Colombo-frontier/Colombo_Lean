import LowRank.GaussianRankHardness

/-! The manuscript's normalized Gaussian range-recovery distribution:
variance 1/d, arbitrary randomized stopping policy, and actual rank-k
projector output. Positive exact-recovery probability forces at least k queries. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem gaussianMatrixLaw_no_exact_range_ae {d k n : ℕ} (hk : k < d) (hn : n < k)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : BoundedTwoSidedPolicy d (Matrix (Fin d) (Fin d) ℝ) n S)
    (hout : policy.Outputs d (fun P => IsOrthogonalProjector P ∧ P.rank = k) n) :
    ∀ᵐ z ∂ν.prod (gaussianMatrixLaw d k),
      wishart z.2 * (1 - runBoundedTwoSided d n policy (wishart z.2) z.1) ≠ 0 := by
  rw [gaussianMatrixLaw_eq_iidMatrixLaw]
  have hv : (d : NNReal)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (show d ≠ 0 by omega))
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hn.le
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' (hn.trans hk).le
  exact stoppingGram_no_exact_range_ae r s n (s + n) (by omega) hk ν policy hout hv

theorem gaussianMatrixLaw_exact_range_probability_zero {d k n : ℕ} (hk : k < d) (hn : n < k)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν]
    (policy : BoundedTwoSidedPolicy d (Matrix (Fin d) (Fin d) ℝ) n S)
    (hout : policy.Outputs d (fun P => IsOrthogonalProjector P ∧ P.rank = k) n) :
    (ν.prod (gaussianMatrixLaw d k)).real
      {z | wishart z.2 * (1 - runBoundedTwoSided d n policy (wishart z.2) z.1) = 0} = 0 := by
  have hnull : (ν.prod (gaussianMatrixLaw d k))
      {z | wishart z.2 * (1 - runBoundedTwoSided d n policy (wishart z.2) z.1) = 0} = 0 := by
    simpa only [ae_iff, not_not] using gaussianMatrixLaw_no_exact_range_ae hk hn ν policy hout
  rw [measureReal_def, hnull, ENNReal.toReal_zero]

theorem exact_gaussian_range_query_lower_bound {d k n : ℕ} (hk : k < d)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy d (Matrix (Fin d) (Fin d) ℝ) n S)
    (hout : policy.Outputs d (fun P => IsOrthogonalProjector P ∧ P.rank = k) n)
    (hsuccess : 0 < (ν.prod (gaussianMatrixLaw d k)).real
      {z | wishart z.2 * (1 - runBoundedTwoSided d n policy (wishart z.2) z.1) = 0}) : k ≤ n := by
  by_contra! hn
  rw [gaussianMatrixLaw_exact_range_probability_zero hk hn ν policy hout] at hsuccess
  exact (lt_irrefl 0) hsuccess

end
end LowRank
