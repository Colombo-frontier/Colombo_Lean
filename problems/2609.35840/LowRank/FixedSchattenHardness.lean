import LowRank.GaussianSchattenHardness
import LowRank.ProbabilityFixedInput

/-! The averaged Gaussian bound supplies one fixed real symmetric input
matrix against each randomized bounded stopping policy. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

theorem exists_fixed_schatten_input_of_average_bound (r s n k : ℕ) (p L ε : ℝ)
    (hp : 0 < p) (hk : k ≤ r + n)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : BoundedTwoSidedPolicy (r + n) (Matrix (Fin (r + n)) (Fin (r + n)) ℝ) n S)
    (haverage : (ν.prod (gaussianMatrixLaw (r + n) (s + n))).real
      (boundedOptimalSchattenSuccess r s n k p L ε policy) ≤ 3 / 20) :
    ∃ H : Matrix (Fin (r + n)) (Fin (r + n)) ℝ, H.IsHermitian ∧
      ν.real {seed | schattenNorm p (H * (1 - runBoundedTwoSided (r + n) n policy H seed)) ≤
        (1 + ε) * optimalSchattenNorm p H k} < 1 / 5 := by
  obtain ⟨X, hX⟩ := exists_small_section_of_prod_bound ν (gaussianMatrixLaw (r + n) (s + n))
    (measurableSet_boundedOptimalSchattenSuccess r s n k p L ε hp hk policy)
    (by norm_num : (0 : ℝ) ≤ 1 / 5) (by norm_num : (3 / 20 : ℝ) < 1 / 5) haverage
  refine ⟨hardMatrix L (wishart X), ?_, hX⟩
  simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using
    hardMatrix_symmetric L (wishart_symmetric X)

theorem exists_fixed_schatten_input_of_spectral_probability {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k s n : ℕ) (ε : ℝ)
      {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
      (policy : BoundedTwoSidedPolicy (k + s + n)
        (Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ) n S),
      0 < k → 0 ≤ ε → ε ≤ 1 →
      policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank = k) n →
      (n : ℝ) ≤ (k + s + n : ℝ) / 100 → (k : ℝ) ≤ (k + s + n : ℝ) / 100 →
      C * ε * (k + s + n : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4 →
      (ν.prod (gaussianMatrixLaw (k + s + n) (s + n))).real
        {z | z.2 ∉ wishartSpectralEvent (k + s + n) (s + n) L c₀ k} ≤ 1 / 20 →
      ∃ H : Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ, H.IsHermitian ∧
        ν.real {seed | schattenNorm p (H * (1 - runBoundedTwoSided (k + s + n) n policy H seed)) ≤
          (1 + ε) * optimalSchattenNorm p H k} < 1 / 5 := by
  obtain ⟨C, hC, haverage⟩ := exists_gaussian_schatten_success_bound hp hL hc
  refine ⟨C, hC, ?_⟩
  intro k s n ε S _ ν _ policy hk hε hε1 hout hn hkd hsmall hbad
  exact exists_fixed_schatten_input_of_average_bound (k + s) s n k p L ε hp (by omega) ν policy
    (haverage k s n ε ν policy hk hε hε1 hout hn hkd hsmall hbad)

end
end LowRank
