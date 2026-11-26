import LowRank.FixedSchattenHardness
import LowRank.WishartSpectralMeasurable

/-! The final conditional square-input lower-bound interface: the only
spectral probability premise is on the input Wishart distribution itself. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

theorem exists_fixed_schatten_input_of_wishart_probability {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k s n : ℕ) (ε : ℝ)
      {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
      (policy : BoundedTwoSidedPolicy (k + s + n)
        (Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ) n S),
      0 < k → 0 ≤ ε → ε ≤ 1 →
      policy.Outputs (k + s + n) (fun P => IsOrthogonalProjector P ∧ P.rank = k) n →
      (n : ℝ) ≤ (k + s + n : ℝ) / 100 → (k : ℝ) ≤ (k + s + n : ℝ) / 100 →
      C * ε * (k + s + n : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4 →
      (gaussianMatrixLaw (k + s + n) (s + n)).real
        (wishartSpectralEvent (k + s + n) (s + n) L c₀ k)ᶜ ≤ 1 / 20 →
      ∃ H : Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ, H.IsHermitian ∧
        ν.real {seed | schattenNorm p (H * (1 - runBoundedTwoSided (k + s + n) n policy H seed)) ≤
          (1 + ε) * optimalSchattenNorm p H k} < 1 / 5 := by
  obtain ⟨C, hC, hmain⟩ := exists_fixed_schatten_input_of_spectral_probability hp hL hc
  refine ⟨C, hC, ?_⟩
  intro k s n ε S _ ν _ policy hk hε hε1 hout hn hkd hsmall hbad
  apply hmain k s n ε ν policy hk hε hε1 hout hn hkd hsmall
  rw [wishartSpectralEvent_bad_prod_real]
  exact hbad

end
end LowRank
