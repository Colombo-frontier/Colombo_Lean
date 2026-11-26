import LowRank.RectangularColumnReduction
import LowRank.RectangularSchattenSuccess
import LowRank.WishartHardnessInterface

/-! The conditional fixed-input Schatten lower bound for arbitrary
rectangular stopping policies. Padding, measurable output conversion,
and query simulation are proved, leaving only the explicit Wishart
spectral probability premise. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

theorem exists_padded_schatten_input_of_wishart_probability {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b k s n : ℕ) (ε : ℝ)
      (ha : k + s + n ≤ a) (hb : k + s + n ≤ b)
      {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
      (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S),
      0 < k → 0 ≤ ε → ε ≤ 1 →
      (n : ℝ) ≤ (k + s + n : ℝ) / 100 → (k : ℝ) ≤ (k + s + n : ℝ) / 100 →
      C * ε * (k + s + n : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4 →
      (gaussianMatrixLaw (k + s + n) (s + n)).real
        (wishartSpectralEvent (k + s + n) (s + n) L c₀ k)ᶜ ≤ 1 / 20 →
      ∃ H : Matrix (Fin (k + s + n)) (Fin (k + s + n)) ℝ, H.IsHermitian ∧
        ν.real (rectangularSchattenSuccess p ε policy (zeroPadFin ha hb H)) < 1 / 5 := by
  obtain ⟨C, hC, hmain⟩ := exists_fixed_schatten_input_of_wishart_probability hp hL hc
  refine ⟨C, hC, ?_⟩
  intro a b k s n ε ha hb S _ ν _ policy hk hε hε1 hn hkd hsmall hbad
  let left := coordinateEmbedding ha
  let right := coordinateEmbedding hb
  let reduced := reduceRectangularColumnPolicy left right n policy
  obtain ⟨H, hH, hfail⟩ := hmain k s n ε ν reduced hk hε hε1
    (reduceRectangularColumnPolicy_outputs (by omega) left right n policy) hn hkd hsmall hbad
  refine ⟨H, hH, ?_⟩
  exact (reduceRectangularColumnPolicy_probability (by omega) hp left
    (coordinateEmbedding_orthogonal ha) right (coordinateEmbedding_orthogonal hb) n ν policy H).trans_lt hfail

theorem exists_rectangular_schatten_input_of_wishart_probability {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b k s n : ℕ) (ε : ℝ),
      k + s + n ≤ a → k + s + n ≤ b →
      ∀ {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
      (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S),
      0 < k → 0 ≤ ε → ε ≤ 1 →
      (n : ℝ) ≤ (k + s + n : ℝ) / 100 → (k : ℝ) ≤ (k + s + n : ℝ) / 100 →
      C * ε * (k + s + n : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4 →
      (gaussianMatrixLaw (k + s + n) (s + n)).real
        (wishartSpectralEvent (k + s + n) (s + n) L c₀ k)ᶜ ≤ 1 / 20 →
      ∃ A : Matrix (Fin a) (Fin b) ℝ, ν.real (rectangularSchattenSuccess p ε policy A) < 1 / 5 := by
  obtain ⟨C, hC, hmain⟩ := exists_padded_schatten_input_of_wishart_probability hp hL hc
  refine ⟨C, hC, ?_⟩
  intro a b k s n ε ha hb S _ ν _ policy hk hε hε1 hn hkd hsmall hbad
  obtain ⟨H, _, hfail⟩ := hmain a b k s n ε ha hb ν policy hk hε hε1 hn hkd hsmall hbad
  exact ⟨zeroPadFin ha hb H, hfail⟩

end
end LowRank
