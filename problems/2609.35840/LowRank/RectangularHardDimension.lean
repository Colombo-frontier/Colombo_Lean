import LowRank.RectangularWishartHardness

/-! Express the conditional rectangular lower bound using an arbitrary
hard dimension d. The query and rank constraints imply the residual
Gaussian dimension is nonnegative; it is constructed inside the proof. -/

namespace LowRank
open Matrix MeasureTheory
noncomputable section

theorem exists_rectangular_schatten_input_in_dimension {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b d k n : ℕ) (ε : ℝ),
      d ≤ a → d ≤ b →
      ∀ {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
      (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S),
      0 < k → 0 ≤ ε → ε ≤ 1 →
      (n : ℝ) ≤ (d : ℝ) / 100 → (k : ℝ) ≤ (d : ℝ) / 100 →
      C * ε * (d : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4 →
      (gaussianMatrixLaw d (d - k)).real (wishartSpectralEvent d (d - k) L c₀ k)ᶜ ≤ 1 / 20 →
      ∃ A : Matrix (Fin a) (Fin b) ℝ, ν.real (rectangularSchattenSuccess p ε policy A) < 1 / 5 := by
  obtain ⟨C, hC, hmain⟩ := exists_rectangular_schatten_input_of_wishart_probability hp hL hc
  refine ⟨C, hC, ?_⟩
  intro a b d k n ε ha hb S _ ν _ policy hk hε hε1 hn hkd hsmall hbad
  have hkn : k + n ≤ d := by
    have hreal : (k : ℝ) + (n : ℝ) ≤ (d : ℝ) := by
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    exact_mod_cast hreal
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hkn
  have hdim : d = k + s + n := by omega
  clear hs
  subst d
  have hcols : k + s + n - k = s + n := by omega
  simp only [Nat.cast_add] at hn hkd hsmall
  rw [hcols] at hbad
  apply hmain a b k s n ε ha hb ν policy hk hε hε1 hn hkd hsmall
  exact hbad

theorem rectangular_schatten_budget_gt_of_wishart_probability {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b d k n : ℕ) (ε : ℝ),
      d ≤ a → d ≤ b →
      ∀ {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
      (policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n S),
      0 < k → 0 ≤ ε → ε ≤ 1 → (k : ℝ) ≤ (d : ℝ) / 100 →
      C * ε * (d : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4 →
      (gaussianMatrixLaw d (d - k)).real (wishartSpectralEvent d (d - k) L c₀ k)ᶜ ≤ 1 / 20 →
      (∀ A : Matrix (Fin a) (Fin b) ℝ, 1 / 5 ≤ ν.real (rectangularSchattenSuccess p ε policy A)) →
      (d : ℝ) / 100 < (n : ℝ) := by
  obtain ⟨C, hC, hmain⟩ := exists_rectangular_schatten_input_in_dimension hp hL hc
  refine ⟨C, hC, ?_⟩
  intro a b d k n ε ha hb S _ ν _ policy hk hε hε1 hkd hsmall hbad hsuccess
  by_contra hn
  obtain ⟨A, hA⟩ := hmain a b d k n ε ha hb ν policy hk hε hε1
    (le_of_not_gt hn) hkd hsmall hbad
  exact (not_le_of_gt hA) (hsuccess A)

end
end LowRank
