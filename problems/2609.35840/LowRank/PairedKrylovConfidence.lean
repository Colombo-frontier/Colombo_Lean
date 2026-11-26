import LowRank.PairedKrylovTailPower

/-! Either Gaussian marginal can certify the common combined output.
Choosing a proof branch according to the input requires no algorithmic
access to that branch condition and no union-bound penalty. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section
universe u

theorem refinedPairedKrylovPolicy_bad_of_left_tail_ritz {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    {p ε γ L : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    (hbudget : (k : ℝ) * (γ / 2) * L ^ (p / 2) ≤ ε * optimalSchattenPower p A k)
    {β : ℝ≥0∞}
    (hbad : (iidMatrixLaw b s 1)
      (krylovTailRitzEvent Aᵀ (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k s n hka γ L)ᶜ ≤ β) :
    ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1))
      (rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A)ᶜ ≤ β := by
  let E := krylovTailRitzEvent Aᵀ (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k s n hka γ L
  have hsub : (rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A)ᶜ ⊆
      Eᶜ ×ˢ (Set.univ : Set (Matrix (Fin b) (Fin t) ℝ)) := by
    intro U hfail
    refine ⟨?_, Set.mem_univ _⟩
    intro hU
    apply hfail
    have hpower := refinedPairedKrylovPolicy_power_of_left_tail_ritz (r := r) hka hkb A U hp hp2 hγ hL hhead hU
    apply schattenNorm_relative_of_power_excess hkb A _ hp hε
    dsimp only at hpower
    linarith
  calc
    _ ≤ ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1)) (Eᶜ ×ˢ Set.univ) := measure_mono hsub
    _ = (iidMatrixLaw b s 1) Eᶜ := by rw [Measure.prod_prod, measure_univ, mul_one]
    _ ≤ β := hbad

theorem refinedPairedKrylovPolicy_bad_of_right_tail_ritz {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    {p ε γ L : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    (hbudget : (k : ℝ) * (γ / 2) * L ^ (p / 2) ≤ ε * optimalSchattenPower p A k)
    {β : ℝ≥0∞}
    (hbad : (iidMatrixLaw b t 1)
      (krylovTailRitzEvent Aᵀ (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k t r hka γ L)ᶜ ≤ β) :
    ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1))
      (rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A)ᶜ ≤ β := by
  let E := krylovTailRitzEvent Aᵀ (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k t r hka γ L
  have hsub : (rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A)ᶜ ⊆
      (Set.univ : Set (Matrix (Fin b) (Fin s) ℝ)) ×ˢ Eᶜ := by
    intro U hfail
    refine ⟨Set.mem_univ _, ?_⟩
    intro hU
    apply hfail
    have hpower := refinedPairedKrylovPolicy_power_of_right_tail_ritz (n := n) hka hkb A U hp hp2 hγ hL hhead hU
    apply schattenNorm_relative_of_power_excess hkb A _ hp hε
    dsimp only at hpower
    linarith
  calc
    _ ≤ ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1)) (Set.univ ×ˢ Eᶜ) := measure_mono hsub
    _ = (iidMatrixLaw b t 1) Eᶜ := by rw [Measure.prod_prod, measure_univ, one_mul]
    _ ≤ β := hbad

theorem refinedPairedKrylovAlgorithm_success_of_bad_le {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    {p ε : ℝ} (hp : 0 < p)
    (hbad : ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1))
      (rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A)ᶜ ≤ 1 / 20) :
    19 / 20 ≤ (refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).law.real
      (rectangularSchattenSuccess p ε (refinedPairedKrylovAlgorithm.{u} a b k s t n r hka hkb).policy A) := by
  rw [refinedPairedKrylovAlgorithm_success_probability hka hkb hp]
  have hr := ENNReal.toReal_mono (by norm_num : (1 / 20 : ℝ≥0∞) ≠ ∞) hbad
  change ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1)).real _ ≤ _ at hr
  rw [measureReal_compl (measurableSet_rectangularSchattenSuccess hkb hp ε _ A),
    measureReal_univ_eq_one] at hr
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hr
  linarith

end
end LowRank
