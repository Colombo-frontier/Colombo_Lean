import LowRank.RefinedPowerWeightedKrylov
import LowRank.PairedKrylovConfidence

/-! Either power-weighted marginal controls the common paired output
for every finite Schatten exponent at least one. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix ENNReal
noncomputable section

theorem refinedPairedKrylovPolicy_power_of_left_weighted_ritz {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (U : PairedKrylovSeed b s t) (v : ℕ) {p δ L : ℝ} (hp : 1 ≤ p)
    (hv : p / 2 - 1 ≤ ((2 * v : ℕ) : ℝ)) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    (hU : U.1 ∈ krylovPowerWeightedRitzEvent Aᵀ
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k s n v hka δ L) :
    let Z := runBoundedRectangular a b (pairedKrylovQueryBudget s t n r)
      (refinedPairedKrylovPolicy a b k s t n r hka hkb) A U
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ optimalSchattenPower p A k +
      max 1 (p / 2) * (k : ℝ) * (δ / 2) * L ^ (p / 2) := by
  apply refinedPairedKrylovPolicy_power_of_capture hka hkb A U (columnRangeProjector_isProjector _)
    (pairedKrylovProjector_absorbs_left Aᵀ n r U) hp
  exact optimalColumnSelector_power_weighted_tail_deficit hka Aᵀ _ v
    (by linarith : 0 < p) hv (by positivity : 0 ≤ δ / 2) hL hhead hU

theorem refinedPairedKrylovPolicy_power_of_right_weighted_ritz {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (U : PairedKrylovSeed b s t) (v : ℕ) {p δ L : ℝ} (hp : 1 ≤ p)
    (hv : p / 2 - 1 ≤ ((2 * v : ℕ) : ℝ)) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    (hU : U.2 ∈ krylovPowerWeightedRitzEvent Aᵀ
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k t r v hka δ L) :
    let Z := runBoundedRectangular a b (pairedKrylovQueryBudget s t n r)
      (refinedPairedKrylovPolicy a b k s t n r hka hkb) A U
    schattenPower p (A * (1 - Z * Zᵀ)) ≤ optimalSchattenPower p A k +
      max 1 (p / 2) * (k : ℝ) * (δ / 2) * L ^ (p / 2) := by
  apply refinedPairedKrylovPolicy_power_of_capture hka hkb A U (columnRangeProjector_isProjector _)
    (pairedKrylovProjector_absorbs_right Aᵀ n r U) hp
  exact optimalColumnSelector_power_weighted_tail_deficit hka Aᵀ _ v
    (by linarith : 0 < p) hv (by positivity : 0 ≤ δ / 2) hL hhead hU

theorem refinedPairedKrylovPolicy_bad_of_left_weighted_ritz {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (v : ℕ) {p ε δ L : ℝ} (hp : 1 ≤ p) (hv : p / 2 - 1 ≤ ((2 * v : ℕ) : ℝ))
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    (hbudget : max 1 (p / 2) * (k : ℝ) * (δ / 2) * L ^ (p / 2) ≤ ε * optimalSchattenPower p A k)
    {β : ℝ≥0∞}
    (hbad : (iidMatrixLaw b s 1) (krylovPowerWeightedRitzEvent Aᵀ
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k s n v hka δ L)ᶜ ≤ β) :
    ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1))
      (rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A)ᶜ ≤ β := by
  let E := krylovPowerWeightedRitzEvent Aᵀ
    (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k s n v hka δ L
  have hsub : (rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A)ᶜ ⊆
      Eᶜ ×ˢ (Set.univ : Set (Matrix (Fin b) (Fin t) ℝ)) := by
    intro U hfail
    refine ⟨?_, Set.mem_univ _⟩
    intro hU
    apply hfail
    have hpower := refinedPairedKrylovPolicy_power_of_left_weighted_ritz (r := r) hka hkb A U v hp hv hδ hL hhead hU
    apply schattenNorm_relative_of_power_excess hkb A _ hp hε
    dsimp only at hpower
    linarith
  calc
    _ ≤ ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1)) (Eᶜ ×ˢ Set.univ) := measure_mono hsub
    _ = (iidMatrixLaw b s 1) Eᶜ := by rw [Measure.prod_prod, measure_univ, mul_one]
    _ ≤ β := hbad

theorem refinedPairedKrylovPolicy_bad_of_right_weighted_ritz {a b k s t n r : ℕ}
    (hka : k ≤ a) (hkb : k ≤ b) (A : Matrix (Fin a) (Fin b) ℝ)
    (v : ℕ) {p ε δ L : ℝ} (hp : 1 ≤ p) (hv : p / 2 - 1 ≤ ((2 * v : ℕ) : ℝ))
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hhead : ∀ j : Fin k, L ≤
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)).value (lastColumnIndex a k hka j))
    (hbudget : max 1 (p / 2) * (k : ℝ) * (δ / 2) * L ^ (p / 2) ≤ ε * optimalSchattenPower p A k)
    {β : ℝ≥0∞}
    (hbad : (iidMatrixLaw b t 1) (krylovPowerWeightedRitzEvent Aᵀ
      (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k t r v hka δ L)ᶜ ≤ β) :
    ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1))
      (rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A)ᶜ ≤ β := by
  let E := krylovPowerWeightedRitzEvent Aᵀ
    (canonicalOrderedSpectrum a (symmetricRightGram Aᵀ)) k t r v hka δ L
  have hsub : (rectangularSchattenSuccess p ε (refinedPairedKrylovPolicy a b k s t n r hka hkb) A)ᶜ ⊆
      (Set.univ : Set (Matrix (Fin b) (Fin s) ℝ)) ×ˢ Eᶜ := by
    intro U hfail
    refine ⟨Set.mem_univ _, ?_⟩
    intro hU
    apply hfail
    have hpower := refinedPairedKrylovPolicy_power_of_right_weighted_ritz (n := n) hka hkb A U v hp hv hδ hL hhead hU
    apply schattenNorm_relative_of_power_excess hkb A _ hp hε
    dsimp only at hpower
    linarith
  calc
    _ ≤ ((iidMatrixLaw b s 1).prod (iidMatrixLaw b t 1)) (Set.univ ×ˢ Eᶜ) := measure_mono hsub
    _ = (iidMatrixLaw b t 1) Eᶜ := by rw [Measure.prod_prod, measure_univ, one_mul]
    _ ≤ β := hbad

end
end LowRank
