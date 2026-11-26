import FreshGradientMinimax.CostedMultilevel

/-! Pointwise law transport for multilevel estimators and their cost tags. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d : ℕ}

theorem independentCorrectionKernel_congr_at (L : ℕ → Kernel X (Euclid d))
    (M : ℕ → Kernel Y (Euclid d)) [∀ j, IsMarkovKernel (L j)] [∀ j, IsMarkovKernel (M j)]
    (x : X) (y : Y) (h : ∀ j, L j x = M j y) (p : ℝ) (j : ℕ) :
    independentCorrectionKernel (L 0) (L (j + 1)) (L j) p x =
      independentCorrectionKernel (M 0) (M (j + 1)) (M j) p y := by
  rw [independentCorrectionKernel_apply, independentCorrectionKernel_apply, h 0, h (j + 1), h j]

theorem multilevelKernel_congr_at (L : ℕ → Kernel X (Euclid d))
    (M : ℕ → Kernel Y (Euclid d)) [∀ j, IsMarkovKernel (L j)] [∀ j, IsMarkovKernel (M j)]
    (x : X) (y : Y) (h : ∀ j, L j x = M j y) (K : ℕ) :
    multilevelKernel L K x = multilevelKernel M K y := by
  by_cases hK : K = 0
  · simpa only [multilevelKernel, if_pos hK] using h 0
  · simp only [multilevelKernel, if_neg hK, finiteMixtureKernel_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [independentCorrectionKernel_congr_at L M x y h]

theorem costedMultilevelKernel_congr_at (L : ℕ → Kernel X (Euclid d))
    (M : ℕ → Kernel Y (Euclid d)) [∀ j, IsMarkovKernel (L j)] [∀ j, IsMarkovKernel (M j)]
    (x : X) (y : Y) (h : ∀ j, L j x = M j y) (c : ℕ → ℕ) (K : ℕ) :
    costedMultilevelKernel L c K x = costedMultilevelKernel M c K y := by
  have htag (U : Kernel X (Euclid d)) (V : Kernel Y (Euclid d))
      (he : U x = V y) (n : ℕ) : taggedKernel U n x = taggedKernel V n y := by
    rw [taggedKernel, taggedKernel, Kernel.map_apply (f := fun r : Euclid d => (r, n)) _
      (measurable_id.prodMk measurable_const), Kernel.map_apply (f := fun r : Euclid d => (r, n)) _
      (measurable_id.prodMk measurable_const), he]
  by_cases hK : K = 0
  · simp only [costedMultilevelKernel, if_pos hK]
    exact htag _ _ (h 0) _
  · simp only [costedMultilevelKernel, if_neg hK, finiteMixtureKernel_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [htag _ _ (independentCorrectionKernel_congr_at L M x y h _ j)]

end FreshGradientMinimax
