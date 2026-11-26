import FreshGradientMinimax.AcceleratedUncappedGradient
import FreshGradientMinimax.CompressedSmoothness

/-! The uncapped formula as an actual NC--SC objective. Its established
joint derivative and four gradient blocks provide the value calculus. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

def acceleratedUncappedModel (n k : ℕ) (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    NCObjective (k * 2 + 1) (k * (n + 2)) 30000 (robinStep (n + 2) ^ 2) where
  μ_pos := sq_pos_of_pos (robinStep_pos (show 0 < n + 2 by omega))
  μ_le_L := (robinStep_sq_le_one n).trans (by norm_num)
  f := acceleratedUncapped n k δ
  gradX := acceleratedUncappedGradientU n k δ
  gradY := acceleratedDualGradient n k δ
  derivative := acceleratedUncapped_hasFDerivAt_joint n k hδ
  joint_smooth := by
    intro x y z w
    apply joint_smooth_of_four_blocks (by norm_num : (0 : ℝ) ≤ 30000) ?_ ?_ ?_ ?_ x z y w
    · intro a b c
      exact (acceleratedUncappedGradientU_difference_u hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
    · intro a b c
      exact (acceleratedUncappedGradientU_difference_y hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
    · intro a b c
      exact (acceleratedDualGradient_difference_u hn hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
    · intro a b c
      exact (acceleratedDualGradient_difference_y n k hδ a b c).trans
        (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
  dual_strong := acceleratedUncapped_strongConcave n k hδ

theorem acceleratedUncappedModel_max {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    (acceleratedUncappedModel n k hn hδ).dualMax u = acceleratedHuberMaximizer n k δ u hδ :=
  ((acceleratedUncappedModel n k hn hδ).dualMax_unique u _ (acceleratedHuberMaximizer_max n k hδ u)).symm

def acceleratedValue (n k : ℕ) (δ : ℝ) (u : Euclid (k * 2 + 1)) : ℝ :=
  sSup (Set.range (acceleratedUncapped n k δ u))

theorem acceleratedValue_eq_max {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    acceleratedValue n k δ u = acceleratedUncapped n k δ u (acceleratedHuberMaximizer n k δ u hδ) := by
  have h := (acceleratedUncappedModel n k hn hδ).value_eq_max u
  rw [acceleratedUncappedModel_max hn hδ] at h
  exact h

theorem acceleratedValue_hasFDerivAt {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    HasFDerivAt (acceleratedValue n k δ)
      (innerSL ℝ (acceleratedUncappedGradientU n k δ u (acceleratedHuberMaximizer n k δ u hδ))) u := by
  have h := (acceleratedUncappedModel n k hn hδ).value_hasFDerivAt u
  change HasFDerivAt (acceleratedValue n k δ)
    (innerSL ℝ (acceleratedUncappedGradientU n k δ u ((acceleratedUncappedModel n k hn hδ).dualMax u))) u at h
  rwa [acceleratedUncappedModel_max hn hδ] at h

theorem acceleratedValue_gradient {n k : ℕ} (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    gradient (acceleratedValue n k δ) u =
      acceleratedUncappedGradientU n k δ u (acceleratedHuberMaximizer n k δ u hδ) :=
  (hasGradientAt_iff_hasFDerivAt.mpr (acceleratedValue_hasFDerivAt hn hδ u)).gradient

theorem acceleratedValue_zero {n k : ℕ} (hn : 10 ≤ n + 2) (u : Euclid (k * 2 + 1)) :
    acceleratedValue n k 0 u = acceleratedIdealValue u := by
  rw [acceleratedValue_eq_max hn (le_refl 0), acceleratedHuberMaximizer_zero hn,
    accelerated_zero_elimination hn]

theorem acceleratedIdealValue_gradient {n k : ℕ} (hn : 10 ≤ n + 2) (u : Euclid (k * 2 + 1)) :
    gradient acceleratedIdealValue u = acceleratedUncappedGradientU n k 0 u (acceleratedQuadraticMaximizer n k u) := by
  have he : acceleratedValue n k 0 = acceleratedIdealValue := funext (acceleratedValue_zero hn)
  rw [← he, acceleratedValue_gradient hn (le_refl 0), acceleratedHuberMaximizer_zero hn]

end FreshGradientMinimax
