import FreshGradientMinimax.LinearFlatEnergy
import FreshGradientMinimax.ConvexGradient
import FreshGradientMinimax.NormalInverse
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The actual maximizer of a regularized flat energy, and its quantitative
distance from the true unflattened quadratic solution. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

variable {n m : ℕ}

def flatPotential (A : Euclid n →L[ℝ] Euclid m) (μ β δ : ℝ) (b y : Euclid n) : ℝ :=
  ⟪b, y⟫_ℝ - μ / 2 * ‖y‖ ^ 2 - linearFlatEnergy A β δ y

def flatPotentialGradient (A : Euclid n →L[ℝ] Euclid m) (μ β δ : ℝ) (b y : Euclid n) : Euclid n :=
  b - μ • y - linearFlatGradient A β δ y

theorem flatPotential_hasFDerivAt (A : Euclid n →L[ℝ] Euclid m) (μ β : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (b y : Euclid n) :
    HasFDerivAt (flatPotential A μ β δ b) (innerSL ℝ (flatPotentialGradient A μ β δ b y)) y := by
  have hn := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (μ / 2)
  apply (((innerSL ℝ b).hasFDerivAt.sub hn).sub (linearFlatEnergy_hasFDerivAt A β hδ y)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [flatPotentialGradient, innerSL_apply, inner_sub_left, real_inner_smul_left]
  ring

theorem flatPotential_strongConcave (A : Euclid n →L[ℝ] Euclid m) (μ : ℝ)
    {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (b : Euclid n) :
    StrongConcaveGradient (flatPotential A μ β δ b) (flatPotentialGradient A μ β δ b) μ := by
  simpa only [zero_add, flatPotential, flatPotentialGradient] using
    convex_penalty_strongConcave (linearFlatEnergy_convex A hβ hδ)
      (linearFlatEnergy_hasFDerivAt A β hδ) μ 0 b

theorem flatPotential_max_exists (A : Euclid n →L[ℝ] Euclid m) {μ β δ : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (b : Euclid n) :
    ∃ y, ∀ z, flatPotential A μ β δ b z ≤ flatPotential A μ β δ b y :=
  strong_concave_maximum_exists hμ (flatPotential_strongConcave A μ hβ hδ b)
    (continuous_iff_continuousAt.mpr (fun y => (flatPotential_hasFDerivAt A μ β hδ b y).continuousAt))

def flatMaximizer (A : Euclid n →L[ℝ] Euclid m) (μ β δ : ℝ)
    (hμ : 0 < μ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (b : Euclid n) : Euclid n :=
  Classical.choose (flatPotential_max_exists A hμ hβ hδ b)

theorem flatMaximizer_max (A : Euclid n →L[ℝ] Euclid m) {μ β δ : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (b z : Euclid n) :
    flatPotential A μ β δ b z ≤ flatPotential A μ β δ b (flatMaximizer A μ β δ hμ hβ hδ b) :=
  Classical.choose_spec (flatPotential_max_exists A hμ hβ hδ b) z

theorem flatMaximizer_gradient_zero (A : Euclid n →L[ℝ] Euclid m) {μ β δ : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (b : Euclid n) :
    flatPotentialGradient A μ β δ b (flatMaximizer A μ β δ hμ hβ hδ b) = 0 :=
  gradient_zero_at_global_max _ (flatPotential_hasFDerivAt A μ β hδ b _)
    (flatMaximizer_max A hμ hβ hδ b)

theorem flatMaximizer_root (A : Euclid n →L[ℝ] Euclid m) {μ β δ : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (b : Euclid n) :
    μ • flatMaximizer A μ β δ hμ hβ hδ b +
      linearFlatGradient A β δ (flatMaximizer A μ β δ hμ hβ hδ b) = b := by
  have h := flatMaximizer_gradient_zero A hμ hβ hδ b
  dsimp only [flatPotentialGradient] at h
  rw [sub_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem flatMaximizer_residual_distance (A : Euclid n →L[ℝ] Euclid m) {μ β δ : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (b y : Euclid n) :
    μ * ‖y - flatMaximizer A μ β δ hμ hβ hδ b‖ ≤ ‖flatPotentialGradient A μ β δ b y‖ := by
  have h := strong_concave_gradient_monotone (flatPotential_strongConcave A μ hβ hδ b)
    y (flatMaximizer A μ β δ hμ hβ hδ b)
  rw [flatMaximizer_gradient_zero, zero_sub] at h
  simpa only [norm_neg] using residual_controls_distance μ (-flatPotentialGradient A μ β δ b y)
    (y - flatMaximizer A μ β δ hμ hβ hδ b) h

theorem flatMaximizer_norm (A : Euclid n →L[ℝ] Euclid m) {μ β δ : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (b : Euclid n) :
    ‖flatMaximizer A μ β δ hμ hβ hδ b‖ ≤ ‖b‖ / μ := by
  have h := flatMaximizer_residual_distance A hμ hβ hδ b 0
  simp only [zero_sub, norm_neg, flatPotentialGradient, smul_zero, sub_zero,
    linearFlatGradient_zero A β hδ] at h
  exact (le_div_iff₀ hμ).mpr (by simpa only [mul_comm] using h)

theorem flatMaximizer_eq_of_root (A : Euclid n →L[ℝ] Euclid m) {μ β δ : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) {b y : Euclid n}
    (hy : flatPotentialGradient A μ β δ b y = 0) : flatMaximizer A μ β δ hμ hβ hδ b = y := by
  have h := flatMaximizer_residual_distance A hμ hβ hδ b y
  rw [hy, norm_zero] at h
  have he : ‖y - flatMaximizer A μ β δ hμ hβ hδ b‖ = 0 := by
    nlinarith [norm_nonneg (y - flatMaximizer A μ β δ hμ hβ hδ b)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

theorem flatMaximizer_quadratic_distance (A : Euclid n →L[ℝ] Euclid m) {μ β δ : ℝ}
    (hμ : 0 < μ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hA : ‖A‖ ≤ 2) (b : Euclid n) :
    ‖flatMaximizer A μ β δ hμ hβ hδ b - normalInverse A μ β hμ hβ b‖ ≤
      2 * β * δ * Real.sqrt m / μ := by
  let y := normalInverse A μ β hμ hβ b
  have he : flatPotentialGradient A μ β δ b y =
      -(linearFlatGradient A β δ y - β • (A†) (A y)) := by
    have h : μ • y + β • (A†) (A y) = b := normalInverse_right A hμ hβ b
    dsimp [flatPotentialGradient]
    rw [← h]
    abel
  have hr := flatMaximizer_residual_distance A hμ hβ hδ b y
  rw [he, norm_neg, norm_sub_rev y] at hr
  have hp := linearFlatGradient_perturbation A hβ hδ hA y
  exact (le_div_iff₀ hμ).mpr (by nlinarith only [hr, hp])

end FreshGradientMinimax
