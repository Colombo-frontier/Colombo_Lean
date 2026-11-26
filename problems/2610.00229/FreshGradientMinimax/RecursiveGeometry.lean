import FreshGradientMinimax.RecursiveParameters
import FreshGradientMinimax.QuadraticFamily
import FreshGradientMinimax.Multilevel
import FreshGradientMinimax.FiniteSquare

/-! Pointwise geometry of the actual recursively regularized functions.
Their minima are constructed from strong convexity. Adjacent-step and
final-gradient estimates follow from value gaps, not from assumed solver
gradient guarantees. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace
variable {d : ℕ}

def recursiveLinear (μ : ℝ) (v : ℕ → Euclid d) (j : ℕ) : Euclid d :=
  ∑ i ∈ Finset.range j, recursiveMass μ i • v i

def recursiveObjective (Q : Euclid d → ℝ) (μ : ℝ) (v : ℕ → Euclid d) (j : ℕ) : Euclid d → ℝ :=
  quadraticFamily Q (recursiveCurvature μ j) (recursiveLinear μ v j)

def recursiveGradient (grad : Euclid d → Euclid d) (μ : ℝ) (v : ℕ → Euclid d) (j : ℕ) : Euclid d → Euclid d :=
  quadraticGradient grad (recursiveCurvature μ j) (recursiveLinear μ v j)

theorem recursiveLinear_succ (μ : ℝ) (v : ℕ → Euclid d) (j : ℕ) :
    recursiveLinear μ v (j + 1) = recursiveLinear μ v j + recursiveMass μ j • v j :=
  Finset.sum_range_succ _ j

theorem recursiveObjective_increment (Q : Euclid d → ℝ) (μ : ℝ) (v : ℕ → Euclid d) (j : ℕ) (x : Euclid d) :
    recursiveObjective Q μ v (j + 1) x = recursiveObjective Q μ v j x +
      recursiveMass μ j / 2 * ‖x - v j‖ ^ 2 - recursiveMass μ j / 2 * ‖v j‖ ^ 2 := by
  unfold recursiveObjective
  rw [recursiveCurvature_succ, recursiveLinear_succ, quadraticFamily_increment]

theorem recursive_gradient_identity (grad : Euclid d → Euclid d) (μ : ℝ) (v : ℕ → Euclid d) (N : ℕ) :
    grad (v N) = recursiveGradient grad μ v N (v N) -
      ∑ j ∈ Finset.range N, recursiveCurvature μ (j + 1) • (v (j + 1) - v j) := by
  have ht := recursive_regularization_identity (recursiveMass μ) v N
  simp_rw [← recursiveCurvature_sum] at ht
  have hs : (∑ i ∈ Finset.range N, recursiveMass μ i • (v N - v i)) =
      recursiveCurvature μ N • v N - recursiveLinear μ v N := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, ← recursiveCurvature_sum, recursiveLinear]
  rw [← ht, hs]
  dsimp [recursiveGradient, quadraticGradient]
  module

namespace SmoothStrongModel
variable {Q : Euclid d → ℝ} {grad : Euclid d → Euclid d} {μ H : ℝ}
variable (model : SmoothStrongModel Q grad μ H)
include model

theorem gradient_sq_le_gap (hH : 0 < H) (u : Euclid d) (hu : ∀ x, Q u ≤ Q x) (x : Euclid d) :
    ‖grad x‖ ^ 2 ≤ 2 * H * (Q x - Q u) := by
  have hs := noisy_primal_step hH x (grad x) 0 (by
    simpa only [add_zero] using model.upper x (x - H⁻¹ • grad x))
  simp only [add_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at hs
  have hmin := hu (x - H⁻¹ • grad x)
  have hd : ‖grad x‖ ^ 2 / (2 * H) ≤ Q x - Q u := by linarith
  have hm := (div_le_iff₀ (by positivity : 0 < 2 * H)).mp hd
  nlinarith only [hm]

theorem recursive_model (v : ℕ → Euclid d) (j : ℕ) :
    SmoothStrongModel (recursiveObjective Q μ v j) (recursiveGradient grad μ v j)
      (recursiveMass μ j) (H + recursiveCurvature μ j) := by
  rw [← recursiveMass_add_curvature]
  exact model.quadratic_model _ _

def recursiveMin (hμ : 0 < μ) (v : ℕ → Euclid d) (j : ℕ) : Euclid d :=
  model.quadraticMin (recursiveCurvature μ j)
    (by rw [recursiveMass_add_curvature]; exact recursiveMass_pos hμ j) (recursiveLinear μ v j)

theorem recursiveMin_minimizes (hμ : 0 < μ) (v : ℕ → Euclid d) (j : ℕ) (x : Euclid d) :
    recursiveObjective Q μ v j (model.recursiveMin hμ v j) ≤ recursiveObjective Q μ v j x :=
  model.quadraticMin_minimizes _ _ _ _

def recursiveGap (hμ : 0 < μ) (v : ℕ → Euclid d) (j : ℕ) : ℝ :=
  recursiveObjective Q μ v j (v j) - recursiveObjective Q μ v j (model.recursiveMin hμ v j)

theorem recursiveGap_nonneg (hμ : 0 < μ) (v : ℕ → Euclid d) (j : ℕ) :
    0 ≤ model.recursiveGap hμ v j := sub_nonneg.mpr (model.recursiveMin_minimizes hμ v j (v j))

theorem recursive_gap_after_add (hμ : 0 < μ) (v : ℕ → Euclid d) (j : ℕ) :
    recursiveObjective Q μ v (j + 1) (v j) -
      recursiveObjective Q μ v (j + 1) (model.recursiveMin hμ v (j + 1)) ≤ model.recursiveGap hμ v j := by
  have hmin := model.recursiveMin_minimizes hμ v j (model.recursiveMin hμ v (j + 1))
  have hp : 0 ≤ recursiveMass μ j / 2 * ‖model.recursiveMin hμ v (j + 1) - v j‖ ^ 2 := by
    have := recursiveMass_pos hμ j
    positivity
  rw [recursiveObjective_increment, recursiveObjective_increment]
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  dsimp only [recursiveGap]
  linarith

theorem recursive_step_distance (hμ : 0 < μ) (v : ℕ → Euclid d) (j : ℕ) :
    recursiveMass μ (j + 1) * ‖v (j + 1) - v j‖ ^ 2 ≤
      4 * (model.recursiveGap hμ v j + model.recursiveGap hμ v (j + 1)) := by
  let z := model.recursiveMin hμ v (j + 1)
  have hx := ((model.recursive_model v (j + 1)).gap_quadratic_bounds z
    (model.recursiveMin_minimizes hμ v (j + 1)) (v j)).1
  have hy := ((model.recursive_model v (j + 1)).gap_quadratic_bounds z
    (model.recursiveMin_minimizes hμ v (j + 1)) (v (j + 1))).1
  have hgap := model.recursive_gap_after_add hμ v j
  have ht := norm_add_sq_le_two (v (j + 1) - z) (z - v j)
  rw [sub_add_sub_cancel, norm_sub_rev z (v j)] at ht
  have htm := mul_le_mul_of_nonneg_left ht (recursiveMass_pos hμ (j + 1)).le
  change _ ≤ model.recursiveGap hμ v (j + 1) at hy
  change _ ≤ model.recursiveGap hμ v j at hgap
  linarith only [hx, hy, hgap, htm]

theorem recursive_step_weighted (hμ : 0 < μ) (v : ℕ → Euclid d) (j : ℕ) :
    ‖recursiveCurvature μ (j + 1) • (v (j + 1) - v j)‖ ^ 2 ≤
      4 * recursiveMass μ (j + 1) * (model.recursiveGap hμ v j + model.recursiveGap hμ v (j + 1)) := by
  rw [norm_smul_sq]
  have hc := sq_le_sq₀ (recursiveCurvature_nonneg hμ (j + 1)) (recursiveMass_pos hμ (j + 1)).le
  have hsq := hc.mpr (recursiveCurvature_le_mass hμ.le (j + 1))
  have ht := mul_le_mul_of_nonneg_left (model.recursive_step_distance hμ v j) (recursiveMass_pos hμ (j + 1)).le
  calc
    _ ≤ recursiveMass μ (j + 1) ^ 2 * ‖v (j + 1) - v j‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ ≤ _ := by nlinarith only [ht]

theorem recursive_last_gradient (hμ : 0 < μ) (hH : 0 < H) (v : ℕ → Euclid d) (N : ℕ)
    (hscale : H ≤ recursiveMass μ N) :
    ‖recursiveGradient grad μ v N (v N)‖ ^ 2 ≤ 4 * recursiveMass μ N * model.recursiveGap hμ v N := by
  have hcurv := recursiveCurvature_le_mass hμ.le N
  have hg := (model.recursive_model v N).gradient_sq_le_gap
    (add_pos_of_pos_of_nonneg hH (recursiveCurvature_nonneg hμ N))
    (model.recursiveMin hμ v N) (model.recursiveMin_minimizes hμ v N) (v N)
  change _ ≤ 2 * (H + recursiveCurvature μ N) * model.recursiveGap hμ v N at hg
  exact hg.trans (mul_le_mul_of_nonneg_right (by linarith) (model.recursiveGap_nonneg hμ v N))

theorem recursive_gradient_gap_bound (hμ : 0 < μ) (hH : 0 < H) (v : ℕ → Euclid d) (N : ℕ)
    (hscale : H ≤ recursiveMass μ N) :
    ‖grad (v N)‖ ^ 2 ≤ (N + 1 : ℕ) *
      (4 * recursiveMass μ N * model.recursiveGap hμ v N +
        ∑ j ∈ Finset.range N, 4 * recursiveMass μ (j + 1) *
          (model.recursiveGap hμ v j + model.recursiveGap hμ v (j + 1))) := by
  rw [recursive_gradient_identity grad μ v N]
  exact (norm_sub_sum_sq_le _ _ N).trans (mul_le_mul_of_nonneg_left
    (add_le_add (model.recursive_last_gradient hμ hH v N hscale)
      (Finset.sum_le_sum (fun j _ => model.recursive_step_weighted hμ v j))) (by positivity))

theorem recursive_gradient_scaled_gap_bound (hμ : 0 < μ) (hH : 0 < H) (v : ℕ → Euclid d) (N : ℕ)
    (hscale : H ≤ recursiveMass μ N) :
    ‖grad (v N)‖ ^ 2 ≤ (N + 1 : ℕ) *
      (4 * (recursiveMass μ N * model.recursiveGap hμ v N) +
        ∑ j ∈ Finset.range N, (8 * (recursiveMass μ j * model.recursiveGap hμ v j) +
          4 * (recursiveMass μ (j + 1) * model.recursiveGap hμ v (j + 1)))) := by
  convert model.recursive_gradient_gap_bound hμ hH v N hscale using 1
  congr 1
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [recursiveMass_succ]
    ring

end SmoothStrongModel
end FreshGradientMinimax
