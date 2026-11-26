import FreshGradientMinimax.RecursiveAccuracy

/-! A quadratic-coefficient potential avoids assuming a common trajectory
or independence of successive solves. Its one-step bound needs only the
actual frozen-coefficient relation between two adjacent outputs. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {dx dy : ℕ}

def recursiveResidualPotential (μ : ℝ) (j : ℕ) (z : Euclid dy × Joint dx dy) : ℝ :=
  ‖recursiveCurvature μ j • z.2.2 - z.1‖ ^ 2 / (j + 1 : ℕ)

theorem recursiveResidualPotential_continuous (μ : ℝ) (j : ℕ) :
    Continuous (recursiveResidualPotential (dx := dx) (dy := dy) μ j) :=
  (((continuous_const.smul continuous_snd.snd).sub continuous_fst).norm.pow 2).div_const _

theorem recursiveResidualPotential_nonneg (μ : ℝ) (j : ℕ) (z : Euclid dy × Joint dx dy) :
    0 ≤ recursiveResidualPotential μ j z := by unfold recursiveResidualPotential; positivity

theorem norm_add_sq_div_succ (x y : Euclid dy) (j : ℕ) :
    ‖x + y‖ ^ 2 / (j + 2 : ℕ) ≤ ‖x‖ ^ 2 / (j + 1 : ℕ) + ‖y‖ ^ 2 := by
  have hp : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hp' : (0 : ℝ) < (j + 2 : ℕ) := by positivity
  have hs := sq_nonneg ‖x - ((j + 1 : ℕ) : ℝ) • y‖
  rw [norm_sub_sq_real, inner_smul_right, norm_smul_sq] at hs
  have hw : (j + 1 : ℕ) * ‖x + y‖ ^ 2 ≤
      (j + 2 : ℕ) * (‖x‖ ^ 2 + (j + 1 : ℕ) * ‖y‖ ^ 2) := by
    rw [norm_add_sq_real]
    push_cast at hs ⊢
    nlinarith only [hs]
  apply (div_le_iff₀ hp').mpr
  apply (mul_le_mul_left hp).mp
  calc
    _ ≤ (j + 2 : ℕ) * (‖x‖ ^ 2 + (j + 1 : ℕ) * ‖y‖ ^ 2) := hw
    _ = _ := by field_simp only [ne_of_gt hp]; ring

namespace SCObjective
variable {ℓ μ α : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem dualQuadraticGap_congr (hfast : ℓ / 4 ≤ α) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a = b) :
    S.dualQuadraticGap hfast a ha = S.dualQuadraticGap hfast b hb := by
  cases hab
  rfl

theorem recursive_coefficient_step (hfast : ℓ / 4 ≤ α) (j : ℕ)
    (x y : Euclid dy × Joint dx dy) (hb : y.1 = x.1 + recursiveMass μ j • x.2.2) :
    ‖recursiveCurvature μ (j + 1) • (y.2.2 - x.2.2)‖ ^ 2 ≤
      4 * recursiveMass μ (j + 1) *
        (S.dualQuadraticGap hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j) x +
          S.dualQuadraticGap hfast (recursiveCurvature μ (j + 1)) (recursiveCurvature_nonneg S.μ_pos (j + 1)) y) := by
  let a := recursiveCurvature μ (j + 1)
  have ha := recursiveCurvature_nonneg S.μ_pos (j + 1)
  let z := S.dualQuadraticMin hfast a ha y.1
  have hx := ((S.dualQuadratic_model hfast a y.1).gap_quadratic_bounds z
    (S.dualQuadraticMin_minimizes hfast a ha y.1) x.2.2).1
  have hy := ((S.dualQuadratic_model hfast a y.1).gap_quadratic_bounds z
    (S.dualQuadraticMin_minimizes hfast a ha y.1) y.2.2).1
  have hgap := S.quadratic_advance_gap hfast (recursiveCurvature μ j) (recursiveMass μ j)
    (recursiveCurvature_nonneg S.μ_pos j) (recursiveMass_pos S.μ_pos j).le x
  rw [← S.dualQuadraticGap_congr hfast ha _ (recursiveCurvature_succ μ j)] at hgap
  change quadraticFamily S.effectiveValue a (x.1 + recursiveMass μ j • x.2.2) x.2.2 -
    quadraticFamily S.effectiveValue a (x.1 + recursiveMass μ j • x.2.2)
      (S.dualQuadraticMin hfast a ha (x.1 + recursiveMass μ j • x.2.2)) ≤ _ at hgap
  rw [← hb] at hgap
  have ht := norm_add_sq_le_two (y.2.2 - z) (z - x.2.2)
  rw [sub_add_sub_cancel, norm_sub_rev z x.2.2] at ht
  have htm := mul_le_mul_of_nonneg_left ht (recursiveMass_pos S.μ_pos (j + 1)).le
  change (μ + recursiveCurvature μ (j + 1)) / 2 * _ ≤ _ at hx hy
  rw [recursiveMass_add_curvature] at hx hy
  change _ ≤ S.dualQuadraticGap hfast a ha y at hy
  have hd : recursiveMass μ (j + 1) * ‖y.2.2 - x.2.2‖ ^ 2 ≤
      4 * (S.dualQuadraticGap hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j) x +
        S.dualQuadraticGap hfast a ha y) := by linarith only [hx, hy, hgap, htm]
  rw [norm_smul_sq]
  have hsq := (sq_le_sq₀ ha (recursiveMass_pos S.μ_pos (j + 1)).le).mpr
    (recursiveCurvature_le_mass S.μ_pos.le (j + 1))
  have hdm := mul_le_mul_of_nonneg_left hd (recursiveMass_pos S.μ_pos (j + 1)).le
  have hnorm := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖y.2.2 - x.2.2‖)
  nlinarith only [hdm, hnorm]

theorem recursive_potential_step (hfast : ℓ / 4 ≤ α) (j : ℕ)
    (x y : Euclid dy × Joint dx dy) (hb : y.1 = x.1 + recursiveMass μ j • x.2.2) :
    recursiveResidualPotential μ (j + 1) y ≤ recursiveResidualPotential μ j x +
      4 * recursiveMass μ (j + 1) *
        (S.dualQuadraticGap hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j) x +
          S.dualQuadraticGap hfast (recursiveCurvature μ (j + 1)) (recursiveCurvature_nonneg S.μ_pos (j + 1)) y) := by
  have hid : recursiveCurvature μ (j + 1) • y.2.2 - y.1 =
      (recursiveCurvature μ j • x.2.2 - x.1) +
        recursiveCurvature μ (j + 1) • (y.2.2 - x.2.2) := by
    rw [hb, recursiveCurvature_succ]
    module
  have h := norm_add_sq_div_succ (recursiveCurvature μ j • x.2.2 - x.1)
    (recursiveCurvature μ (j + 1) • (y.2.2 - x.2.2)) j
  rw [← hid] at h
  exact h.trans (add_le_add_left (S.recursive_coefficient_step hfast j x y hb) _)

theorem recursive_gradient_potential (hfast : ℓ / 4 ≤ α) (N : ℕ)
    (hscale : 5 * ℓ ≤ recursiveMass μ N) (z : Euclid dy × Joint dx dy) :
    ‖gradient S.effectiveValue z.2.2‖ ^ 2 ≤
      8 * recursiveMass μ N * S.dualQuadraticGap hfast (recursiveCurvature μ N) (recursiveCurvature_nonneg S.μ_pos N) z +
        2 * (N + 1 : ℕ) * recursiveResidualPotential μ N z := by
  have hg := ((S.effective_model hfast).quadratic_model (recursiveCurvature μ N) z.1).gradient_sq_le_gap
    (add_pos_of_pos_of_nonneg (by have := S.L_pos; positivity) (recursiveCurvature_nonneg S.μ_pos N))
    (S.dualQuadraticMin hfast _ (recursiveCurvature_nonneg S.μ_pos N) z.1)
    (S.dualQuadraticMin_minimizes hfast _ (recursiveCurvature_nonneg S.μ_pos N) z.1) z.2.2
  have hgap : 0 ≤ S.dualQuadraticGap hfast (recursiveCurvature μ N) (recursiveCurvature_nonneg S.μ_pos N) z :=
    sub_nonneg.mpr (S.dualQuadraticMin_minimizes hfast _ (recursiveCurvature_nonneg S.μ_pos N) z.1 z.2.2)
  have hc := recursiveCurvature_le_mass S.μ_pos.le N
  have hid : gradient S.effectiveValue z.2.2 =
      quadraticGradient (gradient S.effectiveValue) (recursiveCurvature μ N) z.1 z.2.2 +
        -(recursiveCurvature μ N • z.2.2 - z.1) := by dsimp [quadraticGradient]; module
  have ht := norm_add_sq_le_two (quadraticGradient (gradient S.effectiveValue) (recursiveCurvature μ N) z.1 z.2.2)
    (-(recursiveCurvature μ N • z.2.2 - z.1))
  rw [← hid, norm_neg] at ht
  change _ ≤ 2 * (5 * ℓ + recursiveCurvature μ N) * S.dualQuadraticGap hfast _ _ z at hg
  have hg' : ‖quadraticGradient (gradient S.effectiveValue) (recursiveCurvature μ N) z.1 z.2.2‖ ^ 2 ≤
      4 * recursiveMass μ N * S.dualQuadraticGap hfast _ _ z :=
    hg.trans (mul_le_mul_of_nonneg_right (by linarith) hgap)
  have hpos : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have heq : (N + 1 : ℕ) * recursiveResidualPotential μ N z =
      ‖recursiveCurvature μ N • z.2.2 - z.1‖ ^ 2 := by
    unfold recursiveResidualPotential
    exact mul_div_cancel₀ _ hpos
  nlinarith only [ht, hg', heq]

end SCObjective
end FreshGradientMinimax
