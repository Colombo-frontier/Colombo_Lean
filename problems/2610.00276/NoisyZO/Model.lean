import NoisyZO.HardMinimizer
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Normalized smooth strongly-convex model

This file records Definition 2.1 in Lean.  A `SmoothnessOrder` is an explicit
witness for `β = k + α`, with `k` the available derivative order and
`0 < α ≤ 1`.  This avoids hiding the integer/noninteger convention behind a
noncomputable real ceiling while retaining exactly the data used by every
proof.
-/

open scoped ContDiff InnerProductSpace Gradient

namespace NoisyZO

noncomputable section

structure SmoothnessOrder where
  beta : ℝ
  k : ℕ
  alpha : ℝ
  beta_gt_two : 2 < beta
  alpha_pos : 0 < alpha
  alpha_le_one : alpha ≤ 1
  beta_eq : beta = k + alpha

def SmoothnessOrder.exponent (o : SmoothnessOrder) : ℝ :=
  (o.beta - 1) / o.beta

/-- The convention `β = k + α`, `β > 2`, and `α ≤ 1` forces at least two
available derivatives. -/
theorem SmoothnessOrder.two_le_k (o : SmoothnessOrder) : 2 ≤ o.k := by
  by_contra hk
  have hkNat : o.k ≤ 1 := by omega
  have hkReal : (o.k : ℝ) ≤ 1 := by exact_mod_cast hkNat
  linarith [o.beta_gt_two, o.alpha_le_one, o.beta_eq]

/-- At the endpoint `β = 4`, the smoothness convention uniquely determines
the integer and fractional parts used by the Taylor expansion. -/
theorem SmoothnessOrder.k_eq_three_of_beta_eq_four (o : SmoothnessOrder)
    (hbeta : o.beta = 4) : o.k = 3 := by
  have hkltReal : (o.k : ℝ) < 4 := by
    linarith [o.alpha_pos, o.beta_eq]
  have hklt : o.k < 4 := by exact_mod_cast hkltReal
  have hkge : 3 ≤ o.k := by
    by_contra h
    have hkle : o.k ≤ 2 := by omega
    have hkleReal : (o.k : ℝ) ≤ 2 := by exact_mod_cast hkle
    linarith [o.alpha_le_one, o.beta_eq]
  omega

theorem SmoothnessOrder.alpha_eq_one_of_beta_eq_four (o : SmoothnessOrder)
    (hbeta : o.beta = 4) : o.alpha = 1 := by
  have hk := o.k_eq_three_of_beta_eq_four hbeta
  have hdecomp := o.beta_eq
  rw [hk] at hdecomp
  norm_num [hbeta] at hdecomp ⊢
  linarith

/-- The normalized function class from Definition 2.1. -/
structure NormalizedObjective (o : SmoothnessOrder) (d : ℕ) where
  f : Point d → ℝ
  minimizer : Point d
  smooth : ContDiff ℝ o.k f
  minimizer_mem : ‖minimizer‖ ≤ 1
  strong : ∀ x y,
    f x + ⟪∇ f x, y - x⟫_ℝ + (1 / 2 : ℝ) * ‖y - x‖ ^ 2 ≤ f y
  gradient_lipschitz : ∀ x y,
    ‖∇ f x - ∇ f y‖ ≤ 3 * ‖x - y‖
  higher_holder : ∀ x y,
    ‖iteratedFDeriv ℝ o.k f x - iteratedFDeriv ℝ o.k f y‖ ≤
      ‖x - y‖ ^ o.alpha
  minimizer_stationary : ∇ f minimizer = 0

theorem NormalizedObjective.minimizer_is_unique
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) :
    (∀ y, F.f F.minimizer ≤ F.f y) ∧
      (∀ y, F.f y = F.f F.minimizer → y = F.minimizer) := by
  apply stationary_unique_minimizer F.f (∇ F.f) (by norm_num : (0 : ℝ) < 1)
  · intro x y
    simpa using F.strong x y
  · exact F.minimizer_stationary

/-- The local gradient bound `‖∇f(z)‖ ≤ 9` on `Ball(2)` used in the upper
bound. -/
theorem NormalizedObjective.gradient_norm_le_nine
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    {z : Point d} (hz : ‖z‖ ≤ 2) :
    ‖∇ F.f z‖ ≤ 9 := by
  have hlip := F.gradient_lipschitz z F.minimizer
  rw [F.minimizer_stationary, sub_zero] at hlip
  have hdist : ‖z - F.minimizer‖ ≤ 3 := by
    calc
      ‖z - F.minimizer‖ ≤ ‖z‖ + ‖F.minimizer‖ := norm_sub_le _ _
      _ ≤ 3 := by linarith [F.minimizer_mem]
  linarith

/-- The zero-query output `0` has uniformly bounded loss.  This is the
small-budget branch of the upper bound; the constant `9` is sufficient for
the saturated minimax rate. -/
theorem NormalizedObjective.zero_gap_le_nine
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) :
    F.f 0 - F.f F.minimizer ≤ 9 := by
  let s : Set (Point d) := Metric.closedBall 0 1
  have hzero : (0 : Point d) ∈ s := by simp [s]
  have hmin : F.minimizer ∈ s := by
    simpa [s, Metric.mem_closedBall, dist_zero_right] using F.minimizer_mem
  have hdiff : Differentiable ℝ F.f :=
    F.smooth.differentiable (by
      norm_cast
      exact Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) o.two_le_k))
  have hmv := (convex_closedBall (0 : Point d) 1).norm_image_sub_le_of_norm_fderiv_le
    (fun z _hz ↦ hdiff z)
    (fun z hz ↦ by
      calc
        ‖fderiv ℝ F.f z‖ =
            ‖(InnerProductSpace.toDual ℝ (Point d)).symm (fderiv ℝ F.f z)‖ := by
          symm
          exact (InnerProductSpace.toDual ℝ (Point d)).symm.norm_map _
        _ = ‖∇ F.f z‖ := rfl
        _ ≤ 9 := F.gradient_norm_le_nine
          (show ‖z‖ ≤ 2 by
            have hz1 : ‖z‖ ≤ 1 := by
              simpa [s, Metric.mem_closedBall, dist_zero_right] using hz
            linarith))
    hzero hmin
  have hnorm : ‖F.minimizer - (0 : Point d)‖ ≤ 1 := by simpa using F.minimizer_mem
  calc
    F.f 0 - F.f F.minimizer ≤ |F.f F.minimizer - F.f 0| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    _ = ‖F.f F.minimizer - F.f 0‖ := by rw [Real.norm_eq_abs]
    _ ≤ 9 * ‖F.minimizer - (0 : Point d)‖ := hmv
    _ ≤ 9 := by nlinarith

/-- Objective gaps are nonnegative because `minimizer` is globally minimal. -/
theorem NormalizedObjective.gap_nonneg
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    (x : Point d) :
    0 ≤ F.f x - F.f F.minimizer := by
  have hmin := F.minimizer_is_unique.1 x
  linarith

/-- Every point in the unit ball has loss at most `18`.  This boundedness is
used to integrate the projected-SGD recurrence over a random current state. -/
theorem NormalizedObjective.gap_le_eighteen_of_norm_le
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d)
    {x : Point d} (hx : ‖x‖ ≤ 1) :
    F.f x - F.f F.minimizer ≤ 18 := by
  let s : Set (Point d) := Metric.closedBall 0 1
  have hxmem : x ∈ s := by
    simpa [s, Metric.mem_closedBall, dist_zero_right] using hx
  have hmin : F.minimizer ∈ s := by
    simpa [s, Metric.mem_closedBall, dist_zero_right] using F.minimizer_mem
  have hdiff : Differentiable ℝ F.f :=
    F.smooth.differentiable (by
      norm_cast
      exact Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) o.two_le_k))
  have hmv := (convex_closedBall (0 : Point d) 1).norm_image_sub_le_of_norm_fderiv_le
    (fun z _hz ↦ hdiff z)
    (fun z hz ↦ by
      calc
        ‖fderiv ℝ F.f z‖ =
            ‖(InnerProductSpace.toDual ℝ (Point d)).symm (fderiv ℝ F.f z)‖ := by
          symm
          exact (InnerProductSpace.toDual ℝ (Point d)).symm.norm_map _
        _ = ‖∇ F.f z‖ := rfl
        _ ≤ 9 := F.gradient_norm_le_nine
          (show ‖z‖ ≤ 2 by
            have hz1 : ‖z‖ ≤ 1 := by
              simpa [s, Metric.mem_closedBall, dist_zero_right] using hz
            linarith))
    hxmem hmin
  have hdist : ‖x - F.minimizer‖ ≤ 2 := by
    calc
      ‖x - F.minimizer‖ ≤ ‖x‖ + ‖F.minimizer‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith [F.minimizer_mem]
  calc
    F.f x - F.f F.minimizer ≤ |F.f x - F.f F.minimizer| := le_abs_self _
    _ = ‖F.f x - F.f F.minimizer‖ := by rw [Real.norm_eq_abs]
    _ ≤ 9 * ‖x - F.minimizer‖ := by
      rw [norm_sub_rev (F.f x) (F.f F.minimizer)]
      simpa only [norm_sub_rev F.minimizer x] using hmv
    _ ≤ 18 := by nlinarith

/-- The normalized smoothness assumptions make the gradient a continuous
vector field. -/
theorem NormalizedObjective.gradient_continuous
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) :
    Continuous (∇ F.f) := by
  change Continuous (fun x ↦
    (InnerProductSpace.toDual ℝ (Point d)).symm (fderiv ℝ F.f x))
  exact (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
    (F.smooth.continuous_fderiv (by
      norm_cast
      exact Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) o.two_le_k)))

/-- Differentiating once leaves `k - 1` continuous derivatives of the
gradient. -/
theorem NormalizedObjective.gradient_contDiff
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) :
    ContDiff ℝ (↑(o.k - 1) : ℕ∞ω) (∇ F.f) := by
  change ContDiff ℝ (↑(o.k - 1) : ℕ∞ω) (fun x ↦
    (InnerProductSpace.toDual ℝ (Point d)).symm (fderiv ℝ F.f x))
  have hk1 : 1 ≤ o.k := le_trans (by omega) o.two_le_k
  have hfd : ContDiff ℝ (↑(o.k - 1) : ℕ∞ω) (fderiv ℝ F.f) := by
    apply F.smooth.fderiv_right
    exact_mod_cast (show o.k - 1 + 1 ≤ o.k by omega)
  exact hfd.continuousLinearMap_comp
    (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The first-order strong-convexity field implies ordinary convexity on the
whole Euclidean space. -/
theorem NormalizedObjective.convexOn_univ
    {o : SmoothnessOrder} {d : ℕ} (F : NormalizedObjective o d) :
    ConvexOn ℝ Set.univ F.f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z : Point d := a • x + b • y
  have hxStrong := F.strong z x
  have hyStrong := F.strong z y
  have hx : F.f z + ⟪∇ F.f z, x - z⟫_ℝ ≤ F.f x := by
    nlinarith [sq_nonneg ‖x - z‖]
  have hy : F.f z + ⟪∇ F.f z, y - z⟫_ℝ ≤ F.f y := by
    nlinarith [sq_nonneg ‖y - z‖]
  have hweighted := add_le_add
    (mul_le_mul_of_nonneg_left hx ha)
    (mul_le_mul_of_nonneg_left hy hb)
  have hcancel : a • (x - z) + b • (y - z) = 0 := by
    have hbEq : b = 1 - a := by linarith
    subst b
    dsimp [z]
    module
  have hinner :
      a * ⟪∇ F.f z, x - z⟫_ℝ + b * ⟪∇ F.f z, y - z⟫_ℝ = 0 := by
    calc
      a * ⟪∇ F.f z, x - z⟫_ℝ + b * ⟪∇ F.f z, y - z⟫_ℝ =
          ⟪∇ F.f z, a • (x - z) + b • (y - z)⟫_ℝ := by
            simp only [inner_add_right, real_inner_smul_right]
      _ = 0 := by rw [hcancel, inner_zero_right]
  change F.f z ≤ a * F.f x + b * F.f y
  calc
    F.f z = (a + b) * F.f z := by rw [hab]; simp
    _ = a * F.f z + b * F.f z := by ring
    _ = a * F.f z + b * F.f z +
        (a * ⟪∇ F.f z, x - z⟫_ℝ + b * ⟪∇ F.f z, y - z⟫_ℝ) := by
          rw [hinner, add_zero]
    _ = a * (F.f z + ⟪∇ F.f z, x - z⟫_ℝ) +
        b * (F.f z + ⟪∇ F.f z, y - z⟫_ℝ) := by ring
    _ ≤ a * F.f x + b * F.f y := hweighted

end

end NoisyZO
