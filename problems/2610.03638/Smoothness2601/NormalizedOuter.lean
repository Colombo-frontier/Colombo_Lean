import Bilevel.JointDerivative
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The normalized outer steps in Appendix `app:upper`: direction inequality,
actual smooth descent, deterministic travel, and finite-horizon telescoping. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Smoothness2601.NormalizedOuter
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def direction (z : X) : X := ‖z‖⁻¹ • z

@[simp] theorem direction_zero : direction (0 : X) = 0 := by simp [direction]

theorem direction_norm_le (z : X) : ‖direction z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [direction, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

theorem self_inner_direction (z : X) : ⟪z, direction z⟫ = ‖z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [direction, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    ring

/-- The article's inequality holds also at the zero estimated direction. -/
theorem direction_alignment (a z : X) : ‖a‖ - 2 * ‖z-a‖ ≤ ⟪a, direction z⟫ := by
  have hc : ⟪z-a, direction z⟫ ≤ ‖z-a‖ :=
    (real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left (direction_norm_le z)
      (norm_nonneg _)).trans_eq (mul_one _))
  rw [inner_sub_left, self_inner_direction] at hc
  have ht : ‖a‖ ≤ ‖z-a‖ + ‖z‖ := by
    rw [norm_sub_rev]
    simpa only [sub_add_cancel] using norm_add_le (a-z) z
  linarith

def step (x q : X) (η : ℝ) : X := x - η • direction q

theorem step_distance (x q : X) {η : ℝ} (hη : 0 ≤ η) : ‖step x q η - x‖ ≤ η := by
  have he : step x q η - x = -(η • direction q) := by unfold step; abel
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
  exact (mul_le_mul_of_nonneg_left (direction_norm_le q) hη).trans_eq (mul_one _)

variable [CompleteSpace X]

theorem smooth_descent (f : X → ℝ) (g : X → X) {L η : ℝ} (hL : 0 ≤ L)
    (hη : 0 ≤ η) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x q : X) :
    f (step x q η) ≤ f x - η*‖g x‖ + 2*η*‖q-g x‖ + L*η^2/2 := by
  have ht := Bilevel.JointDerivative.gradient_taylor f g L hf hg x (-(η • direction q))
  have ha := (le_abs_self (f (x + -(η • direction q)) - f x -
    ⟪g x, -(η • direction q)⟫)).trans (by simpa only [Real.norm_eq_abs] using ht)
  have hd := step_distance x q hη
  have he : x + -(η • direction q) = step x q η := by simp only [step, sub_eq_add_neg]
  rw [he, inner_neg_right, real_inner_smul_right] at ha
  have hn : ‖-(η • direction q)‖^2 ≤ η^2 := by
    have hnorm : ‖-(η • direction q)‖ ≤ η := by
      simpa only [step, sub_sub_cancel_left, norm_neg] using hd
    exact (sq_le_sq₀ (norm_nonneg _) hη).mpr hnorm
  have hquad := mul_le_mul_of_nonneg_left hn (show 0 ≤ L/2 by positivity)
  have halign := mul_le_mul_of_nonneg_left (direction_alignment (g x) q) hη
  linarith

omit [CompleteSpace X] in
theorem travel_bound (x q : ℕ → X) {η : ℝ} (hη : 0 ≤ η)
    (hstep : ∀ k, x (k+1) = step (x k) (q k) η) (n : ℕ) :
    ‖x n-x 0‖ ≤ (n : ℝ)*η := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ‖(x (n+1)-x n)+(x n-x 0)‖ := by congr 1; abel
      _ ≤ ‖x (n+1)-x n‖+‖x n-x 0‖ := norm_add_le _ _
      _ ≤ η+(n:ℝ)*η := add_le_add (by rw [hstep]; exact step_distance _ _ hη) ih
      _ = _ := by push_cast; ring

/-- Deterministic pathwise inequality before expectation is taken. -/
theorem telescope (f : X → ℝ) (g : X → X) {L η : ℝ} (hL : 0 ≤ L)
    (hη : 0 ≤ η) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x q : ℕ → X)
    (hstep : ∀ k, x (k+1) = step (x k) (q k) η) (n : ℕ) :
    η * (∑ k ∈ Finset.range n, ‖g (x k)‖) ≤ f (x 0)-f (x n) +
      2*η*(∑ k ∈ Finset.range n, ‖q k-g (x k)‖) + (n:ℝ)*L*η^2/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := smooth_descent f g hL hη hf hg (x n) (q n)
    rw [← hstep n] at hs
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    nlinarith

theorem averaged_norm_bound (f : X → ℝ) (g : X → X) {L η Δ floor δ : ℝ}
    (hL : 0 ≤ L) (hη : 0 < η) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x q : ℕ → X)
    (hstep : ∀ k, x (k+1) = step (x k) (q k) η)
    (hlower : ∀ z, floor ≤ f z) (hgap : f (x 0)-floor ≤ Δ)
    (n : ℕ) (hn : 0 < n)
    (herr : (∑ k ∈ Finset.range n, ‖q k-g (x k)‖) ≤ (n:ℝ)*δ) :
    (∑ k ∈ Finset.range n, ‖g (x k)‖) / n ≤ Δ/((n:ℝ)*η) + 2*δ + L*η/2 := by
  have ht := telescope f g hL hη.le hf hg x q hstep n
  have he := mul_le_mul_of_nonneg_left herr (show 0 ≤ 2*η by positivity)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (div_le_iff₀ hn').mpr
  apply (mul_le_mul_left hη).mp
  have hid : η * ((Δ / ((n:ℝ)*η) + 2*δ + L*η/2) * (n:ℝ)) =
      Δ+2*η*((n:ℝ)*δ)+(n:ℝ)*L*η^2/2 := by field_simp; ring
  rw [hid]
  linarith [hlower (x n)]

end Smoothness2601.NormalizedOuter
