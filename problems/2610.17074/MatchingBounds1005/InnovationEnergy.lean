import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Deterministic innovation energy

This file proves the nested-projection and Cauchy--Schwarz calculations used
in `gau:cor:kl-bound` of `1005 (2).tex`. These are statements about actual
orthogonal projections in finite-dimensional real inner-product spaces.
They do not assume or establish an adaptive Gaussian posterior or a KL formula.
-/

noncomputable section

open scoped BigOperators

namespace MatchingBounds1005.InnovationEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Orthogonal projection, with its value regarded in the ambient space. -/
def proj (V : Submodule ℝ E) (x : E) : E := V.orthogonalProjection x

@[simp] theorem proj_mem (V : Submodule ℝ E) (x : E) : proj V x ∈ V :=
  (V.orthogonalProjection x).property

@[simp] theorem proj_zero (V : Submodule ℝ E) : proj V 0 = 0 := by
  simp [proj]

@[simp] theorem proj_bot (x : E) : proj (⊥ : Submodule ℝ E) x = 0 := by
  simp [proj]

theorem proj_residual_inner (V : Submodule ℝ E) (x y : E) (hy : y ∈ V) :
    @inner ℝ E _ (x - proj V x) y = 0 :=
  Submodule.orthogonalProjection_inner_eq_zero x y hy

/-- The new orthogonal measurement component is the difference of the two
nested projections. -/
theorem proj_increment {V W : Submodule ℝ E} (hVW : V ≤ W) (x : E) :
    proj (W ⊓ Vᗮ) x = proj W x - proj V x := by
  apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero
  · constructor
    · exact W.sub_mem (proj_mem W x) (hVW (proj_mem V x))
    · apply (V.mem_orthogonal' _).2
      intro y hy
      have h₁ := proj_residual_inner V x y hy
      have h₂ := proj_residual_inner W x y (hVW hy)
      simp only [inner_sub_left] at h₁ h₂ ⊢
      linarith
  · intro y hy
    have h₁ := proj_residual_inner W x y hy.1
    have h₂ : @inner ℝ E _ (proj V x) y = 0 :=
      Submodule.inner_right_of_mem_orthogonal (proj_mem V x) hy.2
    simp only [inner_sub_left] at h₁ ⊢
    linarith

/-- Pythagoras for one innovation increment. -/
theorem increment_energy {V W : Submodule ℝ E} (hVW : V ≤ W) (x : E) :
    ‖proj (W ⊓ Vᗮ) x‖ ^ 2 = ‖proj W x‖ ^ 2 - ‖proj V x‖ ^ 2 := by
  have horth : @inner ℝ E _ (proj V x) (proj (W ⊓ Vᗮ) x) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (proj_mem V x)
      (proj_mem (W ⊓ Vᗮ) x).2
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (proj V x) (proj (W ⊓ Vᗮ) x) horth
  rw [proj_increment hVW] at hp ⊢
  have heq : proj V x + (proj W x - proj V x) = proj W x := by abel
  rw [heq] at hp
  linarith

/-- Exact telescoping of innovations; the time index is zero-based. -/
theorem sum_innovation_energy (V : ℕ → Submodule ℝ E)
    (hV : Monotone V) (x : E) (n : ℕ) :
    (∑ t ∈ Finset.range n, ‖proj (V (t + 1) ⊓ (V t)ᗮ) x‖ ^ 2) =
      ‖proj (V n) x‖ ^ 2 - ‖proj (V 0) x‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, increment_energy (hV (Nat.le_succ n))]
    ring

/-- In particular, accumulated innovation energy is at most final observed
energy; no factor proportional to the number of queries is lost. -/
theorem sum_innovation_energy_le (V : ℕ → Submodule ℝ E)
    (hV : Monotone V) (x : E) (n : ℕ) :
    (∑ t ∈ Finset.range n, ‖proj (V (t + 1) ⊓ (V t)ᗮ) x‖ ^ 2) ≤
      ‖proj (V n) x‖ ^ 2 := by
  rw [sum_innovation_energy V hV]
  nlinarith [sq_nonneg ‖proj (V 0) x‖]

/-- With an initially empty observation space, the manuscript's telescoping
identity holds exactly. -/
theorem sum_innovation_energy_of_bot (V : ℕ → Submodule ℝ E)
    (hV : Monotone V) (hzero : V 0 = ⊥) (x : E) (n : ℕ) :
    (∑ t ∈ Finset.range n, ‖proj (V (t + 1) ⊓ (V t)ᗮ) x‖ ^ 2) =
      ‖proj (V n) x‖ ^ 2 := by
  rw [sum_innovation_energy V hV, hzero, proj_bot]
  simp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Finite-signal Cauchy--Schwarz, for arbitrary signal vectors. -/
theorem norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)

/-- Apply finite-signal Cauchy--Schwarz to actual projected signals. -/
theorem projected_signal_sum_energy {ι : Type*} (s : Finset ι)
    (V : Submodule ℝ E) (f : ι → E) (w : ℝ) :
    ‖proj V (w • ∑ i ∈ s, f i)‖ ^ 2 ≤
      (s.card : ℝ) * w ^ 2 * ∑ i ∈ s, ‖proj V (f i)‖ ^ 2 := by
  have hsum : proj V (∑ i ∈ s, f i) = ∑ i ∈ s, proj V (f i) := by
    simp [proj, map_sum]
  have hsmul : proj V (w • ∑ i ∈ s, f i) = w • proj V (∑ i ∈ s, f i) := by
    simp [proj]
  rw [hsmul, hsum, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h := norm_sum_sq_le_card s (fun i => proj V (f i))
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg w)]

/-- Truncation to the undisclosed prefix of a finite time horizon. -/
theorem sum_prefix_ite (a : ℕ → ℝ) {ell T : ℕ} (hell : ell ≤ T) :
    (∑ t ∈ Finset.range T, if t < ell then a t else 0) =
      ∑ t ∈ Finset.range ell, a t := by
  calc
    _ = ∑ t ∈ Finset.range ell, if t < ell then a t else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hell)
      intro t ht hnot
      simp only [Finset.mem_range] at hnot
      simp [hnot]
    _ = _ := Finset.sum_congr rfl (fun t ht => if_pos (Finset.mem_range.mp ht))

/-- Energy for a signal present precisely before its disclosure horizon. -/
theorem hidden_signal_energy_le (V : ℕ → Submodule ℝ E)
    (hV : Monotone V) (x : E) {ell T : ℕ} (hell : ell ≤ T) :
    (∑ t ∈ Finset.range T,
      ‖proj (V (t + 1) ⊓ (V t)ᗮ) (if t < ell then x else 0)‖ ^ 2) ≤
      ‖proj (V ell) x‖ ^ 2 := by
  have heq : (∑ t ∈ Finset.range T,
      ‖proj (V (t + 1) ⊓ (V t)ᗮ) (if t < ell then x else 0)‖ ^ 2) =
      ∑ t ∈ Finset.range T,
        if t < ell then ‖proj (V (t + 1) ⊓ (V t)ᗮ) x‖ ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> simp
  rw [heq, sum_prefix_ite _ hell]
  exact sum_innovation_energy_le V hV x ell

/-- The deterministic cumulative inequality underlying `gau:cor:kl-bound`.
The signals need not be orthogonal or rank-one. Each signal is removed at its
own disclosure horizon. This proves the `N w²` bound and the telescoping over
time, without assuming either of those conclusions as a hypothesis. -/
theorem cumulative_hidden_signal_energy {ι : Type*} (signals : Finset ι)
    (V : ℕ → Submodule ℝ E) (hV : Monotone V)
    (f : ι → E) (w : ℝ) (ell : ι → ℕ) (T : ℕ)
    (hell : ∀ s ∈ signals, ell s ≤ T) :
    (∑ t ∈ Finset.range T,
      ‖proj (V (t + 1) ⊓ (V t)ᗮ)
        (w • ∑ s ∈ signals, if t < ell s then f s else 0)‖ ^ 2) ≤
      (signals.card : ℝ) * w ^ 2 *
        ∑ s ∈ signals, ‖proj (V (ell s)) (f s)‖ ^ 2 := by
  calc
    _ ≤ ∑ t ∈ Finset.range T, (signals.card : ℝ) * w ^ 2 *
        ∑ s ∈ signals,
          ‖proj (V (t + 1) ⊓ (V t)ᗮ) (if t < ell s then f s else 0)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact projected_signal_sum_energy signals _ _ w
    _ = (signals.card : ℝ) * w ^ 2 *
        ∑ s ∈ signals, ∑ t ∈ Finset.range T,
          ‖proj (V (t + 1) ⊓ (V t)ᗮ) (if t < ell s then f s else 0)‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro s hs
        exact hidden_signal_energy_le V hV (f s) (hell s hs)
      · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg w)

end MatchingBounds1005.InnovationEnergy

