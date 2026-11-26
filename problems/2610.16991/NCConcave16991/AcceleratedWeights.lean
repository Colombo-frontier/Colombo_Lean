import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Constructed accelerated weights and their quadratic growth -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.Accelerated

/-- The positive solution of `τ a²=A+a`, selected by the quadratic formula. -/
def nextWeight (τ A : ℝ) : ℝ := (1 + Real.sqrt (1 + 4 * τ * A)) / (2 * τ)

 theorem nextWeight_pos {τ A : ℝ} (hτ : 0 < τ) (_hA : 0 ≤ A) : 0 < nextWeight τ A := by
  dsimp [nextWeight]
  exact div_pos (by linarith [Real.sqrt_nonneg (1 + 4 * τ * A)]) (by positivity)

 theorem nextWeight_identity {τ A : ℝ} (hτ : 0 < τ) (hA : 0 ≤ A) :
    τ * nextWeight τ A ^ 2 = A + nextWeight τ A := by
  have hr : 0 ≤ 1 + 4 * τ * A := by positivity
  have hs := Real.sq_sqrt hr
  have hs' := Real.sq_sqrt (show 0 ≤ 1 + τ * 4 * A by positivity)
  dsimp [nextWeight]
  field_simp [hτ.ne']
  nlinarith

/-- The actual accumulated accelerated mass, starting at zero. -/
def mass (τ : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => mass τ k + nextWeight τ (mass τ k)

def weight (τ : ℝ) (k : ℕ) : ℝ := nextWeight τ (mass τ k)

 theorem mass_nonneg {τ : ℝ} (hτ : 0 < τ) (k : ℕ) : 0 ≤ mass τ k := by
  induction k with
  | zero => rfl
  | succ k ih => exact add_nonneg ih (nextWeight_pos hτ ih).le

 theorem weight_pos {τ : ℝ} (hτ : 0 < τ) (k : ℕ) : 0 < weight τ k :=
  nextWeight_pos hτ (mass_nonneg hτ k)

 theorem mass_succ_pos {τ : ℝ} (hτ : 0 < τ) (k : ℕ) : 0 < mass τ (k + 1) :=
  add_pos_of_nonneg_of_pos (mass_nonneg hτ k) (weight_pos hτ k)

 theorem mass_succ (τ : ℝ) (k : ℕ) : mass τ (k + 1) = mass τ k + weight τ k := rfl

 theorem weight_identity {τ : ℝ} (hτ : 0 < τ) (k : ℕ) :
    τ * weight τ k ^ 2 = mass τ (k + 1) :=
  nextWeight_identity hτ (mass_nonneg hτ k)

 theorem mass_monotone {τ : ℝ} (hτ : 0 < τ) : Monotone (mass τ) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [mass_succ]
  exact le_add_of_nonneg_right (weight_pos hτ k).le

 theorem sum_weights (τ : ℝ) (K : ℕ) : ∑ k ∈ Finset.range K, weight τ k = mass τ K := by
  induction K with
  | zero => simp [mass]
  | succ K ih => rw [Finset.sum_range_succ, ih, mass_succ]

/-- The exact constructed masses have the source's `A_K≥(K+1)²/(4τ)` growth. -/
theorem mass_quadratic_lower {τ : ℝ} (hτ : 0 < τ) (k : ℕ) :
    ((k : ℝ) + 2) ^ 2 / (4 * τ) ≤ mass τ (k + 1) := by
  induction k with
  | zero =>
    simp only [mass, nextWeight, mul_zero, add_zero, Real.sqrt_one, Nat.cast_zero]
    apply (div_le_iff₀ (by positivity : 0 < 4 * τ)).mpr
    field_simp [hτ.ne']
    norm_num
  | succ k ih =>
    have hmass := (div_le_iff₀ (by positivity : 0 < 4 * τ)).mp ih
    have hroot : (k : ℝ) + 2 ≤ Real.sqrt (1 + 4 * τ * mass τ (k + 1)) :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    have hw : ((k : ℝ) + 3) / (2 * τ) ≤ weight τ (k + 1) := by
      dsimp [weight, nextWeight]
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * τ)).mpr
      linarith
    have hw' := (div_le_iff₀ (by positivity : 0 < 2 * τ)).mp hw
    rw [mass_succ]
    apply (div_le_iff₀ (by positivity : 0 < 4 * τ)).mpr
    push_cast
    nlinarith

 theorem inverse_mass_bound {τ : ℝ} (hτ : 0 < τ) {K : ℕ} (hK : 0 < K) :
    1 / (2 * mass τ K) ≤ 2 * τ / ((K : ℝ) + 1) ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hK)
  have hm := mass_quadratic_lower hτ k
  have hp := mass_succ_pos hτ k
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hd := (div_le_iff₀ (by positivity : 0 < 4 * τ)).mp hm
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * mass τ (k + 1))
    (by positivity : 0 < (((k + 1 : ℕ) : ℝ) + 1) ^ 2)).mpr
  push_cast
  nlinarith

end NCConcave16991.Accelerated


