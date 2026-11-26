import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Scalar consequence of the projected-subgradient recurrence

This module proves the summation and best-iterate step of `prop:upper`.
It does not prove the geometric one-step recurrence for a hyperbolic algorithm.
-/

namespace Geode

open scoped BigOperators

/-- The exact finite telescoping calculation, before discarding the terminal
squared distance. No positivity assumptions are needed for this step. -/
theorem upper_recurrence_sum (D gap : ℕ → ℝ) (α ζ L : ℝ) (N : ℕ)
    (hstep : ∀ j < N, D (j + 1) ≤ D j - 2 * α * gap j + ζ * α ^ 2 * L ^ 2) :
    2 * α * (∑ j ∈ Finset.range N, gap j) ≤
      D 0 - D N + (N : ℝ) * ζ * α ^ 2 * L ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self N)))
    have hn := hstep N (Nat.lt_succ_self N)
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

/-- A finite recurrence implies that one of the charged query gaps is small.
The `gap` is unrestricted: it need not itself be assumed nonnegative. -/
theorem upper_recurrence_best (D gap : ℕ → ℝ) (α ζ L R : ℝ) (N : ℕ)
    (hN : 0 < N) (hα : 0 < α)
    (hstart : D 0 ≤ R ^ 2) (hend : 0 ≤ D N)
    (hstep : ∀ j < N, D (j + 1) ≤ D j - 2 * α * gap j + ζ * α ^ 2 * L ^ 2) :
    ∃ j < N, gap j ≤ R ^ 2 / (2 * α * (N : ℝ)) + ζ * α * L ^ 2 / 2 := by
  let B := R ^ 2 / (2 * α * (N : ℝ)) + ζ * α * L ^ 2 / 2
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsum := upper_recurrence_sum D gap α ζ L N hstep
  have hid : 2 * α * ((N : ℝ) * B) =
      R ^ 2 + (N : ℝ) * ζ * α ^ 2 * L ^ 2 := by
    dsimp [B]
    field_simp [ne_of_gt hα, ne_of_gt hNr]
    ring
  have hs : (∑ j ∈ Finset.range N, gap j) ≤
      ∑ _j ∈ Finset.range N, B := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    nlinarith
  obtain ⟨j, hj, hb⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr hN.ne') hs
  exact ⟨j, Finset.mem_range.mp hj, hb⟩

/-- The step-size substitution in the paper, as an exact real identity. -/
theorem upper_optimized_expression {ζ L R n : ℝ}
    (hζ : 0 < ζ) (hL : 0 < L) (hR : 0 < R) (hn : 0 < n) :
    R ^ 2 / (2 * (R / (L * Real.sqrt (ζ * n))) * n) +
      ζ * (R / (L * Real.sqrt (ζ * n))) * L ^ 2 / 2 =
      L * R * Real.sqrt (ζ / n) := by
  rw [Real.sqrt_mul hζ.le, Real.sqrt_div hζ.le]
  have hsζ : Real.sqrt ζ ≠ 0 := (Real.sqrt_pos.mpr hζ).ne'
  have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hsqζ := Real.sq_sqrt hζ.le
  have hsqn := Real.sq_sqrt hn.le
  generalize hs : Real.sqrt ζ = s at *
  generalize ht : Real.sqrt n = t at *
  rw [← hsqζ, ← hsqn]
  field_simp [hL.ne', hR.ne', hn.ne', hsζ, hsn]
  ring

/-- The optimized best-iterate estimate; the geometric recurrence remains an
explicit hypothesis, rather than an unverified implementation of an algorithm. -/
theorem upper_recurrence_optimized (D gap : ℕ → ℝ) (ζ L R : ℝ) (N : ℕ)
    (hN : 0 < N) (hζ : 0 < ζ) (hL : 0 < L) (hR : 0 < R)
    (hstart : D 0 ≤ R ^ 2) (hend : 0 ≤ D N)
    (hstep : ∀ j < N, D (j + 1) ≤ D j -
      2 * (R / (L * Real.sqrt (ζ * (N : ℝ)))) * gap j +
      ζ * (R / (L * Real.sqrt (ζ * (N : ℝ)))) ^ 2 * L ^ 2) :
    ∃ j < N, gap j ≤ L * R * Real.sqrt (ζ / (N : ℝ)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hα : 0 < R / (L * Real.sqrt (ζ * (N : ℝ))) := by positivity
  obtain ⟨j, hj, hb⟩ := upper_recurrence_best D gap _ ζ L R N hN hα hstart hend hstep
  rw [upper_optimized_expression hζ hL hR hNr] at hb
  exact ⟨j, hj, hb⟩

/-- The target objective gap follows once the number of charged iterates meets
the scalar budget. -/
theorem upper_recurrence_accuracy (D gap : ℕ → ℝ) (ζ L R ε : ℝ) (N : ℕ)
    (hN : 0 < N) (hζ : 0 < ζ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hbudget : ζ / ε ^ 2 ≤ (N : ℝ))
    (hstart : D 0 ≤ R ^ 2) (hend : 0 ≤ D N)
    (hstep : ∀ j < N, D (j + 1) ≤ D j -
      2 * (R / (L * Real.sqrt (ζ * (N : ℝ)))) * gap j +
      ζ * (R / (L * Real.sqrt (ζ * (N : ℝ)))) ^ 2 * L ^ 2) :
    ∃ j < N, gap j ≤ ε * L * R := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbudget' : ζ ≤ (N : ℝ) * ε ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hε)).mp hbudget
  have hs : Real.sqrt (ζ / (N : ℝ)) ≤ ε := by
    apply (Real.sqrt_le_left hε.le).mpr
    apply (div_le_iff₀ hNr).mpr
    nlinarith
  obtain ⟨j, hj, hb⟩ := upper_recurrence_optimized D gap ζ L R N hN hζ hL hR
    hstart hend hstep
  refine ⟨j, hj, hb.trans ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hs (mul_pos hL hR).le]

end Geode
