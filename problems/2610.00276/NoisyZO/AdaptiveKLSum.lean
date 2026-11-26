import Mathlib.Tactic

/-!
# Finite adaptive-KL summation

The measure-theoretic chain rule is represented by the exact per-edge
identity `hKL`.  From that identity onward, this file formalizes the crucial
order of summation: sum neighboring signals first, then average over hidden
hypercube vertices.  Adaptivity is harmless because `hsignal` is pointwise in
the realized query/history.
-/

open scoped BigOperators

namespace NoisyZO

abbrev Hypercube (d : ℕ) := Fin d → Bool

/-- Abstract form of equations (A.1)--(A.3) in the manuscript. -/
theorem adaptive_KL_total_bound {d T : ℕ}
    (signal : Hypercube d → Fin d → Fin T → ℝ)
    (KL : Hypercube d → Fin d → ℝ) (C : ℝ)
    (hKL : ∀ s i, KL s i = (1 / 2 : ℝ) * ∑ t : Fin T, (signal s i t) ^ 2)
    (hsignal : ∀ s t, ∑ i : Fin d, (signal s i t) ^ 2 ≤ C) :
    (∑ s : Hypercube d, ∑ i : Fin d, KL s i) ≤
      (2 : ℝ) ^ d * T * C / 2 := by
  calc
    (∑ s : Hypercube d, ∑ i : Fin d, KL s i) =
        (1 / 2 : ℝ) *
          (∑ s : Hypercube d, ∑ i : Fin d, ∑ t : Fin T, (signal s i t) ^ 2) := by
            simp_rw [hKL, Finset.mul_sum]
    _ = (1 / 2 : ℝ) *
          (∑ s : Hypercube d, ∑ t : Fin T, ∑ i : Fin d, (signal s i t) ^ 2) := by
            congr 1
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.sum_comm]
    _ ≤ (1 / 2 : ℝ) * (∑ _s : Hypercube d, ∑ _t : Fin T, C) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply Finset.sum_le_sum
            intro s _
            exact Finset.sum_le_sum (fun t _ => hsignal s t)
    _ = (2 : ℝ) ^ d * T * C / 2 := by
            simp
            ring

/-- Division by the number `d * 2^d` of directed hypercube edges. -/
theorem adaptive_KL_average_bound {d T : ℕ} (hd : 0 < d)
    (signal : Hypercube d → Fin d → Fin T → ℝ)
    (KL : Hypercube d → Fin d → ℝ) (C : ℝ)
    (hKL : ∀ s i, KL s i = (1 / 2 : ℝ) * ∑ t : Fin T, (signal s i t) ^ 2)
    (hsignal : ∀ s t, ∑ i : Fin d, (signal s i t) ^ 2 ≤ C) :
    (∑ s : Hypercube d, ∑ i : Fin d, KL s i) /
        ((d : ℝ) * (2 : ℝ) ^ d) ≤
      T * C / (2 * d) := by
  have htotal := adaptive_KL_total_bound signal KL C hKL hsignal
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hpow : 0 < (2 : ℝ) ^ d := by positivity
  apply (div_le_iff₀ (mul_pos hdR hpow)).2
  calc
    (∑ s : Hypercube d, ∑ i : Fin d, KL s i) ≤
        (2 : ℝ) ^ d * T * C / 2 := htotal
    _ = T * C / (2 * d) * ((d : ℝ) * (2 : ℝ) ^ d) := by
      field_simp [ne_of_gt hdR]

end NoisyZO
