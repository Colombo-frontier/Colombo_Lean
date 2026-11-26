import FullJet.Opacity
import Mathlib.Data.Nat.Choose.Sum

open scoped ContDiff BigOperators

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Leibniz's rule preserves a single inverse-bias factor.
The radial and gate derivative bounds are explicit premises of this lemma. -/
theorem local_link_norm_bound {U V : E → ℝ} (k : ℕ) (x : E) (C D ρ : ℝ)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hρ : 0 < ρ)
    (hUb : ∀ r ≤ k, ‖iteratedFDeriv ℝ r U x‖ ≤ C)
    (hVb : ∀ r ≤ k, ‖iteratedFDeriv ℝ r V x‖ ≤ D / ρ) :
    ‖iteratedFDeriv ℝ k (fun y => U y * V y) x‖ ≤ (2 : ℝ) ^ k * C * D / ρ := by
  have hn : (k : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)
  have hsum : ∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) = (2 : ℝ) ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  calc
    _ ≤ ∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) *
        ‖iteratedFDeriv ℝ r U x‖ * ‖iteratedFDeriv ℝ (k - r) V x‖ :=
      norm_iteratedFDeriv_mul_le hU hV x hn
    _ ≤ ∑ r ∈ Finset.range (k + 1), (k.choose r : ℝ) * C * (D / ρ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hUb r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))) (by positivity))
        (hVb (k - r) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]; ring

end FullJet
