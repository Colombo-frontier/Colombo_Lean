import NoisyZO.LowerAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Numerical endgame of the lower bound

This module checks the constants following the adaptive KL and Assouad steps:
the chosen information budget gives `Kbar ≤ 1/8`, hence at least `3d/8`
average Hamming errors, and strong convexity converts this to the paper's
`3 a² h^(2β-2) / 64` loss scale.
-/

open scoped BigOperators

namespace NoisyZO

theorem KL_budget_le_one_eighth
    {a T d h β : ℝ} (ha : 0 < a) (hT : 0 < T) (hd : 0 < d)
    (hhpow : h ^ (2 * β) ≤ d ^ 2 / (16 * a ^ 2 * T)) :
    2 * a ^ 2 * T * h ^ (2 * β) / d ^ 2 ≤ (1 / 8 : ℝ) := by
  calc
    2 * a ^ 2 * T * h ^ (2 * β) / d ^ 2 ≤
        2 * a ^ 2 * T * (d ^ 2 / (16 * a ^ 2 * T)) / d ^ 2 := by
          gcongr
    _ = (1 / 8 : ℝ) := by
          field_simp [ne_of_gt ha, ne_of_gt hT, ne_of_gt hd]
          ring

theorem sqrt_half_le_quarter {Kbar : ℝ}
    (hK0 : 0 ≤ Kbar) (hK : Kbar ≤ 1 / 8) :
    Real.sqrt (Kbar / 2) ≤ (1 / 4 : ℝ) := by
  have harg : 0 ≤ Kbar / 2 := by positivity
  have hsquare := Real.sq_sqrt harg
  have hsqrt0 := Real.sqrt_nonneg (Kbar / 2)
  nlinarith

theorem assouad_three_eighths {N Kbar : ℝ}
    (hN : 0 ≤ N) (hK0 : 0 ≤ Kbar) (hK : Kbar ≤ 1 / 8) :
    3 * N / 8 ≤ N / 2 * (1 - Real.sqrt (Kbar / 2)) := by
  have hsqrt := sqrt_half_le_quarter hK0 hK
  nlinarith

/-- Average Hamming error converted to average strongly-convex loss. -/
theorem averaged_hamming_to_loss {d : ℕ}
    (risk ham : Hypercube d → ℝ) (c : ℝ)
    (hpoint : ∀ s, (c ^ 2 / 2) * ham s ≤ risk s)
    (hham : (2 : ℝ) ^ d * (3 * d / 8) ≤ ∑ s : Hypercube d, ham s) :
    3 * c ^ 2 * d / 16 ≤
      (∑ s : Hypercube d, risk s) / (2 : ℝ) ^ d := by
  have hrisk :
      (c ^ 2 / 2) * (∑ s : Hypercube d, ham s) ≤
        ∑ s : Hypercube d, risk s := by
    calc
      (c ^ 2 / 2) * (∑ s : Hypercube d, ham s) =
          ∑ s : Hypercube d, (c ^ 2 / 2) * ham s := by
            rw [Finset.mul_sum]
      _ ≤ ∑ s : Hypercube d, risk s :=
        Finset.sum_le_sum fun s _ => hpoint s
  have hcoef : 0 ≤ c ^ 2 / 2 := by positivity
  have hpow : 0 < (2 : ℝ) ^ d := by positivity
  apply (le_div_iff₀ hpow).2
  nlinarith [mul_le_mul_of_nonneg_left hham hcoef]

/-- Substitution of the hard-center coordinate magnitude. -/
theorem hard_center_loss_constant {a r d c : ℝ}
    (hc : c ^ 2 * d = a ^ 2 * r ^ 2 / 4) :
    3 * c ^ 2 * d / 16 = 3 * a ^ 2 * r ^ 2 / 64 := by
  calc
    3 * c ^ 2 * d / 16 = 3 * (c ^ 2 * d) / 16 := by ring
    _ = 3 * a ^ 2 * r ^ 2 / 64 := by rw [hc]; ring

end NoisyZO
