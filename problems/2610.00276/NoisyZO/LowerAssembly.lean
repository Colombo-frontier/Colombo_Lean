import NoisyZO.AdaptiveKLSum
import NoisyZO.AssouadTesting

/-!
# Adaptive lower-bound assembly

This file joins the pointwise summed-signal estimate, the adaptive Gaussian KL
identity, and Assouad--Pinsker testing.  The probabilistic semantics enter only
through the two standard edge hypotheses; all budget and hypercube averaging
is discharged here.
-/

open scoped BigOperators

namespace NoisyZO

theorem adaptive_assouad_assembly {d T : ℕ} (hd : 0 < d)
    (signal : Hypercube d → Fin d → Fin T → ℝ)
    (KL err tv : Hypercube d → Fin d → ℝ) (C : ℝ)
    (hGaussianKL : ∀ s i,
      KL s i = (1 / 2 : ℝ) * ∑ t : Fin T, (signal s i t) ^ 2)
    (hsignal : ∀ s t, ∑ i : Fin d, (signal s i t) ^ 2 ≤ C)
    (hedge : ∀ s i,
      1 - tv s i ≤ err s i + err (flipHypercube s i) i)
    (hpinsker : ∀ s i, tv s i ≤ Real.sqrt (KL s i / 2)) :
    ((((2 : ℝ) ^ d * d) / 2) *
        (1 - Real.sqrt ((T * C / (2 * d)) / 2))) ≤
      ∑ s : Hypercube d, ∑ i : Fin d, err s i := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hN : 0 < (d : ℝ) * (2 : ℝ) ^ d := by positivity
  have hKLnonneg : ∀ s i, 0 ≤ KL s i := by
    intro s i
    rw [hGaussianKL]
    positivity
  have hTC : 0 ≤ (T : ℝ) * C := by
    by_cases hT : T = 0
    · simp [hT]
    · let s : Hypercube d := fun _ => false
      let t0 : Fin T := ⟨0, Nat.pos_of_ne_zero hT⟩
      have hs := hsignal s t0
      have hC : 0 ≤ C :=
        (Finset.sum_nonneg fun i _ => sq_nonneg (signal s i t0)).trans hs
      positivity
  have hKbar : 0 ≤ T * C / (2 * d) := by positivity
  have havg := adaptive_KL_average_bound hd signal KL C hGaussianKL hsignal
  have htotal :
      (∑ s : Hypercube d, ∑ i : Fin d, KL s i) ≤
        ((2 : ℝ) ^ d * d) * (T * C / (2 * d)) := by
    have hmul := (div_le_iff₀ hN).mp havg
    nlinarith
  exact assouad_pinsker_bound err tv KL (T * C / (2 * d)) hKbar
    hKLnonneg hedge hpinsker htotal

end NoisyZO
