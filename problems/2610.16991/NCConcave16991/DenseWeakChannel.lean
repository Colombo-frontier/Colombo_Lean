import NCConcave16991.DenseWeakEntropy
import NCConcave16991.DenseWeakArithmetic

/-! # The literal one-cell binary channel in dense weak hiding

Both entropy and posterior-energy estimates are proved for the actual
Bernoulli channel probabilities. Identifying this channel with the posterior
of the full adaptive fixed-table experiment remains a separate obligation.
-/

noncomputable section

namespace NCConcave16991.DenseWeakHiding

def nextSignProbability (n m d σ θ : ℝ) : ℝ :=
  (n + m * θ - d - σ) / (2 * (n - d))

theorem nextSignProbability_difference {n m d σ : ℝ} (hnd : d < n) :
    nextSignProbability n m d σ 1 - nextSignProbability n m d σ (-1) = m / (n - d) := by
  unfold nextSignProbability
  field_simp
  <;> ring

theorem nextSign_entropyGap_le {n m d σ π : ℝ}
    (hm : 0 ≤ m) (hd : 0 ≤ d) (hnd : d < n) (hbudget : 8 * m + 9 * d ≤ n)
    (hσ : |σ| ≤ d) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    binaryEntropy (π * nextSignProbability n m d σ 1 +
      (1 - π) * nextSignProbability n m d σ (-1)) -
      (π * binaryEntropy (nextSignProbability n m d σ 1) +
        (1 - π) * binaryEntropy (nextSignProbability n m d σ (-1))) ≤
      (32 / 63 : ℝ) * (m / (n - d)) ^ 2 := by
  have hp := nextSignProbability_mem_Icc hm hd hnd hbudget hσ (Or.inl rfl)
  have hq := nextSignProbability_mem_Icc hm hd hnd hbudget hσ (Or.inr rfl)
  have hh := binaryEntropy_jensenGap_le hπ0 hπ1 hp hq
  have hb := binaryInformation_coefficient_bound (x :=
    nextSignProbability n m d σ 1 - nextSignProbability n m d σ (-1)) hπ0 hπ1
  change _ ≤ (128 / 63 : ℝ) * π * (1 - π) *
    (nextSignProbability n m d σ 1 - nextSignProbability n m d σ (-1)) ^ 2 at hh
  have hg := hh.trans hb
  rwa [nextSignProbability_difference hnd] at hg

def channelMixture (π p q : ℝ) : ℝ := π * p + (1 - π) * q

def posteriorPositive (π p q : ℝ) : ℝ := π * p / channelMixture π p q
def posteriorNegative (π p q : ℝ) : ℝ := π * (1 - p) / (1 - channelMixture π p q)

theorem channelMixture_mem_Icc {π p q : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hp : p ∈ Set.Icc (7 / 16 : ℝ) (9 / 16))
    (hq : q ∈ Set.Icc (7 / 16 : ℝ) (9 / 16)) :
    channelMixture π p q ∈ Set.Icc (7 / 16 : ℝ) (9 / 16) := by
  have h := (convex_Icc (7 / 16 : ℝ) (9 / 16)) hp hq hπ0
    (sub_nonneg.mpr hπ1) (by ring : π + (1 - π) = 1)
  exact h

/-- Exact Bayes posterior-energy increment of a literal binary experiment. -/
theorem posterior_energy_identity {π p q : ℝ}
    (h0 : channelMixture π p q ≠ 0) (h1 : 1 - channelMixture π p q ≠ 0) :
    channelMixture π p q * (2 * posteriorPositive π p q - 1) ^ 2 +
      (1 - channelMixture π p q) * (2 * posteriorNegative π p q - 1) ^ 2 -
      (2 * π - 1) ^ 2 =
      (4 * π ^ 2 * (1 - π) ^ 2 / (channelMixture π p q * (1 - channelMixture π p q))) *
        (p - q) ^ 2 := by
  unfold posteriorPositive posteriorNegative
  field_simp
  unfold channelMixture
  ring

theorem posterior_energy_increment_le {π p q : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hp : p ∈ Set.Icc (7 / 16 : ℝ) (9 / 16))
    (hq : q ∈ Set.Icc (7 / 16 : ℝ) (9 / 16)) :
    channelMixture π p q * (2 * posteriorPositive π p q - 1) ^ 2 +
      (1 - channelMixture π p q) * (2 * posteriorNegative π p q - 1) ^ 2 -
      (2 * π - 1) ^ 2 ≤ (64 / 63 : ℝ) * (p - q) ^ 2 := by
  have hm := channelMixture_mem_Icc hπ0 hπ1 hp hq
  have h0 : 0 < channelMixture π p q := by linarith [hm.1]
  have h1 : 0 < 1 - channelMixture π p q := by linarith [hm.2]
  rw [posterior_energy_identity h0.ne' h1.ne']
  have hprod0 := mul_nonneg hπ0 (sub_nonneg.mpr hπ1)
  have hprod1 : π * (1 - π) ≤ 1 / 4 := by nlinarith [sq_nonneg (π - 1 / 2)]
  have hsq := pow_le_pow_left₀ hprod0 hprod1 2
  have hvar := bernoulliVariance_lower hm
  have hcoef : 4 * π ^ 2 * (1 - π) ^ 2 /
      (channelMixture π p q * (1 - channelMixture π p q)) ≤ (64 / 63 : ℝ) := by
    apply (div_le_iff₀ (mul_pos h0 h1)).2
    nlinarith only [hsq, hvar]
  exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

end NCConcave16991.DenseWeakHiding
