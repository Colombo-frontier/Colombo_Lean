import NCConcave16991.DenseWeakFiniteEntropy
import NCConcave16991.DenseWeakChannel
import Mathlib.Tactic.FinCases

/-! # Actual finite binary channel and its mutual information

The channel is a normalized nonnegative joint probability mass on two finite
bits. Its mutual information is proved equal to the binary entropy gap, and
then bounded at the paper's literal next-cell probabilities.
-/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

set_option backward.isDefEq.respectTransparency false

def bernoulliMass (p : ℝ) (i : Fin 2) : ℝ := if i = 0 then p else 1 - p

theorem bernoulliMass_nonneg {p : ℝ} (hp : p ∈ Set.Icc 0 1) (i : Fin 2) :
    0 ≤ bernoulliMass p i := by
  unfold bernoulliMass
  split_ifs
  · exact hp.1
  · exact sub_nonneg.mpr hp.2

theorem bernoulliMass_sum (p : ℝ) : ∑ i : Fin 2, bernoulliMass p i = 1 := by
  simp [Fin.sum_univ_two, bernoulliMass]

def centralBinaryChannel (π p q : ℝ) (hπ : π ∈ Set.Icc 0 1)
    (hp : p ∈ Set.Icc (7 / 16 : ℝ) (9 / 16))
    (hq : q ∈ Set.Icc (7 / 16 : ℝ) (9 / 16)) : FiniteLaw (Fin 2 × Fin 2) where
  mass := fun z ↦ bernoulliMass π z.1 * bernoulliMass (if z.1 = 0 then p else q) z.2
  nonneg := by
    intro z
    apply mul_nonneg (bernoulliMass_nonneg hπ z.1)
    apply bernoulliMass_nonneg
    split_ifs
    · exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
    · exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  sum_one := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, bernoulliMass] <;> ring

variable {π p q : ℝ} (hπ : π ∈ Set.Icc 0 1)
  (hp : p ∈ Set.Icc (7 / 16 : ℝ) (9 / 16))
  (hq : q ∈ Set.Icc (7 / 16 : ℝ) (9 / 16))

theorem centralBinaryChannel_fst_mass :
    (centralBinaryChannel π p q hπ hp hq).fst.mass = bernoulliMass π := by
  funext i
  fin_cases i <;>
    simp [FiniteLaw.fst, rowMass, centralBinaryChannel, Fin.sum_univ_two, bernoulliMass] <;> ring

theorem centralBinaryChannel_snd_mass :
    (centralBinaryChannel π p q hπ hp hq).snd.mass = bernoulliMass (channelMixture π p q) := by
  funext i
  fin_cases i <;>
    simp [FiniteLaw.snd, centralBinaryChannel, Fin.sum_univ_two, bernoulliMass, channelMixture] <;> ring

theorem bernoulliMass_entropy (p : ℝ) : finiteEntropy (bernoulliMass p) = binaryEntropy p := by
  simp [finiteEntropy, Fin.sum_univ_two, bernoulliMass, binaryEntropy]

theorem centralBinaryChannel_entropy :
    (centralBinaryChannel π p q hπ hp hq).entropy =
      binaryEntropy π + π * binaryEntropy p + (1 - π) * binaryEntropy q := by
  simp [FiniteLaw.entropy, finiteEntropy, centralBinaryChannel,
    Fintype.sum_prod_type, Fin.sum_univ_two, bernoulliMass,
    Real.negMulLog_mul, binaryEntropy] <;> ring

theorem centralBinaryChannel_mutualInformation :
    (centralBinaryChannel π p q hπ hp hq).mutualInformation =
      binaryEntropy (channelMixture π p q) -
        (π * binaryEntropy p + (1 - π) * binaryEntropy q) := by
  unfold FiniteLaw.mutualInformation
  rw [centralBinaryChannel_entropy]
  change finiteEntropy _ + finiteEntropy _ - _ = _
  rw [centralBinaryChannel_fst_mass, centralBinaryChannel_snd_mass,
    bernoulliMass_entropy, bernoulliMass_entropy]
  ring

/-- The one-cell information bound for the actual normalized joint law. -/
theorem nextSign_mutualInformation_le {n m d σ π : ℝ}
    (hm : 0 ≤ m) (hd : 0 ≤ d) (hnd : d < n) (hbudget : 8 * m + 9 * d ≤ n)
    (hσ : |σ| ≤ d) (hπ : π ∈ Set.Icc 0 1) :
    let p := nextSignProbability n m d σ 1
    let q := nextSignProbability n m d σ (-1)
    let hp := nextSignProbability_mem_Icc hm hd hnd hbudget hσ (Or.inl rfl)
    let hq := nextSignProbability_mem_Icc hm hd hnd hbudget hσ (Or.inr rfl)
    (centralBinaryChannel π p q hπ hp hq).mutualInformation ≤
      (32 / 63 : ℝ) * (m / (n - d)) ^ 2 := by
  dsimp only
  rw [centralBinaryChannel_mutualInformation]
  exact nextSign_entropyGap_le hm hd hnd hbudget hσ hπ.1 hπ.2

end NCConcave16991.DenseWeakHiding
