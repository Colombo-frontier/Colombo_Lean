import LowRank.TailPowerBudget

/-! A small optimal tail power forces a lower spectral cutoff after
discarding enough additional directions. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators
noncomputable section

theorem optimalSchattenPower_eq_tail_sum {a b k : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hk : k ≤ b) {p : ℝ} (hp : 0 < p) :
    optimalSchattenPower p A k =
      ∑ i : Fin (b - k), sp.value (i.castLE (Nat.sub_le b k)) ^ (p / 2) := by
  rw [optimalSchattenPower_eq_bottom_of_le hp A hk]
  unfold bottomPowerTrace
  rw [(orderedMatrixSpectrum (rightGram_posSemidef A).isHermitian).value_unique sp]

theorem optimalSchattenPower_ge_tail_count {a b k t : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hk : k ≤ b)
    (i : Fin b) (hi : i.val + t ≤ b - k) {p : ℝ} (hp : 0 < p) :
    (t : ℝ) * sp.value i ^ (p / 2) ≤ optimalSchattenPower p A k := by
  let f : Fin t → Fin (b - k) := fun j => ⟨i.val + j.val, by have hj := j.isLt; omega⟩
  have hf : Function.Injective f := by
    intro j l h
    apply Fin.ext
    have hval := congrArg Fin.val h
    change i.val + j.val = i.val + l.val at hval
    omega
  rw [optimalSchattenPower_eq_tail_sum A sp hk hp]
  calc
    _ = ∑ _ : Fin t, sp.value i ^ (p / 2) := by simp
    _ ≤ ∑ j : Fin t, sp.value ((f j).castLE (Nat.sub_le b k)) ^ (p / 2) := by
      apply Finset.sum_le_sum
      intro j _
      apply Real.rpow_le_rpow (sp.value_nonneg (rightGram_posSemidef A) i) _ (by positivity)
      apply sp.increasing
      change i.val ≤ i.val + j.val
      omega
    _ = ∑ j ∈ Finset.univ.image f, sp.value (j.castLE (Nat.sub_le b k)) ^ (p / 2) := by
      rw [Finset.sum_image]
      intro x _ y _ h
      exact hf h
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      exact Real.rpow_nonneg (sp.value_nonneg (rightGram_posSemidef A) _) _

theorem cutoff_le_quarter_of_power_budget {E B L c r t : ℝ}
    (hc : 0 ≤ c) (hL : 0 ≤ L) (hr : 0 < r) (hr1 : r ≤ 1) (hB : 0 < B)
    (ht : 4 * B ≤ t) (hbudget : t * c ^ r ≤ E) (hsmall : E < B * L ^ r) : c ≤ L / 4 := by
  by_contra! hcut
  have hLc : L < 4 * c := by linarith
  have hp := Real.rpow_lt_rpow hL hLc hr
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hc] at hp
  have hfour : (4 : ℝ) ^ r ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hr1
  have hpow : L ^ r < 4 * c ^ r := hp.trans_le (mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hc _))
  have hmul := mul_lt_mul_of_pos_left hpow hB
  have hcount := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hc r)
  nlinarith

theorem spectral_cutoff_le_quarter_of_small_tail {a b k t : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (sp : OrderedMatrixSpectrum (Aᵀ * A)) (hk : k ≤ b)
    (i : Fin b) (hi : i.val + t ≤ b - k) {p B L : ℝ}
    (hp : 0 < p) (hp2 : p ≤ 2) (hB : 0 < B) (hL : 0 ≤ L) (ht : 4 * B ≤ (t : ℝ))
    (hsmall : optimalSchattenPower p A k < B * L ^ (p / 2)) : sp.value i ≤ L / 4 :=
  cutoff_le_quarter_of_power_budget (sp.value_nonneg (rightGram_posSemidef A) i) hL
    (by positivity) (by linarith) hB ht (optimalSchattenPower_ge_tail_count A sp hk i hi hp) hsmall

end
end LowRank
