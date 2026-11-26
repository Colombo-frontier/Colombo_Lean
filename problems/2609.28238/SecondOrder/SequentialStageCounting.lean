import SecondOrder.ReferenceActivation

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

/-- A successful run under half the full stage budget must finish at least
half of the stages using fewer than the stage threshold many responses. -/
theorem sequential_fast_stages_count {T N n₀ : ℕ} (hn₀ : 0<n₀)
    (L : Fin T → ℕ) (hcharge : ∑ i, L i≤N) (hbudget : 2*N≤T*n₀) :
    (T:ℝ)≤2*∑ i : Fin T, if L i<n₀ then (1:ℝ) else 0 := by
  have hn : (0:ℝ)<n₀ := by exact_mod_cast hn₀
  have hp (i : Fin T) : (n₀:ℝ)≤(n₀:ℝ)*(if L i<n₀ then (1:ℝ) else 0)+(L i:ℝ) := by
    split_ifs with hi
    · simp only [mul_one]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · simp only [mul_zero, zero_add]
      exact_mod_cast (le_of_not_gt hi)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_add_distrib, ←Finset.mul_sum, ←Nat.cast_sum] at hs
  have hc : ((∑ i, L i:ℕ):ℝ)≤N := by exact_mod_cast hcharge
  have hb : 2*(N:ℝ)≤(T:ℝ)*(n₀:ℝ) := by exact_mod_cast hbudget
  nlinarith only [hs, hc, hb, hn]

/-- The counting/Markov step of the sequential lemma, for any actual finite
experiment. No independence between stage completion events is needed. -/
theorem sequential_completion_probability {Ω : Type*} [Fintype Ω] (p : PMF Ω)
    {T N n₀ : ℕ} (hT : 0<T) (hn₀ : 0<n₀)
    (L : Fin T → Ω → ℕ) (reached : Fin T → Ω → Bool) (complete : Ω → Bool)
    (hcomplete : ∀ ω, complete ω=true → ∀ i, reached i ω=true)
    (hcharge : ∀ ω, ∑ i, L i ω≤N) (hbudget : 2*N≤T*n₀)
    (hfast : ∀ i, pmfEventProbability p (fun ω => decide (reached i ω=true ∧ L i ω<n₀))≤1/32) :
    pmfEventProbability p complete≤1/16 := by
  have hpoint (ω : Ω) : (T:ℝ)*(if complete ω=true then (1:ℝ) else 0)≤
      2*∑ i : Fin T, if reached i ω=true ∧ L i ω<n₀ then (1:ℝ) else 0 := by
    by_cases hc : complete ω=true
    · simp only [if_pos hc, mul_one, hcomplete ω hc, true_and]
      exact sequential_fast_stages_count hn₀ (fun i => L i ω) (hcharge ω) hbudget
    · simp only [if_neg hc, mul_zero]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num))
  have hmean := pmfMean_mono p hpoint
  rw [pmfMean_mul, pmfMean_mul, pmfMean_finset_sum, ←pmfEventProbability_mean] at hmean
  have hfast' (i : Fin T) : pmfMean p (fun ω => if reached i ω=true ∧ L i ω<n₀ then (1:ℝ) else 0)≤1/32 := by
    simpa only [pmfEventProbability_mean, decide_eq_true_eq] using hfast i
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfast' i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have ht : (0:ℝ)<T := by exact_mod_cast hT
  nlinarith only [hmean, hs, ht]

theorem exists_below_pmfMean_bound {H : Type*} [Fintype H] (p : PMF H)
    (success : H → ℝ) {c : ℝ} (hmean : pmfMean p success<c) : ∃ θ, success θ<c := by
  by_contra hn
  have hh : ∀ θ, c≤success θ := by simpa only [not_exists, not_lt] using hn
  have hb := pmfMean_mono p hh
  rw [pmfMean_const] at hb
  exact not_lt_of_ge hb hmean

end
end SecondOrder
