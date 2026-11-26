import SecondOrder.EpochOptimization

namespace SecondOrder
noncomputable section

/-- Clipping the balanced minimizer and rounding upward is within a
factor two of every real competitor in the allowed interval. -/
theorem clippedCeil_near_minimum {A B x q : ℝ} {Q : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 < x) (hQ : 0 < Q)
    (he : A = B*x^2) (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    A/(clippedCeil Q x : ℝ)+B*(clippedCeil Q x : ℝ) ≤ 2*(A/q+B*q) := by
  have hq0 : 0 < q := by linarith
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hdiv : 0 ≤ A/q := div_nonneg hA hq0.le
  by_cases hlo : x ≤ 1
  · rw [clippedCeil_eq_one hQ hlo]
    have hAB : A ≤ B := by nlinarith [mul_nonneg hB (show 0 ≤ 1-x^2 by nlinarith)]
    have hBq := mul_le_mul_of_nonneg_left hq hB
    norm_num only [Nat.cast_one, div_one, mul_one]
    nlinarith
  · by_cases hhi : (Q : ℝ) ≤ x
    · rw [clippedCeil_eq_cap hhi]
      have hBQ : B*(Q : ℝ)^2 ≤ A := by
        rw [he]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQr.le hhi 2) hB
      have hb := clipped_balance_right hQr hBQ
      rw [mul_div_assoc] at hb
      have hc := div_le_div_of_nonneg_left hA hq0 hqQ
      have hn : 0 ≤ B*q := by positivity
      linarith
    · rw [clippedCeil_eq_ceil (lt_of_not_ge hlo) (le_of_lt (lt_of_not_ge hhi))]
      have hround : (⌈x⌉₊ : ℝ) ≤ 2*x := by
        have hc := Nat.ceil_lt_add_one hx.le
        linarith
      have hb := balance_rounding hA hB hx (Nat.le_ceil x) hround
      rw [balance_exact hx he] at hb
      have hmin : 2*B*x ≤ A/q+B*q := by
        apply (mul_le_mul_right hq0).mp
        have hs := mul_nonneg hB (sq_nonneg (x-q))
        rw [add_mul, div_mul_cancel₀ A hq0.ne']
        nlinarith [he]
      linarith

def epochCost (P : Parameters) (τ q : ℝ) : ℝ :=
  epochAnchorCoefficient P τ/q+epochTreeCoefficient P τ*q

/-- The minimum is over the full real interval; the algorithm still
uses the already defined, positive integer epoch length. -/
def epochMinimum (P : Parameters) (τ : ℝ) : ℝ :=
  sInf (epochCost P τ '' Set.Icc 1 (epochGradientCap P τ : ℝ))

theorem epochMinimum_nonneg (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ epochMinimum P τ := by
  apply le_csInf
  · refine ⟨epochCost P τ 1, 1, ?_, rfl⟩
    exact ⟨le_rfl, by exact_mod_cast epochGradientCap_pos P τ⟩
  · rintro y ⟨q, hq, rfl⟩
    have hq0 : 0 ≤ q := by linarith [hq.1]
    exact add_nonneg (div_nonneg (epochAnchorCoefficient_pos P hτ).le hq0)
      (mul_nonneg (epochTreeCoefficient_pos P hτ).le hq0)

theorem trackingEpochLength_near_minimum (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    epochCost P τ (trackingEpochLength P τ : ℝ) ≤ 2*epochMinimum P τ := by
  have hn : (epochCost P τ '' Set.Icc 1 (epochGradientCap P τ : ℝ)).Nonempty := by
    refine ⟨epochCost P τ 1, 1, ?_, rfl⟩
    exact ⟨le_rfl, by exact_mod_cast epochGradientCap_pos P τ⟩
  have hb : epochCost P τ (trackingEpochLength P τ : ℝ)/2 ≤ epochMinimum P τ := by
    apply le_csInf hn
    rintro y ⟨q, hq, rfl⟩
    have hh := clippedCeil_near_minimum
      (epochAnchorCoefficient_pos P hτ).le (epochTreeCoefficient_pos P hτ).le
      (preferredEpochLength_pos P hτ) (epochGradientCap_pos P τ)
      (preferredEpochLength_balance P hτ) hq.1 hq.2
    change epochCost P τ (trackingEpochLength P τ : ℝ) ≤ 2*epochCost P τ q at hh
    linarith
  linarith

theorem epochMinimum_le (P : Parameters) {τ q : ℝ} (hτ : 0 < τ)
    (hq : q ∈ Set.Icc 1 (epochGradientCap P τ : ℝ)) :
    epochMinimum P τ ≤ epochCost P τ q := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    have hr0 : 0 ≤ r := by linarith [hr.1]
    exact add_nonneg (div_nonneg (epochAnchorCoefficient_pos P hτ).le hr0)
      (mul_nonneg (epochTreeCoefficient_pos P hτ).le hr0)
  · exact ⟨q, hq, rfl⟩

theorem epochMinimum_attained (P : Parameters) {τ : ℝ} (hτ : 0 < τ) :
    ∃ q ∈ Set.Icc 1 (epochGradientCap P τ : ℝ), epochMinimum P τ = epochCost P τ q := by
  have hn : (Set.Icc 1 (epochGradientCap P τ : ℝ)).Nonempty :=
    ⟨1, le_rfl, by exact_mod_cast epochGradientCap_pos P τ⟩
  have hc : ContinuousOn (epochCost P τ) (Set.Icc 1 (epochGradientCap P τ : ℝ)) := by
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id (fun q hq => by linarith [hq.1])
    · exact continuousOn_const.mul continuousOn_id
  obtain ⟨q, hq, hm⟩ := isCompact_Icc.exists_isMinOn hn hc
  refine ⟨q, hq, le_antisymm (epochMinimum_le P hτ hq) ?_⟩
  apply le_csInf (hn.image _)
  rintro y ⟨r, hr, rfl⟩
  exact hm hr

theorem epochMinimum_epsilon_scale (P : Parameters) {ε : ℝ} (hε : 0 < ε) :
    epochMinimum P (ε/10) ≤ 10000*epochMinimum P ε := by
  have hτ : 0 < ε/10 := by positivity
  obtain ⟨q, hq, he⟩ := epochMinimum_attained P hε
  have hcap : epochGradientCap P ε ≤ epochGradientCap P (ε/10) := by
    unfold epochGradientCap
    apply Nat.add_le_add_left
    apply Nat.ceil_mono
    have hg : 0 ≤ P.gap*P.gradientLip/ε^2 :=
      div_nonneg (mul_nonneg P.gap_pos.le P.gradientLip_pos.le) (sq_nonneg _)
    calc
      _ ≤ 100*(P.gap*P.gradientLip/ε^2) := by linarith
      _ = _ := by ring
  have hq' : q ∈ Set.Icc 1 (epochGradientCap P (ε/10) : ℝ) :=
    ⟨hq.1, hq.2.trans (by exact_mod_cast hcap)⟩
  have hb := epochMinimum_le P hτ hq'
  have ha : epochAnchorCoefficient P (ε/10) = 10000*epochAnchorCoefficient P ε := by
    unfold epochAnchorCoefficient
    ring
  have ht : epochTreeCoefficient P (ε/10) = 100*epochTreeCoefficient P ε := by
    unfold epochTreeCoefficient
    ring
  have hBq : 0 ≤ epochTreeCoefficient P ε*q :=
    mul_nonneg (epochTreeCoefficient_pos P hε).le (by linarith [hq.1])
  rw [he]
  unfold epochCost at hb ⊢
  rw [ha, ht, mul_div_assoc] at hb
  nlinarith

end
end SecondOrder
