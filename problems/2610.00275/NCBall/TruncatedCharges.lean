import NCBall.TruncatedShadow

/-! # The linear information count is controlled by the concrete shadow clock -/

noncomputable section
namespace NCBall

variable {S : Type*} [MeasurableSpace S] {n H : ℕ}

theorem truncatedDirection_nonzero_stage (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (q₀ j : ℕ) (ρ lam scale : ℝ) (t : ℕ) (h : LinearHistory S t)
    (hd : truncatedShadowDirection d p q₀ j ρ lam scale t h ≠ 0) :
    shadowStage p ρ q₀ t h = j := by
  by_contra he
  exact hd (by simp [truncatedShadowDirection, he])

theorem truncatedDirection_nonzero_clock (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (hdclock : ∀ s k, d.directions s k 0 = 0)
    (q₀ j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (lam scale : ℝ) (t : ℕ) (h : LinearHistory S t)
    (hd : truncatedShadowDirection d p q₀ j ρ lam scale t h ≠ 0) :
    |p.point t h 0 - 4 * ρ * j| ≤ ρ := by
  have hstage := truncatedDirection_nonzero_stage d p q₀ j ρ lam scale t h hd
  by_contra hc
  have hclock : backgroundCenters d ρ t h j 0 = 4 * ρ * j :=
    roomCenter_clock ρ _ (hdclock (historySeed t h)) j
  have hz := roomMeasurement_zero_of_clock_miss (lam := lam) hρ
    (backgroundCenters d ρ t h j) (p.point t h) (by rw [hclock]; exact lt_of_not_ge hc)
  exact hd (by simp [truncatedShadowDirection, hstage, hz])

theorem truncated_queryCount_le_clock (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (hdclock : ∀ s k, d.directions s k 0 = 0)
    (q₀ j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (lam scale : ℝ) (t : ℕ) (h : LinearHistory S t) :
    reusableQueryCount (truncatedShadowPolicy d p q₀ j ρ lam scale) t h ≤
      shadowCounter p ρ q₀ t h - j * q₀ := by
  induction t with
  | zero => simp [reusableQueryCount, shadowCounter]
  | succ t ih =>
    have hp := ih h.1
    rw [reusableQueryCount]
    by_cases hd : (truncatedShadowPolicy d p q₀ j ρ lam scale).direction t h.1 = 0
    · rw [if_pos hd, Nat.add_zero]
      exact hp.trans (Nat.sub_le_sub_right (shadowCounter_step p ρ q₀ t h).1 _)
    · rw [if_neg hd]
      have hr := truncatedDirection_nonzero_stage d p q₀ j ρ lam scale t h.1 hd
      have hc := truncatedDirection_nonzero_clock d p hdclock q₀ j hρ lam scale t h.1 hd
      have hb : j * q₀ ≤ shadowCounter p ρ q₀ t h.1 := by
        rw [← hr, shadowStage]
        exact Nat.div_mul_le_self _ _
      have hnext : shadowCounter p ρ q₀ (t + 1) h = shadowCounter p ρ q₀ t h.1 + 1 := by
        change (if |p.point t h.1 0 - 4 * ρ * shadowStage p ρ q₀ t h.1| ≤ ρ then _ else _) = _
        rw [hr, if_pos hc]
      rw [hnext]
      omega

theorem truncated_queryCount_lt_threshold (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (hdclock : ∀ s k, d.directions s k 0 = 0)
    {q₀ : ℕ} (hq : 0 < q₀) (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (lam scale : ℝ) (t : ℕ) (h : LinearHistory S t) (hr : shadowStage p ρ q₀ t h = j) :
    reusableQueryCount (truncatedShadowPolicy d p q₀ j ρ lam scale) t h < q₀ := by
  have hp := truncated_queryCount_le_clock d p hdclock q₀ j hρ lam scale t h
  have he := Nat.mod_add_div (shadowCounter p ρ q₀ t h) q₀
  change shadowCounter p ρ q₀ t h / q₀ = j at hr
  rw [hr, Nat.mul_comm q₀ j] at he
  have hm := Nat.mod_lt (shadowCounter p ρ q₀ t h) hq
  omega

end NCBall
