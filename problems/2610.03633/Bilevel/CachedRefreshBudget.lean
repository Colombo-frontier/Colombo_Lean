import Bilevel.CachedParameterChoice

/-! A finite public refresh radius also implements the zero-smoothness branch:
the cap radius contains every visited point, so exactly one anchor suffices. -/
noncomputable section
namespace Bilevel.CachedBudgetCalibration
open CachedAnchorCount

def refreshRadius (Λ La Δ ε : ℝ) : ℝ :=
  if La = 0 then radiusCap Λ Δ ε else ε/(64*La)

theorem radiusCap_pos {Λ Δ ε : ℝ} (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    0 < radiusCap Λ Δ ε := by
  have hN : (0:ℝ) < outerCount Λ Δ ε := Nat.cast_pos.mpr (outerCount_pos Λ Δ ε)
  have hcap : 0 < energyCap Λ Δ ε := by unfold energyCap; positivity
  exact div_pos (Real.sqrt_pos.mpr (mul_pos hN hcap)) hΛ

theorem refreshRadius_pos {Λ La Δ ε : ℝ}
    (hΛ : 0 < Λ) (hLa : 0 ≤ La) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    0 < refreshRadius Λ La Δ ε := by
  unfold refreshRadius
  split_ifs with h
  · exact radiusCap_pos hΛ hΔ hε
  · have : 0 < La := lt_of_le_of_ne hLa (Ne.symm h)
    positivity

theorem refreshRadius_budget {Λ La Δ ε : ℝ}
    (hLa : 0 ≤ La) (hε : 0 < ε) : La*refreshRadius Λ La Δ ε ≤ ε/64 := by
  unfold refreshRadius
  split_ifs with h
  · simp only [h,zero_mul]
    positivity
  · have hLa' : 0 < La := lt_of_le_of_ne hLa (Ne.symm h)
    have he : La*(ε/(64*La)) = ε/64 := by field_simp; ring
    exact he.le

variable {E : Type*} [NormedAddCommGroup E]

theorem track_constant_of_ball (radius : ℝ) (x : ℕ → E) (n : ℕ)
    (hx : ∀ i ≤ n, ‖x i-x 0‖ ≤ radius) :
    track radius x n = ⟨x 0,0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht := ih (fun i hi => hx i (hi.trans (Nat.le_succ n)))
    rw [track, ht]
    simp only [not_lt.mpr (hx (n+1) le_rfl), if_false]

variable [InnerProductSpace ℝ E]

theorem capped_prefix_radius {Λ Δ ε : ℝ}
    (hΛ : 0 < Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (x₀ : E) (G : ℕ → E) (n : ℕ) (hn : n ≤ outerCount Λ Δ ε) :
    ‖(CappedExecution.run Λ (energyCap Λ Δ ε) x₀ G n).point-x₀‖ ≤ radiusCap Λ Δ ε := by
  have hc : 0 ≤ energyCap Λ Δ ε := by unfold energyCap; positivity
  have hh := CappedExecution.all_history_radius hΛ hc x₀ G n
  have hm : (n:ℝ)*energyCap Λ Δ ε ≤ (outerCount Λ Δ ε:ℝ)*energyCap Λ Δ ε :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hc
  exact hh.trans (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hm) hΛ.le)

/-- All-history anchor budget, including the single-anchor La=0 branch. -/
theorem capped_anchor_budget {Λ La Δ ε : ℝ}
    (hΛ : 0 < Λ) (hLa : 0 ≤ La) (hLaΛ : La ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (x₀ : E) (G : ℕ → E) (n : ℕ) (hn : n ≤ outerCount Λ Δ ε) :
    let x := fun i => (CappedExecution.run Λ (energyCap Λ Δ ε) x₀ G i).point
    (1+(track (refreshRadius Λ La Δ ε) x n).refreshes : ℝ) ≤
      2560*(1+La*Δ/ε^2) := by
  dsimp only
  let x := fun i => (CappedExecution.run Λ (energyCap Λ Δ ε) x₀ G i).point
  change (1+(track (refreshRadius Λ La Δ ε) x n).refreshes : ℝ) ≤ _
  by_cases hz : La = 0
  · have ht : track (radiusCap Λ Δ ε) x n = ⟨x₀,0⟩ := by
      apply track_constant_of_ball
      intro i hi
      exact capped_prefix_radius hΛ hΔ hε x₀ G i (hi.trans hn)
    simp only [refreshRadius, hz, if_pos rfl, ht, Nat.cast_zero, add_zero, zero_mul,
      zero_div]
    norm_num [ht]
  · have hLap : 0 < La := lt_of_le_of_ne hLa (Ne.symm hz)
    have hc : 0 ≤ energyCap Λ Δ ε := by unfold energyCap; positivity
    have hh := all_history_anchor_count hΛ hc
      (by positivity : 0 < ε/(64*La)) x₀ G n
    have hm : (n:ℝ)*energyCap Λ Δ ε ≤ (outerCount Λ Δ ε:ℝ)*energyCap Λ Δ ε :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hc
    have hr := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hm) hΛ.le
    have hb := div_le_div_of_nonneg_right hr (by positivity : 0 ≤ ε/(64*La))
    have hM : (1+(track (ε/(64*La)) x n).refreshes:ℝ) ≤ 1+radiusCap Λ Δ ε/(ε/(64*La)) :=
      hh.trans (add_le_add_left hb 1)
    simp only [refreshRadius, if_neg hz]
    exact anchor_budget hΛ hLap hLaΛ hΔ hε hM

end Bilevel.CachedBudgetCalibration
