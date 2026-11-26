import Bilevel.PolishedLiteralProfiles

/-! The original linear-growth penalty has globally bounded derivatives at
every positive order. No bound on the penalty value itself is asserted. -/
noncomputable section
open Set

namespace Bilevel.PolishedPenaltyAllDerivatives
open ChiBoundedChain

theorem compact_derivative_all_orders_bound (f : ℝ → ℝ)
    (hf : ∀ k : ℕ, ContDiff ℝ k f) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t, |f t| ≤ B) (hs : HasCompactSupport (deriv f)) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |iteratedDeriv n f t| ≤ K := by
  cases n with
  | zero => exact ⟨B,hB,by simpa only [iteratedDeriv_zero] using hb⟩
  | succ n =>
    apply SmallGapProfileBounds.bound_of_compactSupport
    · rw [iteratedDeriv_succ']
      exact SmallGapProfileBounds.compactSupport_iteratedDeriv hs n
    · exact (contDiff_nat_iff_iteratedDeriv.mp (hf (n+1))).1 (n+1) le_rfl

def penaltySlope (t : ℝ) : ℝ := -theta (-t)

theorem penaltySlope_contDiff (k : ℕ) : ContDiff ℝ k penaltySlope :=
  (theta_contDiff.comp contDiff_id.neg).neg

theorem penaltySlope_deriv_compact : HasCompactSupport (deriv penaltySlope) := by
  apply SmallGapProfileBounds.compactSupport_of_tail 1
  intro t ht
  have hd := (penaltySlope_contDiff 1).differentiable (by norm_num) t
  rcases le_total 0 t with hp | hn
  · apply ZeroChainResidualCutoffs.deriv_zero_of_constant_on hd (uniqueDiffOn_Ici 0)
      (c:=0)
    · intro x hx
      change 0 ≤ x at hx
      simp only [penaltySlope,theta_zero (by linarith : -x ≤ 1/2),neg_zero]
    · exact hp
  · have ht' : t ≤ -1 := by rw [abs_of_nonpos hn] at ht; linarith
    apply ZeroChainResidualCutoffs.deriv_zero_of_constant_on hd (uniqueDiffOn_Iic (-1))
      (c:= -1)
    · intro x hx
      change x ≤ -1 at hx
      simp only [penaltySlope,theta_one (by linarith : 1 ≤ -x)]
    · exact ht'

theorem penaltySlope_all_fixed_orders_bounded (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |iteratedDeriv n penaltySlope t| ≤ K := by
  apply compact_derivative_all_orders_bound penaltySlope penaltySlope_contDiff 1
    (by norm_num) _ penaltySlope_deriv_compact n
  intro t
  simpa only [penaltySlope,abs_neg,abs_of_nonneg (theta_range (-t)).1] using
    (theta_range (-t)).2

theorem literal_penalty_positive_derivative_bounded (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t,
      |iteratedDeriv n PolishedLiteral.penalty t| ≤ K := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have he : deriv ChiOuter.penalty = penaltySlope :=
    funext ChiOuter.penalty_deriv
  simpa only [PolishedLiteral.penalty,iteratedDeriv_succ',he] using
    penaltySlope_all_fixed_orders_bounded m

end Bilevel.PolishedPenaltyAllDerivatives
