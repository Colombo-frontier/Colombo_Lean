import Bilevel.PolishedPenaltyAllDerivatives
import Bilevel.ChiBoundedChainLocalBudgets

/-! The release-profile estimate with its unrestricted fixed-order quantifier,
including the exact b^{-j} scaling in the source's displayed q(s)=q0(s/b). -/
noncomputable section
namespace Bilevel.PolishedReleaseAllDerivatives
open ChiBoundedChain PolishedPenaltyAllDerivatives

theorem releaseGate_all_fixed_orders_bounded (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, |iteratedDeriv n releaseGate t| ≤ K := by
  apply compact_derivative_all_orders_bound releaseGate (fun _ => releaseGate_contDiff)
    1 (by norm_num) _ releaseGate_deriv_compactSupport n
  intro t
  simp only [releaseGate,abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem source_release_all_fixed_orders_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 < b → ∀ t,
      |iteratedDeriv n (fun s => releaseGate (s/b)) t| ≤ K/b^n := by
  obtain ⟨K,hK,hb⟩ := releaseGate_all_fixed_orders_bounded n
  refine ⟨K,hK,fun b hbp t => ?_⟩
  have he : (fun s : ℝ => releaseGate (s/b)) = fun s => releaseGate (b⁻¹*s) := by
    funext s
    congr 1
    ring
  rw [he,iteratedDeriv_comp_const_mul (releaseGate_contDiff (k:=n)) b⁻¹]
  simp only [abs_mul,abs_pow,abs_inv,abs_of_pos hbp]
  have h := mul_le_mul_of_nonneg_left (hb (b⁻¹*t)) (pow_nonneg (inv_nonneg.mpr hbp.le) n)
  simpa only [inv_pow,div_eq_mul_inv,mul_comm] using h

end Bilevel.PolishedReleaseAllDerivatives
