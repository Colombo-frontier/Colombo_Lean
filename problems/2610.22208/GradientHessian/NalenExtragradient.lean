import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! The exact one-step extragradient estimate used by NALEN. The two
variational inequalities are supplied by actual compact-ball subproblem
minimizers in the subsequent construction. -/

noncomputable section
namespace GradientHessian.Nalen
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_young_scaled (x y : E) {η : ℝ} (hη : 0 < η) :
    4*η*⟪x,y⟫_ℝ ≤ 4*η^2*‖x‖^2+‖y‖^2 := by
  have hi := real_inner_le_norm x y
  have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4*η by positivity)
  nlinarith only [hh,sq_nonneg (2*η*‖x‖-‖y‖)]

theorem extragradient_step {η : ℝ} (hη : 0 < η) (g h δ v w u : E)
    (hh : 0 ≤ ⟪η • h+δ-v,w-δ⟫_ℝ)
    (hg : 0 ≤ ⟪η • g+w-v,u-w⟫_ℝ) :
    ⟪g,δ-u⟫_ℝ ≤ ‖u-v‖^2/(2*η)-‖u-w‖^2/(2*η)+η*‖h-g‖^2-
      ‖δ-v‖^2/(2*η)-‖δ-w‖^2/(4*η) := by
  have hy := inner_young_scaled (g-h) (δ-w) hη
  rw [norm_sub_rev g h] at hy
  have he : ‖u-v‖^2/(2*η)-‖u-w‖^2/(2*η)+η*‖h-g‖^2-
      ‖δ-v‖^2/(2*η)-‖δ-w‖^2/(4*η) =
      (2*‖u-v‖^2-2*‖u-w‖^2+4*η^2*‖h-g‖^2-2*‖δ-v‖^2-‖δ-w‖^2)/(4*η) := by
    field_simp
    ring
  rw [he]
  apply (le_div_iff₀ (show 0 < 4*η by positivity)).2
  have hh' := mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hh
  have hg' := mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hg
  simp only [inner_sub_left,inner_add_left,real_inner_smul_left,
    inner_sub_right] at hh' hg' hy ⊢
  simp only [norm_sub_sq_real,real_inner_self_eq_norm_sq,real_inner_comm] at hh' hg' hy ⊢
  nlinarith only [hh',hg',hy]

end GradientHessian.Nalen
