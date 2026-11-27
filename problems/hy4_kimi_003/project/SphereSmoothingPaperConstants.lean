import UpperPublicParameters
namespace Task006.UpperPublicParameters

theorem public_kappa_lt_radius_div_twentyFour {d : ℕ} {R A : ℝ}
    (hd : 1 ≤ d) (hR : 0 < R) (hA : 2 ≤ A) :
    publicRho R A+publicDelta d R A < R/24 := by
  have hδ := publicDelta_le_rho hd hR.le (show 1 ≤ A by linarith)
  have hρ : publicRho R A ≤ R/96 := by
    unfold publicRho
    exact div_le_div_of_nonneg_left hR.le (by norm_num) (by linarith)
  linarith

theorem publicRho_eq_epsilon {L R eps A : ℝ} (hL : 0 < L) (hR : 0 < R)
    (heps : 0 < eps) (hA : A=L*R/eps) : publicRho R A=eps/(48*L) := by
  unfold publicRho
  rw [hA]
  field_simp [hL.ne',hR.ne',heps.ne']

end Task006.UpperPublicParameters
