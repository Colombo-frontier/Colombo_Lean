import UpperProgramPublic
import UpperProgramBudgets
import UpperOptimizationMixture

/-! Complete numerical closure for the same public algorithm and source
parameters. The conservative smoothing route has base allowance 18 eps / 48. -/

open Task006.UpperPublicParameters
namespace Task006.Full

set_option maxHeartbeats 1000000 in
theorem tunedUpper_accuracy {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    upperRiskBudget (tunedUpperParameters d L R eps h) d L (tunedUpperScale d L R eps)
      (tunedUpperRounds d L R eps) < eps := by
  let A := upperAspect L R eps
  let s := tunedUpperScale d L R eps
  let T := publicRounds A s
  let B := publicBiasScale L A s
  let q := (d : ℝ) * Real.exp (-s)
  have hL := h.2.1
  have hR := h.2.2.1
  have heps := h.2.2.2.1
  have hd : 0 < d := by have hd := h.1; omega
  have hA4 : 4 ≤ A := (regime_aspect h).1
  have hA : 0 < A := by linarith
  have hs1 : 1 ≤ s := tunedUpperScale_ge_one h
  have hs : 0 < s := by linarith
  have hTn : 0 < T := publicRounds_pos hA hs
  have hT : 0 < (T : ℝ) := by exact_mod_cast hTn
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hTn
  have hB : 0 < B := publicBiasScale_pos hL hA hs
  have hq : 0 ≤ q := mul_nonneg (Nat.cast_nonneg d) (Real.exp_pos _).le
  have hid := public_scale_identities hd hL hA hs
  have hfd := public_finite_difference_scale (L := L) hd hR hA
  have hub : R * B ≤ eps / 12 :=
    public_optimization_allowance hL hR heps hA hs rfl
  have hρL : publicRho R A * L = eps / 48 := by
    have hALR : A * eps = L * R := by dsimp [A, upperAspect]; field_simp [heps.ne']
    unfold publicRho
    field_simp [hA.ne']
    nlinarith [hALR]
  have hFD : R * (L / (48 * A)) = eps / 48 := by
    have hid : R * (L / (48 * A)) = publicRho R A * L := by unfold publicRho; ring
    rw [hid, hρL]
  have hδ := publicDelta_le_rho (d := d) (R := R) (A := A)
    (by omega : 1 ≤ d) hR.le (by linarith : 1 ≤ A)
  have hbase : 3 * R * B + 2 * R * (L / (48 * A)) +
      2 * publicRho R A * L + L * (publicRho R A + publicDelta d R A) ≤ 18 * eps / 48 := by
    have hδL := mul_le_mul_of_nonneg_left hδ hL.le
    nlinarith [hub, hρL, hFD]
  have hbudget := (public_log_budget h.1 (by linarith : 2 ≤ A) (regime_aspect h).2).2.2
  have hqt : q * (T : ℝ) ≤ (A ^ 2)⁻¹ := by
    have hid : (A⁻¹) ^ 2 = (A ^ 2)⁻¹ := by simp only [inv_pow]
    rw [hid] at hbudget
    convert hbudget using 1 <;> dsimp only [q, T, s, A, tunedUpperScale] <;> ring
  have hfinal := mixture_final_accuracy heps hA4 hT1 hq (mul_nonneg hR.le hB.le) hub hqt
  unfold upperRiskBudget upperActualBias upperActualSecondMoment
  change R ^ 2 / (2 * publicStep R L A s * (T : ℝ)) +
    2 * R * (Real.sqrt d * publicMoment d L s * publicClip d L A s ^ (-1/2:ℝ) +
      Real.sqrt d * ((d:ℝ)*L*publicDelta d R A/publicRho R A) +
        (Real.sqrt d * publicClip d L A s + L) * q) +
      publicStep R L A s * ((d:ℝ)*publicMoment d L s*publicClip d L A s ^ (1/2:ℝ) +
        ((d:ℝ)*publicClip d L A s^2)*q) / 2 +
      2 * publicRho R A * L + L*(publicRho R A+publicDelta d R A) < eps
  rw [hid.1, hid.2.1, hid.2.2.1, hid.2.2.2, hfd]
  have hnorm := mixture_regret_normalization (F := L/(48*A)) (q := q) (L := L) hR hT hB
  change R ^ 2 / (2 * publicStep R L A s * (T:ℝ)) +
    2*R*(B+L/(48*A)+((T:ℝ)*B+L)*q) +
    publicStep R L A s*((T:ℝ)*B^2+(T:ℝ)^2*B^2*q)/2 +
    2*publicRho R A*L+L*(publicRho R A+publicDelta d R A) < eps
  have heq : R ^ 2 / (2 * publicStep R L A s * (T:ℝ)) +
      2*R*(B+L/(48*A)+((T:ℝ)*B+L)*q) +
      publicStep R L A s*((T:ℝ)*B^2+(T:ℝ)^2*B^2*q)/2 =
        3*R*B+2*R*(L/(48*A))+(5/2:ℝ)*R*q*(T:ℝ)*B+2*R*L*q := by
    convert hnorm using 1 <;> dsimp only [publicStep, T, B] <;> ring
  rw [heq]
  have hALR : L * R = eps * A := by
    dsimp only [A, upperAspect]
    field_simp [heps.ne']
  have htail : 2 * R * L * q = 2 * eps * A * q := by
    calc
      _ = 2 * (L * R) * q := by ring
      _ = _ := by rw [hALR]; ring
  rw [htail]
  nlinarith [hbase, hfinal]

#print axioms tunedUpper_accuracy
end Task006.Full
