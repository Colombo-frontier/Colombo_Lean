import UpperProgramPublic
import SphereSmoothingSharpParameters
import UpperOptimizationMixture

open Task006.UpperPublicParameters Task006.HaarRebalancing
open Task006.Full.SampleInstance
namespace Task006.Full

noncomputable def ghostBiasBudget (P : UpperProgramParameters) (d : ℕ) (L s : ℝ) : ℝ :=
  Real.sqrt d*rebalancingThreshold L d s*P.b^(-1/2:ℝ) +
    Real.sqrt d*((d:ℝ)*L*P.δ/(2*P.ρ))

noncomputable def ghostSecondBudget (P : UpperProgramParameters) (d : ℕ) (L s : ℝ) : ℝ :=
  (d:ℝ)*rebalancingThreshold L d s*P.b^(1/2:ℝ)

noncomputable def ghostRiskBudget (P : UpperProgramParameters) (d : ℕ) (L s : ℝ) (T : ℕ) : ℝ :=
  P.R^2/(2*P.η*T)+2*P.R*ghostBiasBudget P d L s +
    P.η*ghostSecondBudget P d L s/2+2*P.ρ*L+L*(P.ρ+P.δ)

theorem tunedUpper_ghost_accuracy {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    ghostRiskBudget (tunedUpperParameters d L R eps h) d L (tunedUpperScale d L R eps)
      (tunedUpperRounds d L R eps) ≤ 17*eps/48 := by
  let A := upperAspect L R eps
  let s := tunedUpperScale d L R eps
  let T := publicRounds A s
  let B := publicBiasScale L A s
  have hL := h.2.1
  have hR := h.2.2.1
  have heps := h.2.2.2.1
  have hd : 0 < d := by have hd := h.1; omega
  have hA : 0 < A := by have hh := (regime_aspect h).1; dsimp only [A]; linarith
  have hs : 0 < s := by have hh := tunedUpperScale_ge_one h; dsimp only [s]; linarith
  have hT : 0 < (T:ℝ) := by exact_mod_cast publicRounds_pos hA hs
  have hB : 0 < B := publicBiasScale_pos hL hA hs
  have hid := public_scale_identities hd hL hA hs
  have hfd := public_finite_difference_scale_sharp (L := L) hd hR hA
  have hub : R*B ≤ eps/12 := public_optimization_allowance hL hR heps hA hs rfl
  have hρL : publicRho R A*L=eps/48 := by
    have he : A*eps=L*R := by dsimp [A,upperAspect]; field_simp [heps.ne']
    unfold publicRho
    field_simp [hA.ne']
    nlinarith
  have hFD : R*(L/(96*A))=eps/96 := by
    have he : R*(L/(96*A))=(publicRho R A*L)/2 := by unfold publicRho; ring
    rw [he,hρL]
    ring
  have hδ := publicDelta_le_rho (d := d) (R := R) (A := A)
    (by omega : 1 ≤ d) hR.le (by have hh := (regime_aspect h).1; dsimp only [A]; linarith)
  have hbase : 3*R*B+2*R*(L/(96*A))+2*publicRho R A*L+
      L*(publicRho R A+publicDelta d R A) ≤ 17*eps/48 := by
    have hδL := mul_le_mul_of_nonneg_left hδ hL.le
    nlinarith
  unfold ghostRiskBudget ghostBiasBudget ghostSecondBudget
  change R^2/(2*publicStep R L A s*(T:ℝ)) +
    2*R*(Real.sqrt d*publicMoment d L s*publicClip d L A s^(-1/2:ℝ)+
      Real.sqrt d*((d:ℝ)*L*publicDelta d R A/(2*publicRho R A))) +
    publicStep R L A s*((d:ℝ)*publicMoment d L s*publicClip d L A s^(1/2:ℝ))/2+
      2*publicRho R A*L+L*(publicRho R A+publicDelta d R A) ≤ 17*eps/48
  rw [hid.1,hid.2.2.1,hfd]
  have hn := mixture_regret_normalization (F := L/(96*A)) (q := 0) (L := L) hR hT hB
  simp only [mul_zero,zero_mul,add_zero] at hn
  have he : R^2/(2*publicStep R L A s*(T:ℝ))+2*R*(B+L/(96*A))+
      publicStep R L A s*((T:ℝ)*B^2)/2 = 3*R*B+2*R*(L/(96*A)) := by
    convert hn using 1 <;> dsimp only [publicStep,T,B] <;> ring
  rw [he]
  exact hbase

theorem tunedUpper_ghost_tail_correction {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    2*L*R*((tunedUpperRounds d L R eps:ℝ)*(d:ℝ)*Real.exp (-tunedUpperScale d L R eps)) ≤
      2*eps/(L*R/eps) := by
  let A := upperAspect L R eps
  have heps := h.2.2.2.1
  have hL := h.2.1
  have hR := h.2.2.1
  have hA : 0 < A := by have hh := (regime_aspect h).1; dsimp only [A]; linarith
  have hbudget := (public_log_budget h.1 (by linarith [(regime_aspect h).1] : 2 ≤ A)
    (regime_aspect h).2).2.2
  have hT : (tunedUpperRounds d L R eps:ℝ)*(d:ℝ)*Real.exp (-tunedUpperScale d L R eps) ≤ A⁻¹^2 := hbudget
  have he : L*R=eps*A := by dsimp only [A,upperAspect]; field_simp [heps.ne']
  calc
    _ ≤ (2*L*R)*A⁻¹^2 := mul_le_mul_of_nonneg_left hT (by positivity)
    _ = 2*eps/A := by
      rw [show 2*L*R=2*(L*R) by ring,he]
      field_simp [hA.ne']

#print axioms tunedUpper_ghost_accuracy
#print axioms tunedUpper_ghost_tail_correction
end Task006.Full
