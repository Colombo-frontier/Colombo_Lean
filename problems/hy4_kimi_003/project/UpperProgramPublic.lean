import UpperPublicParameters
import UpperProgramIntegrability

/-! One public, instance-independent parameter record for the implemented
finite-budget algorithm. All source-model quantifiers remain outside it. -/

open MeasureTheory
open Task006.UpperPublicParameters
namespace Task006.Full

noncomputable def upperAspect (L R eps : ℝ) : ℝ := L * R / eps

theorem regime_aspect {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    4 ≤ upperAspect L R eps ∧ (d : ℝ) ≤ upperAspect L R eps := by
  rcases h with ⟨hd, hL, hR, heps, hmax⟩
  constructor
  · have hh := (le_max_right (d : ℝ) (2 ^ 17 : ℝ)).trans hmax
    change 4 ≤ L * R / eps
    norm_num at hh ⊢
    linarith
  · exact (le_max_left _ _).trans hmax

noncomputable def tunedUpperScale (d : ℕ) (L R eps : ℝ) : ℝ :=
  publicLogScale d (upperAspect L R eps)

noncomputable def tunedUpperRounds (d : ℕ) (L R eps : ℝ) : ℕ :=
  publicRounds (upperAspect L R eps) (tunedUpperScale d L R eps)

theorem tunedUpperScale_ge_one {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    1 ≤ tunedUpperScale d L R eps := by
  have ha := regime_aspect h
  exact (public_log_budget h.1 (by linarith : 2 ≤ upperAspect L R eps) ha.2).1

theorem tunedUpperRounds_pos {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    0 < tunedUpperRounds d L R eps := by
  have ha := regime_aspect h
  exact publicRounds_pos (by linarith : 0 < upperAspect L R eps)
    (by linarith [tunedUpperScale_ge_one h] : 0 < tunedUpperScale d L R eps)

noncomputable def tunedUpperParameters (d : ℕ) (L R eps : ℝ) (h : Regime d L R eps) :
    UpperProgramParameters where
  R := R
  ρ := publicRho R (upperAspect L R eps)
  δ := publicDelta d R (upperAspect L R eps)
  η := publicStep R L (upperAspect L R eps) (tunedUpperScale d L R eps)
  b := publicClip d L (upperAspect L R eps) (tunedUpperScale d L R eps)
  rho_nonneg := (publicRho_pos h.2.2.1 (by linarith [(regime_aspect h).1])).le
  delta_pos := publicDelta_pos (by have hd := h.1; omega : 0 < d) h.2.2.1 (by linarith [(regime_aspect h).1])
  eta_pos := publicStep_pos h.2.2.1 h.2.1 (by linarith [(regime_aspect h).1])
    (by linarith [tunedUpperScale_ge_one h])
  clip_nonneg := (publicClip_pos (by have hd := h.1; omega : 0 < d) h.2.1
    (by linarith [(regime_aspect h).1]) (by linarith [tunedUpperScale_ge_one h])).le
  inner_nonneg := public_inner_nonneg (by have hd := h.1; omega : 1 ≤ d) h.2.2.1.le
    (by linarith [(regime_aspect h).1])

@[simp] theorem tunedUpperParameters_R {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    (tunedUpperParameters d L R eps h).R = R := rfl

theorem tunedUpperParameters_rho_pos {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    0 < (tunedUpperParameters d L R eps h).ρ :=
  publicRho_pos h.2.2.1 (by linarith [(regime_aspect h).1])

theorem tunedUpperParameters_clip_pos {d : ℕ} {L R eps : ℝ} (h : Regime d L R eps) :
    0 < (tunedUpperParameters d L R eps h).b :=
  publicClip_pos (by have hd := h.1; omega : 0 < d) h.2.1 (by linarith [(regime_aspect h).1])
    (by linarith [tunedUpperScale_ge_one h])

#print axioms tunedUpperParameters
end Task006.Full
