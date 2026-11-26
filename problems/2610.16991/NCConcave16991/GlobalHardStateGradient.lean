import NCConcave16991.GlobalHardStateCoefficient
import NCConcave16991.GlobalHardStateSmoothness

/-! # Actual state derivative, with the direct public vector exit separated -/

namespace NCConcave16991.GlobalHard

noncomputable section

open LocalizationScalar LocalizationRadial
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

theorem activationLoad_hasDerivAt (previous current : ℝ) :
    HasDerivAt (activationLoad previous) (-gate previous * deriv gate current) current := by
  have hq := (gate_contDiff.differentiable (by simp) current).hasDerivAt
  have hh := ((hasDerivAt_const current 1).sub hq).const_mul (gate previous)
  convert hh using 1 <;> first | rfl | ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def exitPair (s b : E) : ℝ := ⟪radialCap 21 b, radialCap 10 s⟫_ℝ

/-- All dependence on one state, with neighboring blocks held fixed. The
three outgoing scalar terms are exactly the next outer-stage couplings. -/
def localStateObjective (v b : E) (previous next entry nextEntry nextExit : ℝ) (s : E) : ℝ :=
  statePenalty v s + incomingScoreFunction previous (stateScore v s) entry 0 -
    activationLoad previous (stateScore v s) * exitPair s b +
    outgoingScoreFunction (stateScore v s) next nextEntry nextExit

theorem localStateObjective_eq_outer {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    (u : A) (v b s : E) (a : A) (previous next nextEntry nextExit : ℝ) :
    localStateObjective v b previous next ⟪u, radialCap 21 a⟫_ℝ nextEntry nextExit s =
      outerStage u v previous s a b + outgoingScoreFunction (stateScore v s) next nextEntry nextExit := by
  rw [localStateObjective, incomingScoreFunction_eq]
  dsimp [outerStage, entrance, exit, stateCoupling, activationLoad, exitPair]
  have hc : ⟪radialCap 21 b, radialCap 10 s⟫_ℝ = ⟪radialCap 10 s, radialCap 21 b⟫_ℝ := real_inner_comm _ _
  rw [hc]
  ring

def localStateDerivative (v b : E) (previous next entry nextEntry nextExit : ℝ) (s : E) : E →L[ℝ] ℝ :=
  gamma • innerSL ℝ s +
    stateScoreCoefficient previous (stateScore v s) next entry (exitPair s b) nextEntry nextExit • fderiv ℝ (stateScore v) s -
    activationLoad previous (stateScore v s) • ((innerSL ℝ (radialCap 21 b)).comp (fderiv ℝ (radialCap 10) s))

/-- Exact first derivative of the literal state function, with no
connector bound, dual-interiority assumption or gradient formula premise. -/
theorem localStateObjective_hasFDerivAt (v b : E) (previous next entry nextEntry nextExit : ℝ) (s : E) :
    HasFDerivAt (localStateObjective v b previous next entry nextEntry nextExit)
      (localStateDerivative v b previous next entry nextEntry nextExit s) s := by
  have ht := ((stateScore_contDiff v).differentiable (by simp) s).hasFDerivAt
  have hp := ((statePenalty_contDiff v).differentiable (by simp) s).hasFDerivAt
  have hi := (incomingScoreFunction_hasDerivAt previous (stateScore v s) entry 0).comp_hasFDerivAt s ht
  have hl := (activationLoad_hasDerivAt previous (stateScore v s)).comp_hasFDerivAt s ht
  have hx := (innerSL ℝ (radialCap 21 b)).hasFDerivAt.comp s
    ((radialCap_differentiable (by norm_num : (0 : ℝ) < 10) s).hasFDerivAt)
  have ho := (outgoingScoreFunction_hasDerivAt (stateScore v s) next nextEntry nextExit).comp_hasFDerivAt s ht
  have hh := ((hp.add hi).sub (hl.mul hx)).add ho
  refine hh.congr_fderiv ?_
  ext h
  simp only [localStateDerivative, statePenalty_fderiv,
    scalar_score_fderiv activationSq activationSqDerivative activationSq_hasDerivAt,
    scalar_score_fderiv statePotential statePotentialDerivative statePotential_hasDerivAt,
    ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  dsimp [stateScoreCoefficient, incomingScoreDerivative, incomingScoreCoefficient,
    outgoingScoreDerivative, activationSqDerivative, exitPair]
  ring

theorem localStateObjective_fderiv (v b : E) (previous next entry nextEntry nextExit : ℝ) (s : E) :
    fderiv ℝ (localStateObjective v b previous next entry nextEntry nextExit) s =
      localStateDerivative v b previous next entry nextEntry nextExit s :=
  (localStateObjective_hasFDerivAt v b previous next entry nextEntry nextExit s).fderiv

end

end NCConcave16991.GlobalHard
