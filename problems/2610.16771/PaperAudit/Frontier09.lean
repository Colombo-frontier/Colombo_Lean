import Mathlib
import PaperAudit.Frontier08

open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000


section
-- Source component: EnvelopeOracleProgram.lean

namespace OriginalEnvelopeOracleProgram
open OriginalSaddleImplicit OriginalSaddleTangent OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

structure Estimate (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  saddle : Joint E F
  grad : E
  hess : E →L[ℝ] E

noncomputable def hessianFromAnswer (L : ℝ) (H : Joint E F →L[ℝ] Joint E F) : E →L[ℝ] E :=
  (2 * L) • ContinuousLinearMap.id ℝ E - (4 * L ^ 2) •
    (OriginalSchurInverse.schur (H + (2 * L) • primalProjection)).inverse

noncomputable def fromAnswer (L : ℝ) (x : E) (w : Joint E F)
    (a : OriginalDualOracleProgram.OracleAnswer (Joint E F)) : Estimate E F :=
  ⟨w, OriginalEnvelopeOracle.plugInGradient L x w, hessianFromAnswer L a.hess⟩

noncomputable def program (L : ℝ) (x : E)
    (warm : GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F)) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Estimate E F) :=
  FangqingGetterComposition.bind warm (fun w => .ask w (fun a => .pure (fromAnswer L x w a)))

theorem actual_execution (J : Joint E F → ℝ) (L : ℝ) (x : E)
    (warm : GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F)) :
    let first := execute (OriginalDualOracleProgram.actualOracle J) warm
    execute (OriginalDualOracleProgram.actualOracle J) (program L x warm) =
      (⟨first.1, OriginalEnvelopeOracle.plugInGradient L x first.1,
        OriginalEnvelopeOracle.plugInHessian J L first.1⟩, first.2 + 1) := by
  simp only [program, execute_bind, execute, fromAnswer, hessianFromAnswer,
    OriginalEnvelopeOracle.plugInHessian, saddleHessian, OriginalDualOracleProgram.actualOracle]

theorem actual_errors_from_checked_saddle_program
    (J : Joint E F → ℝ) (L mu rho tau : ℝ) (hL : 0 < L) (hmu : 0 < mu) (hrho : 0 ≤ rho)
    (hC2 : ContDiff ℝ 2 J)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (x : E)
    (warm : GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F))
    (hclose : ‖(execute (OriginalDualOracleProgram.actualOracle J) warm).1 -
      zStar (JointSliceRegularity.curry J) L x‖ ≤ tau) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program L x warm)
    ‖run.1.grad - gradient (OriginalSaddleTransfer.saddleEnvelope (JointSliceRegularity.curry J) L) x‖ ≤ 2 * L * tau ∧
      ‖run.1.hess - fderiv ℝ (gradient (OriginalSaddleTransfer.saddleEnvelope (JointSliceRegularity.curry J) L)) x‖ ≤
        (4 * rho * (1 + L / mu) ^ 2) * tau ∧
      run.2 = (execute (OriginalDualOracleProgram.actualOracle J) warm).2 + 1 := by
  have h := OriginalEnvelopeOracle.envelope_oracle_from_joint_negative_slice J L mu rho hL hmu hrho
    hC2 hsc hLip hHess x _ tau hclose
  rw [actual_execution]
  exact ⟨h.1, h.2, rfl⟩

noncomputable def targetTolerance (L C deltaG deltaH : ℝ) : ℝ :=
  1 / (1 + 2 * L / deltaG + (1 + C) / deltaH)

theorem targetTolerance_properties
    (L C δg δH : ℝ) (hL : 0 < L) (hC : 0 ≤ C) (hg : 0 < δg) (hH : 0 < δH) :
    0 < targetTolerance L C δg δH ∧ 2 * L * targetTolerance L C δg δH ≤ δg ∧
      C * targetTolerance L C δg δH ≤ δH ∧
      Real.log (1 + 1 / targetTolerance L C δg δH) = Real.log (2 + 2 * L / δg + (1 + C) / δH) := by
  let D := 1 + 2 * L / δg + (1 + C) / δH
  have hD : 0 < D := by dsimp only [D]; positivity
  change 0 < 1 / D ∧ 2 * L * (1 / D) ≤ δg ∧ C * (1 / D) ≤ δH ∧
    Real.log (1 + 1 / (1 / D)) = _
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [mul_one_div]
    apply (div_le_iff₀ hD).mpr
    have heq : δg * D = 2 * L + δg * (1 + (1 + C) / δH) := by
      dsimp only [D]
      field_simp
      <;> ring
    rw [heq]
    have hp : 0 ≤ δg * (1 + (1 + C) / δH) := by positivity
    linarith only [hp]
  · rw [mul_one_div]
    apply (div_le_iff₀ hD).mpr
    have heq : δH * D = C + (δH * (1 + 2 * L / δg) + 1) := by
      dsimp only [D]
      field_simp
      <;> ring
    rw [heq]
    have hp : 0 ≤ δH * (1 + 2 * L / δg) + 1 := by positivity
    linarith only [hp]
  · congr 1
    rw [one_div_one_div]
    dsimp only [D]
    ring


noncomputable def secondOrderProgram (mu L rho D deltaG deltaH : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Estimate E F) :=
  program L x (OriginalSecondOrderWarmAll.program mu L rho D
    (targetTolerance L (4 * rho * (1 + L / mu) ^ 2) deltaG deltaH) x uInit yin)

theorem actual_second_order_envelope_oracle
    (J : Joint E F → ℝ) (mu L rho D deltaG deltaH : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (hG : 0 < deltaG) (hH : 0 < deltaH)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - OriginalSaddleTransfer.vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let tau := targetTolerance L (4 * rho * (1 + L / mu) ^ 2) deltaG deltaH
    let run := execute (OriginalDualOracleProgram.actualOracle J) (secondOrderProgram mu L rho D deltaG deltaH x uInit yin)
    ‖run.1.grad - gradient (OriginalSaddleTransfer.saddleEnvelope (JointSliceRegularity.curry J) L) x‖ ≤ deltaG ∧
      ‖run.1.hess - fderiv ℝ (gradient (OriginalSaddleTransfer.saddleEnvelope (JointSliceRegularity.curry J) L)) x‖ ≤ deltaH ∧
      run.2 ≤ OriginalSecondOrderWarmAll.queryBudget J mu L rho D tau x uInit yin + 1 ∧
      Real.log (1 + 1 / tau) =
        Real.log (2 + 2 * L / deltaG + (1 + 4 * rho * (1 + L / mu) ^ 2) / deltaH) := by
  let tau := targetTolerance L (4 * rho * (1 + L / mu) ^ 2) deltaG deltaH
  have hp := targetTolerance_properties L (4 * rho * (1 + L / mu) ^ 2) deltaG deltaH hL (by positivity) hG hH
  have hw := OriginalSecondOrderWarmAll.actual_second_order_joint_warm_solve J mu L rho D tau
    hmu hL hrho hp.1 hC2 hLip hHess hsc x uInit yin hwarm
  have he := actual_errors_from_checked_saddle_program J L mu rho tau hL hmu hrho hC2 hsc hLip hHess x
    (OriginalSecondOrderWarmAll.program mu L rho D tau x uInit yin) hw.1
  exact ⟨he.1.trans hp.2.1, he.2.1.trans hp.2.2.1, by
    change (execute (OriginalDualOracleProgram.actualOracle J)
      (program L x (OriginalSecondOrderWarmAll.program mu L rho D tau x uInit yin))).2 ≤ _
    rw [he.2.2]
    exact Nat.add_le_add_right hw.2 1,
    hp.2.2.2⟩

end OriginalEnvelopeOracleProgram
end

section
-- Source component: EnvelopeOracleMinProgram.lean

namespace OriginalEnvelopeOracleMinProgram
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalEnvelopeOracleProgram

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def program (mu L rho D deltaG deltaH : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Estimate E F) :=
  OriginalEnvelopeOracleProgram.program L x (OriginalMinimumWarmSolver.program mu L rho D
    (targetTolerance L (4 * rho * (1 + L / mu) ^ 2) deltaG deltaH) x uInit yin)

theorem envelope_oracle_with_actual_minimum_warm_solver
    (J : Joint E F → ℝ) (mu L rho D : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hconcave : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu (fun y => J (WithLp.toLp 2 (u, y))))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    (∀ w : Joint E F, ∀ tau : ℝ, ‖w - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau →
      ‖OriginalEnvelopeOracle.plugInGradient L x w - gradient (saddleEnvelope (JointSliceRegularity.curry J) L) x‖ ≤ 2 * L * tau ∧
      ‖OriginalEnvelopeOracle.plugInHessian J L w - fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x‖ ≤
        (4 * rho * (1 + L / mu) ^ 2) * tau) ∧
    (∀ deltaG deltaH : ℝ, 0 < deltaG → 0 < deltaH →
      let tau := targetTolerance L (4 * rho * (1 + L / mu) ^ 2) deltaG deltaH
      let run := execute (OriginalDualOracleProgram.actualOracle J) (program mu L rho D deltaG deltaH x uInit yin)
      0 < tau ∧
      ‖run.1.grad - gradient (saddleEnvelope (JointSliceRegularity.curry J) L) x‖ ≤ deltaG ∧
      ‖run.1.hess - fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x‖ ≤ deltaH ∧
      (run.2 : ℝ) ≤ (1 + min (Real.sqrt (L / mu)) ((rho * D / mu) ^ (2 / 7 : ℝ))) *
        (OriginalMinimumWarmSolver.logFactor J mu L rho D tau x uInit yin + 1) ∧
      Real.log (1 + 1 / tau) =
        Real.log (2 + 2 * L / deltaG + (1 + 4 * rho * (1 + L / mu) ^ 2) / deltaH)) := by
  have hL : 0 < L := hmu.trans_le hLmu
  refine ⟨fun w tau hclose => OriginalEnvelopeOracle.envelope_oracle_from_standing_joint J L mu rho hL hmu hrho
    hC2 hconcave hLip hHess x w tau hclose, ?_⟩
  intro deltaG deltaH hG hH
  let tau := targetTolerance L (4 * rho * (1 + L / mu) ^ 2) deltaG deltaH
  have hp := targetTolerance_properties L (4 * rho * (1 + L / mu) ^ 2) deltaG deltaH hL (by positivity) hG hH
  have hw := OriginalMinimumWarmSolver.warm_solve_from_standing_joint J mu L rho D tau hmu hLmu hrho hp.1
    hC2 hLip hHess hconcave x uInit yin hwarm
  let p := OriginalMinimumWarmSolver.program mu L rho D tau x uInit yin
  have he := OriginalEnvelopeOracle.envelope_oracle_from_standing_joint J L mu rho hL hmu hrho hC2 hconcave hLip hHess
    x (execute (OriginalDualOracleProgram.actualOracle J) p).1 tau hw.1
  have hD : 0 ≤ D := (norm_nonneg _).trans hwarm
  have hP : 1 ≤ 1 + min (Real.sqrt (L / mu)) ((rho * D / mu) ^ (2 / 7 : ℝ)) :=
    le_add_of_nonneg_right (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _))
  have hexec := actual_execution J L x p
  refine ⟨hp.1, ?_, ?_, ?_, hp.2.2.2⟩
  · change ‖(execute (OriginalDualOracleProgram.actualOracle J) (OriginalEnvelopeOracleProgram.program L x p)).1.grad - _‖ ≤ _
    rw [hexec]
    exact he.1.trans hp.2.1
  · change ‖(execute (OriginalDualOracleProgram.actualOracle J) (OriginalEnvelopeOracleProgram.program L x p)).1.hess - _‖ ≤ _
    rw [hexec]
    exact he.2.trans hp.2.2.1
  · change ((execute (OriginalDualOracleProgram.actualOracle J) (OriginalEnvelopeOracleProgram.program L x p)).2 : ℝ) ≤ _
    rw [hexec]
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith only [hw.2, hP]

end OriginalEnvelopeOracleMinProgram
end

section
-- Source component: InexactOuterGradientDescent.lean

namespace OriginalOuterGD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable section

inductive Program (E R : Type*) where
  | pure : R → Program E R
  | ask : E → (E → Program E R) → Program E R

def execute {R : Type*} (oracle : E → E) : Program E R → R × ℕ
  | .pure r => (r, 0)
  | .ask x cont => let next := execute oracle (cont (oracle x)); (next.1, next.2 + 1)

def map {R S : Type*} (f : R → S) : Program E R → Program E S
  | .pure r => .pure (f r)
  | .ask x cont => .ask x (fun v => map f (cont v))

theorem execute_map {R S : Type*} (oracle : E → E) (f : R → S) (p : Program E R) :
    execute oracle (map f p) = (f (execute oracle p).1, (execute oracle p).2) := by
  induction p with
  | pure r => rfl
  | ask x cont ih => simp only [map, execute, ih]

structure Output (E : Type*) where
  point : E
  success : Bool
  steps : ℕ
  squaredSteps : ℝ

def appendStep (s : E) (out : Output E) : Output E :=
  ⟨out.point, out.success, out.steps + 1, ‖s‖ ^ 2 + out.squaredSteps⟩

def step (L : ℝ) (v : E) : E := -(L⁻¹) • v

def program (L eps : ℝ) : ℕ → E → Program E (Output E)
  | 0, x => .pure ⟨x, false, 0, 0⟩
  | n + 1, x => .ask x (fun v =>
      if ‖v‖ ≤ eps / 2 then .pure ⟨x, true, 0, 0⟩
      else map (appendStep (step L v)) (program L eps n (x + step L v)))

theorem one_step_descent
    (f : E → ℝ) (L eps : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (hdiff : Differentiable ℝ f)
    (hLip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x v : E) (herror : ‖v - gradient f x‖ ≤ eps / 16)
    (haway : ¬ ‖v‖ ≤ eps / 2) :
    L / 4 * ‖step L v‖ ^ 2 ≤ f x - f (x + step L v) ∧
      eps ^ 2 / (16 * L) ≤ f x - f (x + step L v) := by
  have hs := OriginalAudit.smooth_descent_upper f L hL hdiff hLip x (step L v)
  have hnorm : ‖step L v‖ = L⁻¹ * ‖v‖ := by
    rw [step, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hL)]
  have hscale : L * ‖step L v‖ = ‖v‖ := by rw [hnorm]; field_simp
  have hinner : inner ℝ (gradient f x) (step L v) =
      -L * ‖step L v‖ ^ 2 + inner ℝ (gradient f x - v) (step L v) := by
    have hv : v = -L • step L v := by rw [step, smul_smul]; field_simp; simp
    have hiv : inner ℝ v (step L v) = -L * ‖step L v‖ ^ 2 := by
      calc
        _ = inner ℝ (-L • step L v) (step L v) := congrArg (fun w : E => inner ℝ w (step L v)) hv
        _ = _ := by rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    calc
      _ = inner ℝ v (step L v) + inner ℝ (gradient f x - v) (step L v) := by
        rw [inner_sub_left]
        ring
      _ = _ := by rw [hiv]
  have herr := real_inner_le_norm (gradient f x - v) (step L v)
  have he : ‖gradient f x - v‖ ≤ eps / 16 := by simpa only [norm_sub_rev] using herror
  have hm := mul_le_mul_of_nonneg_right he (norm_nonneg (step L v))
  have hrel : eps / 16 * ‖step L v‖ ≤ L / 8 * ‖step L v‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge haway)) (norm_nonneg (step L v))
    have hscale2 := congrArg (fun r : ℝ => r * ‖step L v‖) hscale
    nlinarith only [hh, hscale2]
  have hdec : L / 4 * ‖step L v‖ ^ 2 ≤ f x - f (x + step L v) := by
    rw [hinner] at hs
    nlinarith only [hs, herr, hm, hrel, mul_nonneg hL.le (sq_nonneg ‖step L v‖)]
  have hminstep : eps / (2 * L) < ‖step L v‖ := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * L)).mpr
    nlinarith only [lt_of_not_ge haway, hscale]
  have hsq : (eps / (2 * L)) ^ 2 ≤ ‖step L v‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hminstep.le
  refine ⟨hdec, ?_⟩
  have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ L / 4)
  have hid : L / 4 * (eps / (2 * L)) ^ 2 = eps ^ 2 / (16 * L) := by field_simp <;> ring
  rw [hid] at hh
  exact hh.trans hdec

def Spec (f : E → ℝ) (L eps : ℝ) (n : ℕ) (x : E) (run : Output E × ℕ) : Prop :=
  L / 4 * run.1.squaredSteps ≤ f x - f run.1.point ∧
  (run.1.steps : ℝ) * (eps ^ 2 / (16 * L)) ≤ f x - f run.1.point ∧
  (run.1.success = true → ‖gradient f run.1.point‖ ≤ eps) ∧
  (run.1.success = false → run.1.steps = n) ∧
  run.2 ≤ run.1.steps + 1

theorem program_spec
    (f : E → ℝ) (L eps : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (hdiff : Differentiable ℝ f)
    (hLip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (oracle : E → E) (hvalid : ∀ x, ‖oracle x - gradient f x‖ ≤ eps / 16)
    (n : ℕ) (x : E) : Spec f L eps n x (execute oracle (program L eps n x)) := by
  induction n generalizing x with
  | zero => simp [Spec, program, execute]
  | succ n ih =>
      let v := oracle x
      by_cases hstop : ‖v‖ ≤ eps / 2
      · have htrue : ‖gradient f x‖ ≤ eps := by
          have hn := norm_sub_le v (v - gradient f x)
          have he : v - (v - gradient f x) = gradient f x := by abel
          rw [he] at hn
          have hvError : ‖v - gradient f x‖ ≤ eps / 16 := hvalid x
          nlinarith only [hn, hvError, hstop, heps]
        have hstop' : ‖oracle x‖ ≤ eps / 2 := hstop
        simpa [Spec, program, execute, hstop'] using htrue
      · have hdec := one_step_descent f L eps hL heps hdiff hLip x v (hvalid x) hstop
        have hi := ih (x + step L v)
        dsimp only [v] at hi hdec
        have hstop' : ¬ ‖oracle x‖ ≤ eps / 2 := hstop
        simp only [Spec] at hi
        simp only [program, execute, if_neg hstop', execute_map, Spec, appendStep,
          Nat.cast_add, Nat.cast_one]
        refine ⟨by nlinarith only [hi.1, hdec.1], by nlinarith only [hi.2.1, hdec.2],
          hi.2.2.1, ?_, ?_⟩
        · intro hh
          have hk := hi.2.2.2.1 hh
          omega
        · have hc := hi.2.2.2.2
          omega

def fuel (Delta L eps : ℝ) : ℕ := Nat.ceil (16 * Delta * L / eps ^ 2) + 1

theorem finite_termination_and_step_budget
    (f : E → ℝ) (L eps Delta lower : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (hdiff : Differentiable ℝ f)
    (hLip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (oracle : E → E) (hvalid : ∀ x, ‖oracle x - gradient f x‖ ≤ eps / 16)
    (hbelow : ∀ x, lower ≤ f x) (start : E) (hgap : f start - lower ≤ Delta) :
    let run := execute oracle (program L eps (fuel Delta L eps) start)
    run.1.success = true ∧ ‖gradient f run.1.point‖ ≤ eps ∧
      run.1.squaredSteps ≤ 4 * Delta / L ∧
      (run.1.steps : ℝ) ≤ 16 * Delta * L / eps ^ 2 ∧
      (run.2 : ℝ) ≤ 1 + 16 * Delta * L / eps ^ 2 := by
  dsimp only
  let run := execute oracle (program L eps (fuel Delta L eps) start)
  have hs := program_spec f L eps hL heps hdiff hLip oracle hvalid (fuel Delta L eps) start
  change Spec f L eps (fuel Delta L eps) start run at hs
  dsimp only [Spec] at hs
  have hvalue : f start - f run.1.point ≤ Delta := by linarith only [hbelow run.1.point, hgap]
  have hcount : (run.1.steps : ℝ) ≤ 16 * Delta * L / eps ^ 2 := by
    have hc : 0 < eps ^ 2 / (16 * L) := by positivity
    have hh := (le_div_iff₀ hc).mpr (le_trans hs.2.1 hvalue)
    convert! hh using 1 <;> field_simp <;> ring
  have hsuccess : run.1.success = true := by
    cases hb : run.1.success with
    | true => rfl
    | false =>
        have hsteps := hs.2.2.2.1 hb
        have hceil : 16 * Delta * L / eps ^ 2 ≤
            ((Nat.ceil (16 * Delta * L / eps ^ 2) : ℕ) : ℝ) := Nat.le_ceil _
        rw [hsteps] at hcount
        unfold fuel at hcount
        push_cast at hcount
        linarith only [hcount, hceil]
  refine ⟨hsuccess, hs.2.2.1 hsuccess, ?_, hcount, ?_⟩
  · apply (le_div_iff₀ hL).mpr
    linarith only [hs.1, hvalue]
  · have hh : (run.2 : ℝ) ≤ (run.1.steps : ℝ) + 1 := by exact_mod_cast hs.2.2.2.2
    linarith only [hh, hcount]

theorem bounded_below_original_interface
    (f : E → ℝ) (L eps Delta : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (hdiff : Differentiable ℝ f)
    (hLip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (oracle : E → E) (hvalid : ∀ x, ‖oracle x - gradient f x‖ ≤ eps / 16)
    (hbelow : BddBelow (Set.range f)) (start : E)
    (hgap : f start - sInf (Set.range f) ≤ Delta) :
    let run := execute oracle (program L eps (fuel Delta L eps) start)
    run.1.success = true ∧ ‖gradient f run.1.point‖ ≤ eps ∧
      run.1.squaredSteps ≤ 4 * Delta / L ∧
      (run.1.steps : ℝ) ≤ 16 * Delta * L / eps ^ 2 ∧
      (run.2 : ℝ) ≤ 1 + 16 * Delta * L / eps ^ 2 := by
  exact finite_termination_and_step_budget f L eps Delta (sInf (Set.range f)) hL heps
    hdiff hLip oracle hvalid (fun x => csInf_le hbelow ⟨x, rfl⟩) start hgap

end
end OriginalOuterGD
end

section
-- Source component: WarmAmortization.lean

namespace OriginalWarmAmortization
open scoped BigOperators

variable {ι : Type*}

theorem holder_squared_step_movement (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, (a i) ^ (2 / 7 : ℝ) ≤
      (s.card : ℝ) ^ (6 / 7 : ℝ) * (∑ i ∈ s, (a i) ^ 2) ^ (1 / 7 : ℝ) := by
  have hpq : Real.HolderConjugate (7 : ℝ) (7 / 6 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s (f := fun i => (a i) ^ (2 / 7 : ℝ)) (g := fun _ => (1 : ℝ)) hpq
    (fun i hi => Real.rpow_nonneg (ha i hi) _) (fun _ _ => by norm_num)
  have he : ∑ i ∈ s, ((a i) ^ (2 / 7 : ℝ)) ^ (7 : ℝ) = ∑ i ∈ s, (a i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (ha i hi)]
    norm_num
  simp only [mul_one, Real.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one, he] at h
  norm_num only [show (1 / (7 / 6 : ℝ)) = (6 / 7 : ℝ) by norm_num] at h
  calc
    _ ≤ (∑ i ∈ s, (a i) ^ 2) ^ (1 / 7 : ℝ) * (s.card : ℝ) ^ (6 / 7 : ℝ) := h
    _ = _ := mul_comm _ _

theorem holder_cubed_step_movement (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, (a i) ^ (2 / 7 : ℝ) ≤
      (s.card : ℝ) ^ (19 / 21 : ℝ) * (∑ i ∈ s, (a i) ^ 3) ^ (2 / 21 : ℝ) := by
  have hpq : Real.HolderConjugate (21 / 2 : ℝ) (21 / 19 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s (f := fun i => (a i) ^ (2 / 7 : ℝ)) (g := fun _ => (1 : ℝ)) hpq
    (fun i hi => Real.rpow_nonneg (ha i hi) _) (fun _ _ => by norm_num)
  have he : ∑ i ∈ s, ((a i) ^ (2 / 7 : ℝ)) ^ (21 / 2 : ℝ) = ∑ i ∈ s, (a i) ^ 3 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (ha i hi)]
    norm_num
  simp only [mul_one, Real.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one, he] at h
  norm_num only [show (1 / (21 / 19 : ℝ)) = (19 / 21 : ℝ) by norm_num,
    show (1 / (21 / 2 : ℝ)) = (2 / 21 : ℝ) by norm_num] at h
  calc
    _ ≤ (∑ i ∈ s, (a i) ^ 3) ^ (2 / 21 : ℝ) * (s.card : ℝ) ^ (19 / 21 : ℝ) := h
    _ = _ := mul_comm _ _

theorem warm_cost_sum_from_squared_steps
    (s : Finset ι) (steps radius : ι → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hstep : ∀ i ∈ s, 0 ≤ steps i)
    (hradius : ∀ i ∈ s, 0 ≤ radius i) (hwarm : ∀ i ∈ s, radius i ≤ a + b * steps i) :
    ∑ i ∈ s, (1 + (radius i) ^ (2 / 7 : ℝ)) ≤
      (s.card : ℝ) * (1 + a ^ (2 / 7 : ℝ)) +
      b ^ (2 / 7 : ℝ) * (s.card : ℝ) ^ (6 / 7 : ℝ) * (∑ i ∈ s, (steps i) ^ 2) ^ (1 / 7 : ℝ) := by
  have hpoint : ∀ i ∈ s, (radius i) ^ (2 / 7 : ℝ) ≤ a ^ (2 / 7 : ℝ) +
      b ^ (2 / 7 : ℝ) * (steps i) ^ (2 / 7 : ℝ) := by
    intro i hi
    calc
      _ ≤ (a + b * steps i) ^ (2 / 7 : ℝ) := Real.rpow_le_rpow (hradius i hi) (hwarm i hi) (by norm_num)
      _ ≤ a ^ (2 / 7 : ℝ) + (b * steps i) ^ (2 / 7 : ℝ) :=
        Real.rpow_add_le_add_rpow ha (mul_nonneg hb (hstep i hi)) (by norm_num) (by norm_num)
      _ = _ := by rw [Real.mul_rpow hb (hstep i hi)]
  have hsum := Finset.sum_le_sum (fun i hi => add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) (hpoint i hi))
  have heq : ∑ i ∈ s, (1 + (a ^ (2 / 7 : ℝ) + b ^ (2 / 7 : ℝ) * (steps i) ^ (2 / 7 : ℝ))) =
      (s.card : ℝ) * (1 + a ^ (2 / 7 : ℝ)) + b ^ (2 / 7 : ℝ) * ∑ i ∈ s, (steps i) ^ (2 / 7 : ℝ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hholder := mul_le_mul_of_nonneg_left (holder_squared_step_movement s steps hstep)
    (Real.rpow_nonneg hb (2 / 7 : ℝ))
  calc
    _ ≤ (s.card : ℝ) * (1 + a ^ (2 / 7 : ℝ)) + b ^ (2 / 7 : ℝ) * ∑ i ∈ s, (steps i) ^ (2 / 7 : ℝ) :=
      hsum.trans_eq heq
    _ ≤ _ := add_le_add le_rfl (by simpa only [mul_assoc] using hholder)

section ActualSaddle
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem actual_warm_dual_distance
    (J : Joint E F → ℝ) (L mu : ℝ) (hL : 0 < L) (hmu : 0 < mu) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (previous current : E) (approximate : F) (tau : ℝ)
    (hprevious : ‖approximate - vStar (JointSliceRegularity.curry J) L previous‖ ≤ tau) :
    ‖approximate - vStar (JointSliceRegularity.curry J) L current‖ ≤
      tau + 2 * Real.sqrt (L / mu) * ‖current - previous‖ := by
  have hstable := (actual_saddle_lipschitz_components (JointSliceRegularity.curry J) L mu hL hmu
    (JointSliceRegularity.differentiable_x_slice J hJ) (JointSliceRegularity.differentiable_y_slice J hJ) hsc
    (fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y)
    (fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v) previous current).2
  rw [norm_sub_rev previous current] at hstable
  exact (norm_sub_le_norm_sub_add_norm_sub approximate (vStar (JointSliceRegularity.curry J) L previous)
    (vStar (JointSliceRegularity.curry J) L current)).trans (add_le_add hprevious hstable)
end ActualSaddle

end OriginalWarmAmortization
end

section
-- Source component: OuterPrimalInitialization.lean

namespace OriginalOuterPrimalInitialization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem prox_displacement_from_envelope_gap
    (Phi : E → ℝ) (L lower B : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ Phi)
    (hweak : ConvexOn ℝ (Set.univ : Set E) (fun u => Phi u + L / 2 * ‖u‖ ^ 2))
    (hbelow : ∀ u, lower ≤ Phi u) (x : E)
    (hgap : MoreauTransfer.envelope Phi L x - lower ≤ B) :
    0 ≤ B ∧ ‖x - MoreauTransfer.prox Phi L x‖ ≤ Real.sqrt (B / L) := by
  rw [MoreauTransfer.envelope_eq_prox_objective Phi L hL hdiff hweak] at hgap
  unfold MoreauTransfer.objective at hgap
  have hsq : L * ‖x - MoreauTransfer.prox Phi L x‖ ^ 2 ≤ B := by
    rw [norm_sub_rev] at hgap
    linarith only [hgap, hbelow (MoreauTransfer.prox Phi L x)]
  have hB : 0 ≤ B := (by positivity : 0 ≤ L * ‖x - MoreauTransfer.prox Phi L x‖ ^ 2).trans hsq
  have hquot : ‖x - MoreauTransfer.prox Phi L x‖ ^ 2 ≤ B / L :=
    (le_div_iff₀ hL).mpr (by simpa only [mul_comm] using hsq)
  have hsqrt := Real.sq_sqrt (show 0 ≤ B / L by positivity)
  have hn := norm_nonneg (x - MoreauTransfer.prox Phi L x)
  have hr := Real.sqrt_nonneg (B / L)
  exact ⟨hB, by nlinarith only [hquot, hsqrt, hr, hn]⟩

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalPrimalElimination

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

theorem standing_primal_residual_bound
    (J : Joint E F → ℝ) (L mu lower B D : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : ∀ u, lower ≤ phi (JointSliceRegularity.curry J) u)
    (x : E) (yin : F)
    (hgap : saddleEnvelope (JointSliceRegularity.curry J) L x - lower ≤ B)
    (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    0 ≤ B ∧
      ‖x - primal J L x yin‖ ≤ Real.sqrt (B / L) + D ∧
      ‖residual J L x (yin, x)‖ / L ≤ 3 * (Real.sqrt (B / L) + D) := by
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdx := JointSliceRegularity.differentiable_x_slice J hJ
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y
  have hxy := fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v
  obtain ⟨hphi, hweak⟩ := phi_regular_from_slices f L mu hL hmu hdx hdy hsc hxx hxy
  have hE := saddleEnvelope_eq_moreau f L mu hmu hsc hdy
  rw [hE] at hgap
  obtain ⟨hB, hdisp⟩ := prox_displacement_from_envelope_gap (phi f) L lower B hL hphi hweak hbelow x hgap
  change ‖x - uStar f L x‖ ≤ Real.sqrt (B / L) at hdisp
  have hprimal := OriginalDualMinimizer.primal_at_actual_dual_saddle J L mu hL hmu hJ hLip hsc x
  have hnear := primal_lipschitz J L hL hJ hLip x yin (vStar f L x)
  rw [hprimal, norm_sub_rev] at hnear
  have hdist : ‖x - primal J L x yin‖ ≤ Real.sqrt (B / L) + D := by
    calc
      _ ≤ ‖x - uStar f L x‖ + ‖uStar f L x - primal J L x yin‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add hdisp (hnear.trans hwarm)
  have hres := OriginalDualOracleEstimates.residual_norm_upper J L hL hC2 hLip x x yin
  refine ⟨hB, hdist, (div_le_iff₀ hL).mpr ?_⟩
  calc
    _ ≤ 3 * L * ‖x - primal J L x yin‖ := hres
    _ ≤ 3 * L * (Real.sqrt (B / L) + D) := mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = _ := by ring

theorem actual_primal_simulator_at_bounded_gap
    (J : Joint E F → ℝ) (L mu rho lower B D e : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hrho : 0 ≤ rho) (he : 0 < e)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : ∀ u, lower ≤ phi (JointSliceRegularity.curry J) u)
    (x : E) (yin : F)
    (hgap : saddleEnvelope (JointSliceRegularity.curry J) L x - lower ≤ B)
    (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := OriginalDualOracleProgram.execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalDualOracleProgram.simulator L x yin x e)
    ‖run.1.u - primal J L x yin‖ ≤ e ∧
      (run.2 : ℝ) ≤ 2 + 18 * Real.log (1 + 9 * (Real.sqrt (B / L) + D) / e) := by
  have hb := standing_primal_residual_bound J L mu lower B D hL hmu hC2 hLip hsc hbelow x yin hgap hwarm
  have hs := OriginalDualOracleProgram.reduced_dual_oracle_simulation J L rho hL hrho hC2 hLip hHess x x yin e he
  dsimp only at hs ⊢
  refine ⟨hs.2.1, hs.2.2.2.2.2.trans ?_⟩
  have harg : 1 + 3 * (‖residual J L x (yin, x)‖ / L) / e ≤
      1 + 9 * (Real.sqrt (B / L) + D) / e := by
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb.2.2 (by norm_num : (0 : ℝ) ≤ 3)) he.le
    have heq : 3 * (3 * (Real.sqrt (B / L) + D)) / e = 9 * (Real.sqrt (B / L) + D) / e := by ring
    rw [heq] at hh
    exact add_le_add le_rfl hh
  have hleft : 0 < 1 + 3 * (‖residual J L x (yin, x)‖ / L) / e := by positivity
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.log_le_log hleft harg) (by norm_num))

end OriginalOuterPrimalInitialization
end

section
-- Source component: InitialSaddleRadius.lean

namespace OriginalInitialSaddleRadius

open OriginalSaddleImplicit OriginalSaddleTransfer

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem actual_yStar_lipschitz
    (J : Joint E F → ℝ) (L mu : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x z : E) :
    ‖yStar (JointSliceRegularity.curry J) x - yStar (JointSliceRegularity.curry J) z‖ ≤
      (L / mu) * ‖x - z‖ := by
  let f := JointSliceRegularity.curry J
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hmax := yStar_maximizes f mu hmu hsc hdy
  have hz : gradient (fun y => -f z y) (yStar f z) = 0 :=
    PacketCore.gradient_eq_zero_at_global_min _ _ (fun y => neg_le_neg (hmax z y))
  have hd := PacketCore.strongConvex_gradient_distance (fun y => -f x y) mu hmu
    (hsc x) (hdy x).neg (yStar f x) (fun y => neg_le_neg (hmax x y)) (yStar f z)
  rw [norm_sub_rev] at hd
  have hg := JointSliceRegularity.gradient_y_lipschitz_in_x J hJ L hLip x z (yStar f z)
  have hnegX := OriginalSaddleRegularity.gradient_neg_of_differentiable (f x) (hdy x) (yStar f z)
  have hnegZ := OriginalSaddleRegularity.gradient_neg_of_differentiable (f z) (hdy z) (yStar f z)
  rw [hnegZ, neg_eq_zero] at hz
  change ‖gradient (f x) (yStar f z) - gradient (f z) (yStar f z)‖ ≤ L * ‖x - z‖ at hg
  rw [hz, sub_zero] at hg
  rw [hnegX, norm_neg] at hd
  have hm : mu * ‖yStar f x - yStar f z‖ ≤ L * ‖x - z‖ := hd.trans hg
  rw [show L / mu * ‖x - z‖ = (L * ‖x - z‖) / mu by ring]
  apply (le_div_iff₀ hmu).mpr
  simpa only [mul_comm] using hm

theorem actual_initial_dual_radius
    (J : Joint E F → ℝ) (L mu Delta Ry : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (x0 : E) (y0 : F)
    (hgap : phi (JointSliceRegularity.curry J) x0 - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖y0 - yStar (JointSliceRegularity.curry J) x0‖ ≤ Ry) :
    ‖y0 - vStar (JointSliceRegularity.curry J) L x0‖ ≤
      Ry + (L / mu) * Real.sqrt (Delta / L) := by
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdx := JointSliceRegularity.differentiable_x_slice J hJ
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y
  have hxy := fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v
  obtain ⟨hphi, hweak⟩ := phi_regular_from_slices f L mu hL hmu hdx hdy hsc hxx hxy
  have hdisp := MoreauTransfer.prox_displacement_le_sqrt_initial_gap (phi f) L hL hphi hweak hbelow x0 Delta hgap
  change ‖uStar f L x0 - x0‖ ≤ Real.sqrt (Delta / L) at hdisp
  have hstable := actual_yStar_lipschitz J L mu hL hmu hJ hLip hsc x0 (uStar f L x0)
  rw [norm_sub_rev x0 (uStar f L x0)] at hstable
  have hmul := mul_le_mul_of_nonneg_left hdisp (show 0 ≤ L / mu by positivity)
  change ‖y0 - yStar f (uStar f L x0)‖ ≤ _
  exact (norm_sub_le_norm_sub_add_norm_sub y0 (yStar f x0) (yStar f (uStar f L x0))).trans
    (add_le_add hdual (hstable.trans hmul))

theorem actual_initial_primal_residual
    (J : Joint E F → ℝ) (L mu Delta Ry : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (x0 : E) (y0 : F)
    (hgap : phi (JointSliceRegularity.curry J) x0 - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖y0 - yStar (JointSliceRegularity.curry J) x0‖ ≤ Ry) :
    ‖OriginalPrimalElimination.residual J L x0 (y0, x0)‖ / L ≤
      3 * (Real.sqrt (Delta / L) + (Ry + (L / mu) * Real.sqrt (Delta / L))) := by
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdx := JointSliceRegularity.differentiable_x_slice J hJ
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y
  have hxy := fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v
  obtain ⟨hphi, hweak⟩ := phi_regular_from_slices f L mu hL hmu hdx hdy hsc hxx hxy
  have hE := saddleEnvelope_eq_moreau f L mu hmu hsc hdy
  have hle := MoreauTransfer.envelope_le_original (phi f) L hL hphi hweak x0
  have hegap : saddleEnvelope f L x0 - sInf (Set.range (phi f)) ≤ Delta := by
    rw [hE]
    linarith only [hle, hgap]
  have hwarm := actual_initial_dual_radius J L mu Delta Ry hL hmu hC2 hLip hsc hbelow x0 y0 hgap hdual
  exact (OriginalOuterPrimalInitialization.standing_primal_residual_bound J L mu
    (sInf (Set.range (phi f))) Delta (Ry + (L / mu) * Real.sqrt (Delta / L)) hL hmu
    hC2 hLip hsc (fun u => csInf_le hbelow ⟨u, rfl⟩) x0 y0 hegap hwarm).2.2

end OriginalInitialSaddleRadius
end

section
-- Source component: StatefulEnvelopeGradientDescent.lean

namespace OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

structure Move (E F : Type*) where
  previous : E
  next : E
  warm : F
  radius : ℝ

structure Result (E F : Type*) where
  point : E
  saddle : Joint E F
  success : Bool
  moves : List (Move E F)

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def squaredMovement (moves : List (Move E F)) : ℝ :=
  (moves.map (fun m => ‖m.next - m.previous‖ ^ 2)).sum

def moveCost (J : Joint E F → ℝ) (mu L rho tau : ℝ) (m : Move E F) : ℝ :=
  (1 + min (Real.sqrt (L / mu)) ((rho * m.radius / mu) ^ (2 / 7 : ℝ))) *
    OriginalMinimumWarmSolver.logFactor J mu L rho m.radius tau m.next m.next m.warm

def costSum (J : Joint E F → ℝ) (mu L rho tau : ℝ) (moves : List (Move E F)) : ℝ :=
  (moves.map (moveCost J mu L rho tau)).sum

def appendMove (m : Move E F) (out : Result E F) : Result E F :=
  { out with moves := m :: out.moves }

/-- A genuine stateful outer program. The next inner solve receives the previous
returned dual point. Every inner query is lowered to the original exact bundled oracle. -/
def loop (mu L rho tau eps : ℝ) : ℕ → E → Joint E F →
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F)
  | 0, x, w => .pure ⟨x, w, false, []⟩
  | n + 1, x, w =>
      let g := OriginalEnvelopeOracle.plugInGradient L x w
      if ‖g‖ ≤ eps / 2 then .pure ⟨x, w, true, []⟩
      else
        let s := OriginalOuterGD.step (2 * L) g
        let y := x + s
        let D := tau + 2 * Real.sqrt (L / mu) * ‖s‖
        let m : Move E F := ⟨x, y, w.snd, D⟩
        bind (OriginalMinimumWarmSolver.program mu L rho D tau y y w.snd) (fun wy =>
          map (appendMove m) (loop mu L rho tau eps n y wy))

def LoopSpec (J : Joint E F → ℝ) (mu L rho tau eps : ℝ) (n : ℕ) (x : E)
    (run : Result E F × ℕ) : Prop :=
  ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L run.1.point‖ ≤ tau ∧
  (2 * L) / 4 * squaredMovement run.1.moves ≤
    saddleEnvelope (JointSliceRegularity.curry J) L x - saddleEnvelope (JointSliceRegularity.curry J) L run.1.point ∧
  (run.1.moves.length : ℝ) * (eps ^ 2 / (16 * (2 * L))) ≤
    saddleEnvelope (JointSliceRegularity.curry J) L x - saddleEnvelope (JointSliceRegularity.curry J) L run.1.point ∧
  (run.1.success = true → ‖gradient (saddleEnvelope (JointSliceRegularity.curry J) L) run.1.point‖ ≤ eps) ∧
  (run.1.success = false → run.1.moves.length = n) ∧
  (run.2 : ℝ) ≤ costSum J mu L rho tau run.1.moves ∧
  (∀ m ∈ run.1.moves,
    ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
    m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
    saddleEnvelope (JointSliceRegularity.curry J) L m.previous ≤ saddleEnvelope (JointSliceRegularity.curry J) L x ∧
    saddleEnvelope (JointSliceRegularity.curry J) L m.next ≤ saddleEnvelope (JointSliceRegularity.curry J) L x)


theorem actual_loop_spec
    (J : Joint E F → ℝ) (mu L rho tau eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau) (heps : 0 < eps)
    (htolerance : 2 * L * tau ≤ eps / 16)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (n : ℕ) (x : E) (w : Joint E F)
    (hclose : ‖w - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau) :
    LoopSpec J mu L rho tau eps n x
      (execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau eps n x w)) := by
  have hL : 0 < L := hmu.trans_le hLmu
  let Ef := saddleEnvelope (JointSliceRegularity.curry J) L
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hEdiff : Differentiable ℝ Ef :=
    OriginalEnvelopeRegularity.actual_envelope_differentiable J L mu hL hmu hC2 hsc hLip
  have hELip : ∀ x y : E, ‖gradient Ef x - gradient Ef y‖ ≤ (2 * L) * ‖x - y‖ := by
    intro a b
    exact OriginalEnvelopeGradientRegularity.envelope_gradient_lipschitz_from_slices
      (JointSliceRegularity.curry J) L mu hL hmu
      (JointSliceRegularity.differentiable_x_slice J hJ)
      (JointSliceRegularity.differentiable_y_slice J hJ) hsc
      (fun y a b => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip a b y)
      (fun a y z => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip a y z) a b
  induction n generalizing x w with
  | zero => simp [loop, execute, LoopSpec, squaredMovement, costSum, hclose]

  | succ n ih =>
      let g := OriginalEnvelopeOracle.plugInGradient L x w
      have hg : ‖g - gradient Ef x‖ ≤ eps / 16 :=
        ((OriginalEnvelopeOracle.envelope_oracle_from_joint_negative_slice J L mu rho hL hmu hrho
          hC2 hsc hLip hHess x w tau hclose).1).trans htolerance
      by_cases hstop : ‖g‖ ≤ eps / 2
      · have htrue : ‖gradient Ef x‖ ≤ eps := by
          have hn := norm_sub_le g (g - gradient Ef x)
          rw [show g - (g - gradient Ef x) = gradient Ef x by abel] at hn
          linarith only [hn, hg, hstop, heps]
        have hstop' : ‖OriginalEnvelopeOracle.plugInGradient L x w‖ ≤ eps / 2 := hstop
        simpa [loop, hstop', execute, LoopSpec, squaredMovement, costSum, hclose] using htrue

      · let s := OriginalOuterGD.step (2 * L) g
        let y := x + s
        let D := tau + 2 * Real.sqrt (L / mu) * ‖s‖
        let m : Move E F := ⟨x, y, w.snd, D⟩
        let p := OriginalMinimumWarmSolver.program mu L rho D tau y y w.snd
        let first := execute (OriginalDualOracleProgram.actualOracle J) p
        let rest := execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau eps n y first.1)
        have hs : y - x = s := by dsimp only [y]; abel
        have hprevious : ‖w.snd - vStar (JointSliceRegularity.curry J) L x‖ ≤ tau := by
          have hp := WithLp.norm_snd_le E (w - zStar (JointSliceRegularity.curry J) L x)
          exact hp.trans hclose
        have hwarm : ‖w.snd - vStar (JointSliceRegularity.curry J) L y‖ ≤ D := by
          have hd := OriginalWarmAmortization.actual_warm_dual_distance J L mu hL hmu hJ hLip hsc x y w.snd tau hprevious
          simpa only [hs] using hd
        have hfirst := OriginalMinimumWarmSolver.actual_minimum_warm_solver J mu L rho D tau
          hmu hLmu hrho htau hC2 hLip hHess hsc y y w.snd hwarm
        have hfirstClose : ‖first.1 - zStar (JointSliceRegularity.curry J) L y‖ ≤ tau := hfirst.1
        have hfirstCost : (first.2 : ℝ) ≤ moveCost J mu L rho tau m := hfirst.2
        have hrec := ih y first.1 hfirstClose
        change LoopSpec J mu L rho tau eps n y rest at hrec
        rcases hrec with ⟨hfinalClose, henergy, hcount, hterminal, hfuel, hqueries, htrace⟩
        have hdec := OriginalOuterGD.one_step_descent Ef (2 * L) eps (by positivity) heps hEdiff hELip x g hg hstop
        change (2 * L) / 4 * ‖s‖ ^ 2 ≤ Ef x - Ef y ∧
          eps ^ 2 / (16 * (2 * L)) ≤ Ef x - Ef y at hdec
        change (2 * L) / 4 * squaredMovement rest.1.moves ≤ Ef y - Ef rest.1.point at henergy
        change (rest.1.moves.length : ℝ) * (eps ^ 2 / (16 * (2 * L))) ≤ Ef y - Ef rest.1.point at hcount
        have hdescent : Ef y ≤ Ef x := by
          have hp : 0 ≤ (2 * L) / 4 * ‖s‖ ^ 2 := by positivity
          linarith only [hdec.1, hp]
        have hexec : execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau eps (n + 1) x w) =
            (appendMove m rest.1, first.2 + rest.2) := by
          have hstop' : ¬ ‖OriginalEnvelopeOracle.plugInGradient L x w‖ ≤ eps / 2 := hstop
          simp only [loop, if_neg hstop', execute_bind, execute_map]
          rfl
        rw [hexec]
        have hsq : squaredMovement (m :: rest.1.moves) = ‖s‖ ^ 2 + squaredMovement rest.1.moves := by
          simp only [squaredMovement, List.map_cons, List.sum_cons]
          change ‖y - x‖ ^ 2 + _ = _
          rw [hs]
        have hcost : costSum J mu L rho tau (m :: rest.1.moves) =
            moveCost J mu L rho tau m + costSum J mu L rho tau rest.1.moves := by
          simp only [costSum, List.map_cons, List.sum_cons]
        refine ⟨hfinalClose, ?_, ?_, hterminal, ?_, ?_, ?_⟩
        · change (2 * L) / 4 * squaredMovement (m :: rest.1.moves) ≤ Ef x - Ef rest.1.point
          rw [hsq]
          nlinarith only [hdec.1, henergy]
        · change ((m :: rest.1.moves).length : ℝ) * (eps ^ 2 / (16 * (2 * L))) ≤ Ef x - Ef rest.1.point
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          nlinarith only [hdec.2, hcount]
        · intro hh
          exact congrArg Nat.succ (hfuel hh)
        · change ((first.2 + rest.2 : ℕ) : ℝ) ≤ costSum J mu L rho tau (m :: rest.1.moves)
          rw [Nat.cast_add, hcost]
          exact add_le_add hfirstCost hqueries
        · intro move hmem
          rcases List.mem_cons.mp hmem with hm | hm
          · subst move
            refine ⟨hwarm, ?_, le_refl _, hdescent⟩
            change D = tau + 2 * Real.sqrt (L / mu) * ‖y - x‖
            rw [hs]
          · obtain ⟨hlegal, hradius, hprev, hnext⟩ := htrace move hm
            exact ⟨hlegal, hradius, hprev.trans hdescent, hnext.trans hdescent⟩


def program (mu L rho D0 tau eps Delta : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F) :=
  bind (OriginalMinimumWarmSolver.program mu L rho D0 tau start start yin) (fun w =>
    loop mu L rho tau eps (OriginalOuterGD.fuel Delta (2 * L) eps) start w)

def initialCost (J : Joint E F → ℝ) (mu L rho D0 tau : ℝ) (start : E) (yin : F) : ℝ :=
  (1 + min (Real.sqrt (L / mu)) ((rho * D0 / mu) ^ (2 / 7 : ℝ))) *
    OriginalMinimumWarmSolver.logFactor J mu L rho D0 tau start start yin

/-- Finite actual original-oracle execution. The one-time initial warm solve is
separated from the one actual warm solve per executed outer move. All subsequent
centers retain the initial envelope gap, rather than importing an arbitrary-center
uniform primal-initialization assumption. -/
theorem actual_finite_termination_with_warm_trace
    (J : Joint E F → ℝ) (mu L rho D0 tau eps Delta lower : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau) (heps : 0 < eps)
    (htolerance : 2 * L * tau ≤ eps / 16)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : ∀ x, lower ≤ saddleEnvelope (JointSliceRegularity.curry J) L x)
    (start : E) (yin : F)
    (hgap : saddleEnvelope (JointSliceRegularity.curry J) L start - lower ≤ Delta)
    (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L start‖ ≤ D0) :
    let run := execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D0 tau eps Delta start yin)
    run.1.success = true ∧
    ‖gradient (saddleEnvelope (JointSliceRegularity.curry J) L) run.1.point‖ ≤ eps ∧
    ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L run.1.point‖ ≤ tau ∧
    squaredMovement run.1.moves ≤ 2 * Delta / L ∧
    (run.1.moves.length : ℝ) ≤ 32 * Delta * L / eps ^ 2 ∧
    (run.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin + costSum J mu L rho tau run.1.moves ∧
    (∀ m ∈ run.1.moves,
      ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
      m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
      saddleEnvelope (JointSliceRegularity.curry J) L m.previous - lower ≤ Delta ∧
      saddleEnvelope (JointSliceRegularity.curry J) L m.next - lower ≤ Delta) := by
  let p0 := OriginalMinimumWarmSolver.program mu L rho D0 tau start start yin
  let first := execute (OriginalDualOracleProgram.actualOracle J) p0
  let n := OriginalOuterGD.fuel Delta (2 * L) eps
  let rest := execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau eps n start first.1)
  have hL : 0 < L := hmu.trans_le hLmu
  have hfirst := OriginalMinimumWarmSolver.actual_minimum_warm_solver J mu L rho D0 tau
    hmu hLmu hrho htau hC2 hLip hHess hsc start start yin hwarm
  have hfirstClose : ‖first.1 - zStar (JointSliceRegularity.curry J) L start‖ ≤ tau := hfirst.1
  have hfirstCost : (first.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin := hfirst.2
  have hloop := actual_loop_spec J mu L rho tau eps hmu hLmu hrho htau heps htolerance
    hC2 hLip hHess hsc n start first.1 hfirstClose
  change LoopSpec J mu L rho tau eps n start rest at hloop
  rcases hloop with ⟨hclose, henergy, hcount, hterminal, hfuel, hqueries, htrace⟩
  have hvalue : saddleEnvelope (JointSliceRegularity.curry J) L start -
      saddleEnvelope (JointSliceRegularity.curry J) L rest.1.point ≤ Delta := by
    linarith only [hbelow rest.1.point, hgap]
  have hcount' : (rest.1.moves.length : ℝ) ≤ 32 * Delta * L / eps ^ 2 := by
    have hc : 0 < eps ^ 2 / (16 * (2 * L)) := by positivity
    have hh := (le_div_iff₀ hc).mpr (hcount.trans hvalue)
    convert! hh using 1 <;> field_simp <;> ring
  have hsuccess : rest.1.success = true := by
    cases hb : rest.1.success with
    | true => rfl
    | false =>
        have hs := hfuel hb
        have hceil := Nat.le_ceil (16 * Delta * (2 * L) / eps ^ 2)
        rw [hs] at hcount'
        dsimp [n, OriginalOuterGD.fuel] at hcount'
        push_cast at hcount'
        have he : 16 * Delta * (2 * L) / eps ^ 2 = 32 * Delta * L / eps ^ 2 := by ring
        rw [he] at hceil hcount'
        linarith only [hcount', hceil]
  have hexec : execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D0 tau eps Delta start yin) = (rest.1, first.2 + rest.2) := by
    simp only [program, execute_bind]
    rfl
  rw [hexec]
  refine ⟨hsuccess, hterminal hsuccess, hclose, ?_, hcount', ?_, ?_⟩
  · apply (le_div_iff₀ hL).mpr
    linarith only [henergy, hvalue]
  · simp only [Nat.cast_add]
    exact add_le_add hfirstCost hqueries
  · intro m hm
    obtain ⟨hlegal, hradius, hprev, hnext⟩ := htrace m hm
    exact ⟨hlegal, hradius, by linarith only [hprev, hgap], by linarith only [hnext, hgap]⟩

end
end OriginalStatefulEnvelopeGD
end

section
-- Source component: StatefulEnvelopeGradientCaller.lean

namespace OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

theorem actual_phi_gradient_lipschitz
    (J : Joint E F → ℝ) (mu L : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x z : E) :
    ‖gradient (phi (JointSliceRegularity.curry J)) x - gradient (phi (JointSliceRegularity.curry J)) z‖ ≤
      L * (1 + L / mu) * ‖x - z‖ := by
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdx := JointSliceRegularity.differentiable_x_slice J hJ
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y
  have hxy := fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v
  have hg (u : E) : gradient (phi f) u = gradient (fun t => f t (yStar f u)) u :=
    (phi_hasGradientAt_yStar f L mu hL hmu hdx hdy hsc hxx hxy u).gradient
  rw [hg x, hg z]
  have h1 := hxx (yStar f x) x z
  have h2 := hxy z (yStar f x) (yStar f z)
  have hy := OriginalInitialSaddleRadius.actual_yStar_lipschitz J L mu hL hmu hJ hLip hsc x z
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (gradient (fun t => f t (yStar f x)) x)
    (gradient (fun t => f t (yStar f x)) z)
    (gradient (fun t => f t (yStar f z)) z)
  have hmul := mul_le_mul_of_nonneg_left hy hL.le
  nlinarith only [h1, h2, ht, hmul]

def callerTolerance (mu L eps : ℝ) := eps / (128 * L * (1 + L / mu))

def caller (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F) :=
  program mu L rho (Ry + (L / mu) * Real.sqrt (Delta / L)) (callerTolerance mu L eps)
    (eps / 2) Delta start yin

/-- Original standing and original initialization data suffice for a real stateful
outer/inner execution and true primal-value stationarity. This result deliberately
retains the actual inner log-factor sum; its global frontier normalization is separate. -/
theorem actual_gradient_caller_from_original_inputs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let tau := callerTolerance mu L eps
    let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.1.moves.length : ℝ) ≤ 128 * Delta * L / eps ^ 2 ∧
    squaredMovement run.1.moves ≤ 2 * Delta / L ∧
    (run.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin + costSum J mu L rho tau run.1.moves ∧
    (∀ m ∈ run.1.moves,
      ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
      m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
      OriginalDualResidualQueryBound.observedRadius J L m.next m.next m.warm ≤
        3 * (Real.sqrt (Delta / L) + m.radius)) := by
  let f := JointSliceRegularity.curry J
  let lower := sInf (Set.range (phi f))
  let tau := callerTolerance mu L eps
  let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  have hratio : 0 < L / mu := by positivity
  have htau : 0 < tau := by unfold tau callerTolerance; positivity
  have htol : 2 * L * tau ≤ (eps / 2) / 16 := by
    dsimp [tau, callerTolerance]
    rw [show 2 * L * (eps / (128 * L * (1 + L / mu))) =
      (2 * L * eps) / (128 * L * (1 + L / mu)) by ring]
    apply (div_le_iff₀ (show 0 < 128 * L * (1 + L / mu) by positivity)).mpr
    have hp : 0 < L * eps := mul_pos hL heps
    have hq : 0 < L * eps * (L / mu) := mul_pos hp hratio
    nlinarith only [hp, hq]

  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdx := JointSliceRegularity.differentiable_x_slice J hJ
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y
  have hxy := fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v
  obtain ⟨hPhi, hweak⟩ := phi_regular_from_slices f L mu hL hmu hdx hdy hsc hxx hxy
  have hE := saddleEnvelope_eq_moreau f L mu hmu hsc hdy
  have hElower : ∀ x, lower ≤ saddleEnvelope f L x := by
    intro x
    rw [hE, MoreauTransfer.envelope_eq_prox_objective (phi f) L hL hPhi hweak]
    have hp := csInf_le hbelow (Set.mem_range_self (MoreauTransfer.prox (phi f) L x))
    unfold MoreauTransfer.objective
    have hn : 0 ≤ L * ‖MoreauTransfer.prox (phi f) L x - x‖ ^ 2 := by positivity
    change lower ≤ phi f (MoreauTransfer.prox (phi f) L x) + _
    linarith only [hp, hn]
  have hEgap : saddleEnvelope f L start - lower ≤ Delta := by
    have hh := MoreauTransfer.envelope_le_original (phi f) L hL hPhi hweak start
    rw [← hE] at hh
    linarith only [hh, hgap]
  have hinit := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry
    hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hh := actual_finite_termination_with_warm_trace J mu L rho D0 tau (eps / 2) Delta lower
    hmu hLmu hrho htau (by positivity) htol hC2 hLip hHess hsc hElower start yin hEgap hinit
  change run.1.success = true ∧ _ at hh
  rcases hh with ⟨htrue, hgradE, hclose, hsquares, hcount, hcost, htrace⟩
  change ‖gradient (saddleEnvelope f L) run.1.point‖ ≤ eps / 2 at hgradE
  have htransfer := exact_transfer_from_slices f L mu hL hmu hdx hdy hsc hxx hxy hbelow start Delta hgap
  have hPhiLip := actual_phi_gradient_lipschitz J mu L hmu hL hC2 hLip hsc
  have hfirst : ‖run.1.saddle.fst - uStar f L run.1.point‖ ≤ tau := by
    exact (WithLp.norm_fst_le E (run.1.saddle - zStar f L run.1.point)).trans hclose
  have houtput : ‖gradient (phi f) run.1.saddle.fst‖ ≤ eps := by
    have hd := hPhiLip run.1.saddle.fst (uStar f L run.1.point)
    have hm := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ L * (1 + L / mu) by positivity)
    have hn := norm_le_norm_sub_add (gradient (phi f) run.1.saddle.fst)
      (gradient (phi f) (uStar f L run.1.point))
    change ‖gradient (phi f) run.1.saddle.fst - gradient (phi f) (uStar f L run.1.point)‖ ≤ _ at hd
    rw [← (htransfer.1 run.1.point).2] at hn hd
    have he : L * (1 + L / mu) * tau = eps / 128 := by
      dsimp [tau, callerTolerance]
      field_simp
      <;> ring
    rw [he] at hm
    linarith only [hd, hm, hn, hgradE, heps]
  refine ⟨htrue, houtput, ?_, hsquares, hcost, ?_⟩
  · have he : 32 * Delta * L / (eps / 2) ^ 2 = 128 * Delta * L / eps ^ 2 := by field_simp; ring
    rwa [he] at hcount
  · intro m hm
    obtain ⟨hlegal, hradius, hprev, hnext⟩ := htrace m hm
    have hb := (OriginalOuterPrimalInitialization.standing_primal_residual_bound J L mu lower Delta m.radius
      hL hmu hC2 hLip hsc (fun u => csInf_le hbelow ⟨u, rfl⟩) m.next m.warm hnext hlegal).2.2
    exact ⟨hlegal, hradius, hb⟩

end
end OriginalStatefulEnvelopeGD
end

section
-- Source component: StatefulGDResourceAmortization.lean

open scoped BigOperators

namespace OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 3000000

def moveLog (J : Joint E F → ℝ) (mu L rho tau : ℝ) (m : Move E F) : ℝ :=
  OriginalMinimumWarmSolver.logFactor J mu L rho m.radius tau m.next m.next m.warm

def maximumLog (J : Joint E F → ℝ) (mu L rho tau : ℝ) (moves : List (Move E F)) : ℝ :=
  (moves.map (moveLog J mu L rho tau)).foldr max 1

def polynomialBound (mu L rho tau : ℝ) (moves : List (Move E F)) : ℝ :=
  (moves.length : ℝ) * (1 + (rho * tau / mu) ^ (2 / 7 : ℝ)) +
    (rho / mu * (2 * Real.sqrt (L / mu))) ^ (2 / 7 : ℝ) *
      (moves.length : ℝ) ^ (6 / 7 : ℝ) * squaredMovement moves ^ (1 / 7 : ℝ)

theorem list_sum_as_fin {T : Type*} (l : List T) (f : T → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  have he : List.ofFn (fun i : Fin l.length => f (l.get i)) = l.map f := by
    change List.ofFn (f ∘ l.get) = l.map f
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← he, List.sum_ofFn]

theorem maximum_log_positive (J : Joint E F → ℝ) (mu L rho tau : ℝ) (moves : List (Move E F)) :
    1 ≤ maximumLog J mu L rho tau moves := by
  induction moves with
  | nil => rfl
  | cons m moves ih =>
      exact ih.trans (le_max_right _ _)

/-- Actual per-move costs are amortized over the actual physical step trace.
The finite maximum of log-factors is retained explicitly, rather than assumed to be
uniformly polylogarithmic. -/
theorem actual_cost_sum_holder_bound
    (J : Joint E F → ℝ) (mu L rho tau : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hrho : 0 ≤ rho) (htau : 0 ≤ tau) (moves : List (Move E F))
    (hradii : ∀ m ∈ moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖) :
    costSum J mu L rho tau moves ≤
      maximumLog J mu L rho tau moves * polynomialBound mu L rho tau moves := by
  let N := moves.length
  let step : Fin N → ℝ := fun i => ‖(moves.get i).next - (moves.get i).previous‖
  let radius : Fin N → ℝ := fun i => rho * (moves.get i).radius / mu
  have hradius : ∀ i : Fin N, 0 ≤ (moves.get i).radius := by
    intro i
    rw [hradii (moves.get i) (List.get_mem _ _)]
    positivity
  have hM : 0 ≤ maximumLog J mu L rho tau moves :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (maximum_log_positive J mu L rho tau moves)
  have hpoint : ∀ i : Fin N,
      moveCost J mu L rho tau (moves.get i) ≤
        maximumLog J mu L rho tau moves * (1 + radius i ^ (2 / 7 : ℝ)) := by
    intro i
    have hlog : moveLog J mu L rho tau (moves.get i) ≤ maximumLog J mu L rho tau moves := by
      exact List.le_max_of_le' 1 (List.mem_map.mpr ⟨moves.get i, List.get_mem _ _, rfl⟩) le_rfl
    have hscale : 0 ≤ 1 + min (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ)) := by
      have hp : 0 ≤ radius i := div_nonneg (mul_nonneg hrho (hradius i)) hmu.le
      exact add_nonneg zero_le_one (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg hp _))
    have ha := mul_le_mul_of_nonneg_left hlog hscale
    have hb := mul_le_mul_of_nonneg_left
      (add_le_add_left (min_le_right (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ))) 1) hM
    change (1 + min (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ))) *
      moveLog J mu L rho tau (moves.get i) ≤ _
    exact ha.trans (by nlinarith only [hb])
  have hholder := OriginalWarmAmortization.warm_cost_sum_from_squared_steps
    (Finset.univ : Finset (Fin N)) step radius (rho * tau / mu)
    (rho / mu * (2 * Real.sqrt (L / mu))) (by positivity) (by positivity)
    (fun _ _ => norm_nonneg _) (fun i _ => div_nonneg (mul_nonneg hrho (hradius i)) hmu.le) (by
      intro i _
      have hi := hradii (moves.get i) (List.get_mem _ _)
      change rho * (moves.get i).radius / mu ≤ rho * tau / mu +
        rho / mu * (2 * Real.sqrt (L / mu)) * ‖(moves.get i).next - (moves.get i).previous‖
      rw [hi]
      ring_nf
      exact le_rfl)
  have hsq : ∑ i : Fin N, step i ^ 2 = squaredMovement moves :=
    (list_sum_as_fin moves (fun m => ‖m.next - m.previous‖ ^ 2)).symm
  have hpoly : ∑ i : Fin N, (1 + radius i ^ (2 / 7 : ℝ)) ≤ polynomialBound mu L rho tau moves := by
    simpa only [Finset.card_univ, Fintype.card_fin, hsq, N, polynomialBound] using hholder
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [← Finset.mul_sum] at hsum
  rw [costSum, list_sum_as_fin]
  exact hsum.trans (mul_le_mul_of_nonneg_left hpoly hM)


theorem squared_movement_nonnegative (moves : List (Move E F)) : 0 ≤ squaredMovement moves := by
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
    exact sq_nonneg _)

theorem one_step_squared_le_total (moves : List (Move E F)) (m : Move E F) (hm : m ∈ moves) :
    ‖m.next - m.previous‖ ^ 2 ≤ squaredMovement moves := by
  induction moves with
  | nil => cases hm
  | cons head tail ih =>
      simp only [squaredMovement, List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hm with h | h
      · subst m
        exact le_add_of_nonneg_right (squared_movement_nonnegative tail)
      · exact (ih h).trans (le_add_of_nonneg_left (sq_nonneg _))

theorem warm_radii_uniform_bound (L mu tau Delta : ℝ) (hL : 0 < L)
    (moves : List (Move E F))
    (hsquares : squaredMovement moves ≤ 2 * Delta / L)
    (hradii : ∀ m ∈ moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖) :
    ∀ m ∈ moves, m.radius ≤ tau + 2 * Real.sqrt (L / mu) * Real.sqrt (2 * Delta / L) := by
  have hnonneg : 0 ≤ 2 * Delta / L := (squared_movement_nonnegative moves).trans hsquares
  have hsq := Real.sq_sqrt hnonneg
  intro m hm
  have hstep := (one_step_squared_le_total moves m hm).trans hsquares
  have hnorm : ‖m.next - m.previous‖ ≤ Real.sqrt (2 * Delta / L) := by
    nlinarith only [hstep, hsq, norm_nonneg (m.next - m.previous), Real.sqrt_nonneg (2 * Delta / L)]
  rw [hradii m hm]
  have hh := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * Real.sqrt (L / mu) by positivity)
  linarith only [hh]

end
end OriginalStatefulEnvelopeGD
end

section
-- Source component: GDRateNormalization.lean

namespace OriginalGDRateNormalization

noncomputable section
set_option maxHeartbeats 2000000

def A1 (Delta L eps : ℝ) : ℝ := Delta * L / eps ^ 2

def ratio (mu L rho eps : ℝ) : ℝ := rho * (Real.sqrt (L / mu)) ^ 3 * eps / L ^ 2

theorem movement_normalization (mu L rho eps Delta N S : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (heps : 0 < eps) (hrho : 0 ≤ rho)
    (hDelta : 0 ≤ Delta) (hN : 0 ≤ N) (hS : 0 ≤ S)
    (hsteps : N ≤ 128 * A1 Delta L eps) (hsquares : S ≤ 2 * Delta / L) :
    (rho / mu * (2 * Real.sqrt (L / mu))) ^ (2 / 7 : ℝ) * N ^ (6 / 7 : ℝ) * S ^ (1 / 7 : ℝ) ≤
      256 * A1 Delta L eps * ratio mu L rho eps ^ (2 / 7 : ℝ) := by
  let k := Real.sqrt (L / mu)
  let b := rho / mu * (2 * k)
  let r := rho * k ^ 3 * eps / L ^ 2
  let a := A1 Delta L eps
  have hb : 0 ≤ b := by dsimp [b, k]; positivity
  have hr : 0 ≤ r := by dsimp [r, k]; positivity
  have ha : 0 ≤ a := by dsimp [a, A1]; positivity
  have hpow (x : ℝ) (hx : 0 ≤ x) (j : ℕ) : (x ^ ((j : ℝ) / 7)) ^ 7 = x ^ j := by
    calc
      _ = (x ^ ((j : ℝ) / 7)) ^ (7 : ℝ) := (Real.rpow_natCast _ _).symm
      _ = x ^ (((j : ℝ) / 7) * 7) := (Real.rpow_mul hx _ _).symm
      _ = x ^ (j : ℝ) := by congr 1; ring
      _ = x ^ j := Real.rpow_natCast _ _
  have hb2 : (b ^ (2 / 7 : ℝ)) ^ 7 = b ^ 2 := by simpa using hpow b hb 2
  have hN6 : (N ^ (6 / 7 : ℝ)) ^ 7 = N ^ 6 := by simpa using hpow N hN 6
  have hS1 : (S ^ (1 / 7 : ℝ)) ^ 7 = S := by simpa using hpow S hS 1
  have hr2 : (r ^ (2 / 7 : ℝ)) ^ 7 = r ^ 2 := by simpa using hpow r hr 2
  have hT : (b ^ (2 / 7 : ℝ) * N ^ (6 / 7 : ℝ) * S ^ (1 / 7 : ℝ)) ^ 7 = b ^ 2 * N ^ 6 * S := by
    rw [mul_pow, mul_pow, hb2, hN6, hS1]
  have hR : (256 * a * r ^ (2 / 7 : ℝ)) ^ 7 = (256 : ℝ) ^ 7 * a ^ 7 * r ^ 2 := by
    rw [mul_pow, mul_pow, hr2]
  have hbudget : b ^ 2 * N ^ 6 * S ≤ b ^ 2 * (128 * a) ^ 6 * (2 * Delta / L) := by
    gcongr
  have hroot : 0 < k := Real.sqrt_pos.mpr (by positivity)
  have hSQ : Real.sqrt (L / mu) ^ 2 = L / mu := Real.sq_sqrt (by positivity)
  have hLeq : L = mu * k ^ 2 := by change L = mu * Real.sqrt (L / mu) ^ 2; rw [hSQ]; field_simp
  have heq : b ^ 2 * (128 * a) ^ 6 * (2 * Delta / L) =
      (8 * (128 : ℝ) ^ 6) * a ^ 7 * r ^ 2 := by
    dsimp only [b, a, r, A1]
    rw [hLeq]
    field_simp
    <;> ring
  rw [heq] at hbudget
  have hc : 8 * (128 : ℝ) ^ 6 ≤ (256 : ℝ) ^ 7 := by norm_num
  have hlast := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (pow_nonneg ha 7))
    (sq_nonneg r)
  have htotal : (b ^ (2 / 7 : ℝ) * N ^ (6 / 7 : ℝ) * S ^ (1 / 7 : ℝ)) ^ 7 ≤
      (256 * a * r ^ (2 / 7 : ℝ)) ^ 7 := by
    rw [hT, hR]
    exact hbudget.trans hlast
  exact (pow_le_pow_iff_left₀ (by positivity : 0 ≤ b ^ (2 / 7 : ℝ) * N ^ (6 / 7 : ℝ) * S ^ (1 / 7 : ℝ))
    (by positivity : 0 ≤ 256 * a * r ^ (2 / 7 : ℝ)) (by norm_num : (7 : ℕ) ≠ 0)).mp htotal


theorem ratio_eq_paper (mu L rho eps : ℝ) (hmu : 0 < mu) (hL : 0 < L) :
    ratio mu L rho eps = rho * (L / mu) ^ (3 / 2 : ℝ) * eps / L ^ 2 := by
  have hk : 0 ≤ L / mu := by positivity
  have he : Real.sqrt (L / mu) ^ 3 = (L / mu) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hk]
    norm_num
  simp only [ratio, he]

theorem fixed_tolerance_ratio_bound (mu L rho eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (heps : 0 < eps) :
    rho * (eps / (128 * L * (1 + L / mu))) / mu ≤ ratio mu L rho eps := by
  have hL : 0 < L := hmu.trans_le hLmu
  have hk1 : 1 ≤ L / mu := (le_div_iff₀ hmu).mpr (by simpa using hLmu)
  have hksq := Real.sq_sqrt (show 0 ≤ L / mu by positivity)
  have hk : 1 ≤ Real.sqrt (L / mu) := by nlinarith [Real.sqrt_nonneg (L / mu)]
  have hk3 : 1 ≤ Real.sqrt (L / mu) ^ 3 := one_le_pow₀ hk
  have he : rho * (eps / (128 * L * (1 + L / mu))) / mu = rho * eps / (128 * L * (mu + L)) := by
    field_simp
    <;> ring
  rw [he]
  calc
    _ ≤ rho * eps / L ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hL)
      nlinarith only [mul_pos hL hmu, sq_nonneg L]
    _ ≤ ratio mu L rho eps := by
      dsimp [ratio]
      have hh := mul_le_mul_of_nonneg_left hk3 (show 0 ≤ rho * eps / L ^ 2 by positivity)
      convert! hh using 1 <;> ring

/-- Full GD Holder normalization with the actual caller's stricter fixed accuracy.
This arithmetic lemma includes zero gap and zero Hessian-Lipschitz modulus. -/
theorem full_gradient_polynomial_normalization (mu L rho eps Delta N S : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (heps : 0 < eps) (hrho : 0 ≤ rho)
    (hDelta : 0 ≤ Delta) (hN : 0 ≤ N) (hS : 0 ≤ S)
    (hsteps : N ≤ 128 * A1 Delta L eps) (hsquares : S ≤ 2 * Delta / L) :
    N * (1 + (rho * (eps / (128 * L * (1 + L / mu))) / mu) ^ (2 / 7 : ℝ)) +
      (rho / mu * (2 * Real.sqrt (L / mu))) ^ (2 / 7 : ℝ) * N ^ (6 / 7 : ℝ) * S ^ (1 / 7 : ℝ) ≤
        512 * A1 Delta L eps * (1 + ratio mu L rho eps ^ (2 / 7 : ℝ)) := by
  have hL : 0 < L := hmu.trans_le hLmu
  have hfixed := fixed_tolerance_ratio_bound mu L rho eps hmu hLmu hrho heps
  have hfixed0 : 0 ≤ rho * (eps / (128 * L * (1 + L / mu))) / mu := by positivity
  have hpow := Real.rpow_le_rpow hfixed0 hfixed (by norm_num : (0 : ℝ) ≤ 2 / 7)
  have hfirst : N * (1 + (rho * (eps / (128 * L * (1 + L / mu))) / mu) ^ (2 / 7 : ℝ)) ≤
      128 * A1 Delta L eps * (1 + ratio mu L rho eps ^ (2 / 7 : ℝ)) := by
    exact mul_le_mul hsteps (add_le_add le_rfl hpow)
      (by positivity) (by unfold A1; positivity)
  have hmove := movement_normalization mu L rho eps Delta N S hmu hL heps hrho hDelta hN hS hsteps hsquares
  have ha : 0 ≤ A1 Delta L eps := by unfold A1; positivity
  have hr : 0 ≤ ratio mu L rho eps ^ (2 / 7 : ℝ) := by unfold ratio; positivity
  nlinarith only [hfirst, hmove, mul_nonneg ha hr, ha]


end
end OriginalGDRateNormalization
end

section
-- Source component: StatefulGDFrontierWithExplicitLogs.lean

namespace OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 3000000

/-- The actual original-input caller, normalized to the middle-branch polynomial.
The only retained resource factor is the explicitly defined finite maximum of genuine
inner log-factors. Its global parameter-only majorant is not an assumption or conclusion. -/
theorem actual_gradient_frontier_with_explicit_logs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let tau := callerTolerance mu L eps
    let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin +
      512 * maximumLog J mu L rho tau run.1.moves * OriginalGDRateNormalization.A1 Delta L eps *
        (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ)) ∧
    (∀ m ∈ run.1.moves, m.radius ≤
      tau + 2 * Real.sqrt (L / mu) * Real.sqrt (2 * Delta / L)) := by
  let tau := callerTolerance mu L eps
  let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  have htau : 0 < tau := by unfold tau callerTolerance; positivity
  have h := actual_gradient_caller_from_original_inputs J mu L rho Delta Ry eps hmu hLmu hrho heps
    hC2 hLip hHess hsc hbelow start yin hgap hdual
  change run.1.success = true ∧ _ at h
  rcases h with ⟨htrue, hstationary, hcount, hsquares, hcost, htrace⟩
  have hradii : ∀ m ∈ run.1.moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ :=
    fun m hm => (htrace m hm).2.1
  have hholder := actual_cost_sum_holder_bound J mu L rho tau hmu hL hrho htau.le run.1.moves hradii
  have hDelta : 0 ≤ Delta := by
    have hh := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap, hh]
  have hn : (run.1.moves.length : ℝ) ≤ 128 * OriginalGDRateNormalization.A1 Delta L eps := by
    convert! hcount using 1 <;> unfold OriginalGDRateNormalization.A1 <;> ring
  have hnormalize := OriginalGDRateNormalization.full_gradient_polynomial_normalization
    mu L rho eps Delta (run.1.moves.length : ℝ) (squaredMovement run.1.moves)
    hmu hLmu heps hrho hDelta (by positivity) (squared_movement_nonnegative _) hn hsquares
  have hp : polynomialBound mu L rho tau run.1.moves ≤
      512 * OriginalGDRateNormalization.A1 Delta L eps *
        (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ)) := hnormalize
  have hM : 0 ≤ maximumLog J mu L rho tau run.1.moves :=
    zero_le_one.trans (maximum_log_positive J mu L rho tau run.1.moves)
  have hfinal := hholder.trans (mul_le_mul_of_nonneg_left hp hM)
  refine ⟨htrue, hstationary, ?_, warm_radii_uniform_bound L mu tau Delta hL _ hsquares hradii⟩
  have hc := add_le_add_left hfinal (initialCost J mu L rho D0 tau start yin)
  have hh := hcost.trans (by convert! hc using 1 <;> ring)
  convert! hh using 1 <;> ring

end
end OriginalStatefulEnvelopeGD
end

section
-- Source component: GDFirstOrderResourceCap.lean

open scoped BigOperators

namespace OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 2000000

/-- The same actual min-solver program also has the first-order polynomial cap;
no choice based on hidden instance data is required. -/
theorem actual_cost_sum_first_order_cap
    (J : Joint E F → ℝ) (mu L rho tau : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hrho : 0 ≤ rho) (moves : List (Move E F))
    (hradii : ∀ m ∈ moves, 0 ≤ m.radius) :
    costSum J mu L rho tau moves ≤
      maximumLog J mu L rho tau moves * (moves.length : ℝ) * (1 + Real.sqrt (L / mu)) := by
  let M := maximumLog J mu L rho tau moves
  have hM : 0 ≤ M := zero_le_one.trans (maximum_log_positive J mu L rho tau moves)
  have hpoint (i : Fin moves.length) : moveCost J mu L rho tau (moves.get i) ≤ M * (1 + Real.sqrt (L / mu)) := by
    let m := moves.get i
    have hm : m ∈ moves := List.get_mem _ _
    have hD := hradii m hm
    have hlog : moveLog J mu L rho tau m ≤ M :=
      List.le_max_of_le' 1 (List.mem_map.mpr ⟨m, hm, rfl⟩) le_rfl
    have hscale : 0 ≤ 1 + min (Real.sqrt (L / mu)) ((rho * m.radius / mu) ^ (2 / 7 : ℝ)) := by
      have hp : 0 ≤ rho * m.radius / mu := by positivity
      exact add_nonneg zero_le_one (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg hp _))
    have hfirst := mul_le_mul_of_nonneg_left hlog hscale
    have hcap : 1 + min (Real.sqrt (L / mu)) ((rho * m.radius / mu) ^ (2 / 7 : ℝ)) ≤
        1 + Real.sqrt (L / mu) := add_le_add (le_refl (1 : ℝ)) (min_le_left _ _)
    have hsecond := mul_le_mul_of_nonneg_left hcap hM
    exact hfirst.trans (by convert! hsecond using 1 <;> ring)
  rw [costSum, list_sum_as_fin]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  apply hs.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end
end OriginalStatefulEnvelopeGD
end

section
-- Source component: UniformBetaBoxMonotonicity.lean

namespace OriginalUniformBetaResources

open OriginalCoupledBetaSearch OriginalBetaSearchEndpoints OriginalBetaATSUniform

theorem modulus_box_monotonicity
    (c : Settings) (hc : Legal c)
    (Amin1 Amax1 Gmax1 Dmax1 Amin2 Amax2 Gmax2 Dmax2 : ℝ)
    (hAmin2 : 0 < Amin2) (hAmin : Amin2 ≤ Amin1) (hAlo : Amin1 ≤ c.A)
    (hAhi : c.A ≤ Amax1) (hAmax : Amax1 ≤ Amax2)
    (hG1 : 0 ≤ Gmax1) (hG : Gmax1 ≤ Gmax2)
    (hD1 : 0 ≤ Dmax1) (hD : Dmax1 ≤ Dmax2) :
    modulusCeiling c Amin1 Amax1 Gmax1 Dmax1 ≤
      modulusCeiling c Amin2 Amax2 Gmax2 Dmax2 := by
  have hAmin1 : 0 < Amin1 := hAmin2.trans_le hAmin
  have hAmax1 : 0 < Amax1 := hc.A_pos.trans_le hAhi
  have hAmax2 : 0 < Amax2 := hAmax1.trans_le hAmax
  have hG2 : 0 ≤ Gmax2 := hG1.trans hG
  have hD2 : 0 ≤ Dmax2 := hD1.trans hD
  obtain ⟨hb1, _, hm1, _, hl1, _, _, _⟩ := endpoint_bounds c hc Amin1 Amax1 Gmax1 Gmax1
    hAmin1 hAlo hAhi hG1 le_rfl
  obtain ⟨hb2, _, hm2, _, hl2, _, _, _⟩ := endpoint_bounds c hc Amin2 Amax2 Gmax2 Gmax2
    hAmin2 (hAmin.trans hAlo) (hAhi.trans hAmax) hG2 le_rfl
  have hlow : lambdaLow c.M c.sigmaLow c.sigma Gmax2 ≤ lambdaLow c.M c.sigmaLow c.sigma Gmax1 := by
    unfold lambdaLow
    apply min_le_min le_rfl
    apply div_le_div_of_nonneg_left
    · have hs := hc.sigma_lt_one
      have hl := hc.low_pos
      positivity
    · have hM := hc.M_pos
      positivity
    · have hM := hc.M_pos
      have hh := mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 2 * c.M)
      nlinarith only [hh]
  have hlow2 := (lambdaLow_positive c.M c.sigmaLow c.sigma Gmax2
    hc.M_pos hc.low_pos hc.sigma_lt_one hG2).1
  have hbeta : betaFloor c Amax2 Gmax2 ≤ betaFloor c Amax1 Gmax1 := by
    unfold betaFloor betaLow
    apply min_le_min le_rfl
    calc
      _ ≤ lambdaLow c.M c.sigmaLow c.sigma Gmax2 / (4 * (1 + Amax1)) :=
        div_le_div_of_nonneg_left hlow2.le (by positivity) (by linarith only [hAmax])
      _ ≤ _ := div_le_div_of_nonneg_right hlow (by positivity)
  have hmargin : marginFloor c Amin2 ≤ marginFloor c Amin1 := by
    unfold marginFloor highMargin
    apply min_le_min le_rfl
    apply div_le_div_of_nonneg_right hAmin
    unfold lambdaHigh
    have hM := hc.M_pos
    have hrho := hc.rho_pos
    have hs := hc.sigma_pos
    have hup := hc.low_pos.trans hc.low_lt_up
    positivity
  have hlambda : lambdaFloor c Amin2 Amax2 Gmax2 ≤ lambdaFloor c Amin1 Amax1 Gmax1 := by
    unfold lambdaFloor
    exact mul_le_mul hAmin ((sq_le_sq₀ hb2.le hb1.le).mpr hbeta) (sq_nonneg _) hAmin1.le
  let T1 := 2 * Amax1 / marginFloor c Amin1 ^ 2
  let T2 := 2 * Amax2 / marginFloor c Amin2 ^ 2
  let I1 := T1 / lambdaFloor c Amin1 Amax1 Gmax1 ^ 2
  let I2 := T2 / lambdaFloor c Amin2 Amax2 Gmax2 ^ 2
  have hT10 : 0 ≤ T1 := by dsimp only [T1]; positivity
  have hT20 : 0 ≤ T2 := by dsimp only [T2]; positivity
  have hT : T1 ≤ T2 := by
    dsimp only [T1, T2]
    calc
      _ ≤ 2 * Amax2 / marginFloor c Amin1 ^ 2 := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        ((sq_le_sq₀ hm2.le hm1.le).mpr hmargin)
  have hI10 : 0 ≤ I1 := by dsimp only [I1]; positivity
  have hI20 : 0 ≤ I2 := by dsimp only [I2]; positivity
  have hI : I1 ≤ I2 := by
    dsimp only [I1, I2]
    calc
      _ ≤ T2 / lambdaFloor c Amin1 Amax1 Gmax1 ^ 2 := div_le_div_of_nonneg_right hT (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left hT20 (by positivity)
        ((sq_le_sq₀ hl2.le hl1.le).mpr hlambda)
  have hratio : Amax1 / marginFloor c Amin1 ≤ Amax2 / marginFloor c Amin2 := by
    calc
      _ ≤ Amax2 / marginFloor c Amin1 := div_le_div_of_nonneg_right hAmax hm1.le
      _ ≤ _ := div_le_div_of_nonneg_left hAmax2.le hm2 hmargin
  have hmu := hc.mu_pos
  have hLg := hc.Lg_nonneg
  have hM := hc.M_pos
  have hstep : (c.Lg * Dmax1 + (c.M * Dmax1 + I1) * (Gmax1 / c.mu)) / c.mu ≤
      (c.Lg * Dmax2 + (c.M * Dmax2 + I2) * (Gmax2 / c.mu)) / c.mu := by
    gcongr
  change T1 * (Gmax1 / c.mu) + (Amax1 / marginFloor c Amin1) *
      ((c.Lg * Dmax1 + (c.M * Dmax1 + I1) * (Gmax1 / c.mu)) / c.mu) ≤
    T2 * (Gmax2 / c.mu) + (Amax2 / marginFloor c Amin2) *
      ((c.Lg * Dmax2 + (c.M * Dmax2 + I2) * (Gmax2 / c.mu)) / c.mu)
  gcongr

noncomputable def atLg (c : Settings) (Lg : ℝ) : Settings := { c with Lg := Lg }

theorem atLg_legal (c : Settings) (hc : Legal c) (Lg : ℝ) (hLg : c.Lg ≤ Lg) :
    Legal (atLg c Lg) :=
  ⟨hc.mu_pos, hc.Lg_nonneg.trans hLg, hc.M_pos, hc.A_pos, hc.sigma_pos, hc.sigma_lt_one,
    hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

theorem modulus_Lg_monotonicity
    (c : Settings) (hc : Legal c) (Lg Amin Amax Gmax Dmax : ℝ)
    (hLg : c.Lg ≤ Lg) (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ Gmax) (hD : 0 ≤ Dmax) :
    modulusCeiling c Amin Amax Gmax Dmax ≤ modulusCeiling (atLg c Lg) Amin Amax Gmax Dmax := by
  obtain ⟨_, _, hm, _, hl, _, _, _⟩ := endpoint_bounds c hc Amin Amax Gmax Gmax
    hAmin hAlo hAhi hG le_rfl
  have hAmax : 0 < Amax := hc.A_pos.trans_le hAhi
  have hmu := hc.mu_pos
  have hLg0 := hc.Lg_nonneg
  have hLg1 : 0 ≤ Lg := hLg0.trans hLg
  have hM := hc.M_pos
  let T := 2 * Amax / marginFloor c Amin ^ 2
  let I := T / lambdaFloor c Amin Amax Gmax ^ 2
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hI : 0 ≤ I := by dsimp only [I]; positivity
  change T * (Gmax / c.mu) + (Amax / marginFloor c Amin) *
      ((c.Lg * Dmax + (c.M * Dmax + I) * (Gmax / c.mu)) / c.mu) ≤
    T * (Gmax / c.mu) + (Amax / marginFloor c Amin) *
      ((Lg * Dmax + (c.M * Dmax + I) * (Gmax / c.mu)) / c.mu)
  gcongr

end OriginalUniformBetaResources
end

section
-- Source component: UniformBetaRhoMonotonicity.lean

namespace OriginalUniformBetaResources
open OriginalCoupledBetaSearch OriginalBetaSearchEndpoints OriginalBetaATSUniform
noncomputable section

def atRho (c : Settings) (rho : ℝ) : Settings := { c with rho := rho }

theorem atRho_legal (c : Settings) (hc : Legal c) (rho : ℝ) (hrho : c.rho ≤ rho) : Legal (atRho c rho) :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, hc.A_pos, hc.sigma_pos, hc.sigma_lt_one,
    hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos.trans_le hrho⟩

theorem lambdaHigh_rho_antitone (c : Settings) (hc : Legal c) (rho : ℝ) (hrho : c.rho ≤ rho) :
    lambdaHigh c.M rho c.sigma c.sigmaUp ≤ lambdaHigh c.M c.rho c.sigma c.sigmaUp := by
  have hM := hc.M_pos
  have hs := hc.sigma_pos
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hr := hc.rho_pos
  unfold lambdaHigh
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left hrho hM.le

theorem endpoint_rho_monotonicity (c : Settings) (hc : Legal c) (rho Amin Amax : ℝ)
    (hrho : c.rho ≤ rho) (hAmin : 0 < Amin) :
    marginFloor c Amin ≤ marginFloor (atRho c rho) Amin ∧
      lambdaCeiling (atRho c rho) Amax ≤ lambdaCeiling c Amax := by
  have hH := lambdaHigh_rho_antitone c hc rho hrho
  have hM := hc.M_pos
  have hs := hc.sigma_pos
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hρ : 0 < rho := hc.rho_pos.trans_le hrho
  have hHhi : 0 ≤ lambdaHigh c.M rho c.sigma c.sigmaUp := by unfold lambdaHigh; positivity
  constructor
  · change min (1 / 4 : ℝ) (Amin / (8 * (1 + lambdaHigh c.M c.rho c.sigma c.sigmaUp))) ≤
      min (1 / 4 : ℝ) (Amin / (8 * (1 + lambdaHigh c.M rho c.sigma c.sigmaUp)))
    exact min_le_min le_rfl (div_le_div_of_nonneg_left hAmin.le (by positivity) (by linarith only [hH]))
  · change 4 * Amax + 8 * (1 + lambdaHigh c.M rho c.sigma c.sigmaUp) ≤
      4 * Amax + 8 * (1 + lambdaHigh c.M c.rho c.sigma c.sigmaUp)
    linarith only [hH]

theorem uniform_tolerance_rho_mono (mu Lg M lo up sigma rho rho' : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hlo : 0 < lo) (hup : 0 < up)
    (hsigma : 0 ≤ sigma) (hrho : rho ≤ rho') :
    uniformTolerance mu Lg M lo up sigma rho ≤ uniformTolerance mu Lg M lo up sigma rho' := by
  have hstep : uniformStepFloor mu Lg M lo rho ≤ uniformStepFloor mu Lg M lo rho' := by
    change min 1 (rho / (8 * (Lg + mu / 4 + lo⁻¹ + M / 2))) ≤
      min 1 (rho' / (8 * (Lg + mu / 4 + lo⁻¹ + M / 2)))
    exact min_le_min le_rfl (div_le_div_of_nonneg_right hrho (by positivity))
  have hterm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hsigma) (by positivity : 0 ≤ 2 * up)
  exact min_le_min (div_le_div_of_nonneg_right hrho (by norm_num))
    (min_le_min le_rfl (min_le_min hterm le_rfl))

theorem precision_rho_monotonicity (c : Settings) (hc : Legal c) (rho Amin Amax Gmax sigma0 : ℝ)
    (hrho : c.rho ≤ rho) (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hGmax : 0 ≤ Gmax) (hmargin : c.sigma + c.sigmaUp < sigma0) :
    0 < queryPrecisionFloor c Amin Amax Gmax sigma0 ∧
      queryPrecisionFloor c Amin Amax Gmax sigma0 ≤ queryPrecisionFloor (atRho c rho) Amin Amax Gmax sigma0 := by
  have hc' := atRho_legal c hc rho hrho
  have he := endpoint_bounds c hc Amin Amax Gmax Gmax hAmin hAlo hAhi hGmax le_rfl
  have he' := endpoint_bounds (atRho c rho) hc' Amin Amax Gmax Gmax hAmin hAlo hAhi hGmax le_rfl
  rcases he with ⟨_, _, _, _, hlo, _, hup, _⟩
  rcases he' with ⟨_, _, _, _, _, _, hup', _⟩
  have hep := endpoint_rho_monotonicity c hc rho Amin Amax hrho hAmin
  have hcenter : centerPrecisionFloor c Amin Amax Gmax ≤ centerPrecisionFloor (atRho c rho) Amin Amax Gmax := by
    have hfirst := uniform_tolerance_rho_mono c.mu c.Lg c.M (lambdaFloor c Amin Amax Gmax)
      (lambdaCeiling c Amax) c.sigma c.rho rho hc.mu_pos hc.Lg_nonneg hc.M_pos.le hlo hup hc.sigma_pos.le hrho
    have hsecond := uniform_tolerance_mono c.mu c.Lg c.M (lambdaFloor c Amin Amax Gmax)
      (lambdaCeiling c Amax) (lambdaFloor c Amin Amax Gmax) (lambdaCeiling (atRho c rho) Amax)
      c.sigma rho hc.mu_pos hc.Lg_nonneg hc.M_pos.le hlo le_rfl hup' hep.2 hc.sigma_pos
      (hc.rho_pos.trans_le hrho)
    exact hfirst.trans hsecond
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have heta := (RobustAHPE.chosenSlack_properties (c.sigma + c.sigmaUp) sigma0
    (add_nonneg hc.sigma_pos.le hu.le) hmargin).1
  have houtput : outputPrecisionFloor c Amax sigma0 ≤ outputPrecisionFloor (atRho c rho) Amax sigma0 := by
    exact min_le_min (div_le_div_of_nonneg_right hrho (by norm_num))
      (uniform_output_tolerance_antitone c.mu c.M (lambdaCeiling c Amax) (lambdaCeiling (atRho c rho) Amax)
        (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow
        hc.mu_pos hc.M_pos hup' hep.2 heta.le hc.low_pos.le)
  exact ⟨(all_query_precision_bounds c hc Amin Amax Gmax Gmax sigma0 hAmin hAlo hAhi hGmax le_rfl hmargin).1,
    min_le_min le_rfl (min_le_min hcenter houtput)⟩

theorem modulus_rho_antitone (c : Settings) (hc : Legal c) (rho Amin Amax Gmax Dmax : ℝ)
    (hrho : c.rho ≤ rho) (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hGmax : 0 ≤ Gmax) (hDmax : 0 ≤ Dmax) :
    modulusCeiling (atRho c rho) Amin Amax Gmax Dmax ≤ modulusCeiling c Amin Amax Gmax Dmax := by
  have he := endpoint_bounds c hc Amin Amax Gmax Gmax hAmin hAlo hAhi hGmax le_rfl
  rcases he with ⟨_, _, hm0, _, hlo0, _, _, _⟩
  have hmargin := (endpoint_rho_monotonicity c hc rho Amin Amax hrho hAmin).1
  have hm1 : 0 < marginFloor (atRho c rho) Amin := hm0.trans_le hmargin
  have hAmax : 0 < Amax := hc.A_pos.trans_le hAhi
  have hmu := hc.mu_pos
  have hLg := hc.Lg_nonneg
  have hM := hc.M_pos
  let m0 := marginFloor c Amin
  let m1 := marginFloor (atRho c rho) Amin
  let lo := lambdaFloor c Amin Amax Gmax
  let T0 := 2 * Amax / m0 ^ 2
  let T1 := 2 * Amax / m1 ^ 2
  let I0 := T0 / lo ^ 2
  let I1 := T1 / lo ^ 2
  have hT0 : 0 ≤ T0 := by dsimp only [T0, m0]; positivity
  have hT1 : 0 ≤ T1 := by dsimp only [T1, m1]; positivity
  have hI0 : 0 ≤ I0 := by dsimp only [I0, lo]; positivity
  have hI1 : 0 ≤ I1 := by dsimp only [I1, lo]; positivity
  have hT : T1 ≤ T0 := by
    dsimp only [T0, T1]
    exact div_le_div_of_nonneg_left (by positivity) (by change 0 < marginFloor c Amin ^ 2; positivity)
      ((sq_le_sq₀ hm0.le hm1.le).mpr hmargin)
  have hI : I1 ≤ I0 := div_le_div_of_nonneg_right hT (sq_nonneg lo)
  have hratio : Amax / m1 ≤ Amax / m0 := div_le_div_of_nonneg_left hAmax.le hm0 hmargin
  change T1 * (Gmax / c.mu) + (Amax / m1) *
      ((c.Lg * Dmax + (c.M * Dmax + I1) * (Gmax / c.mu)) / c.mu) ≤
    T0 * (Gmax / c.mu) + (Amax / m0) *
      ((c.Lg * Dmax + (c.M * Dmax + I0) * (Gmax / c.mu)) / c.mu)
  gcongr

end
end OriginalUniformBetaResources
end

section
-- Source component: UniformBetaPrecisionBox.lean

namespace OriginalUniformBetaResources

open OriginalCoupledBetaSearch OriginalBetaSearchEndpoints OriginalBetaATSUniform

/-- Increasing the physical A/G resource box decreases its explicit positive
primitive precision floor. This is a scalar comparison of actual formulas. -/
theorem precision_box_antitone
    (c : Settings) (hc : Legal c)
    (Amin1 Amax1 Gmax1 Amin2 Amax2 Gmax2 sigma0 : ℝ)
    (hAmin2 : 0 < Amin2) (hAmin : Amin2 ≤ Amin1) (hAlo : Amin1 ≤ c.A)
    (hAhi : c.A ≤ Amax1) (hAmax : Amax1 ≤ Amax2)
    (hG1 : 0 ≤ Gmax1) (hG : Gmax1 ≤ Gmax2) (hmargin : c.sigma + c.sigmaUp < sigma0) :
    0 < queryPrecisionFloor c Amin2 Amax2 Gmax2 sigma0 ∧
      queryPrecisionFloor c Amin2 Amax2 Gmax2 sigma0 ≤
        queryPrecisionFloor c Amin1 Amax1 Gmax1 sigma0 := by
  have hAmin1 : 0 < Amin1 := hAmin2.trans_le hAmin
  have hAmax1 : 0 < Amax1 := hc.A_pos.trans_le hAhi
  have hAmax2 : 0 < Amax2 := hAmax1.trans_le hAmax
  have hG2 : 0 ≤ Gmax2 := hG1.trans hG
  obtain ⟨hb1, _, _, _, hl1, _, hu1, _⟩ := endpoint_bounds c hc Amin1 Amax1 Gmax1 Gmax1
    hAmin1 hAlo hAhi hG1 le_rfl
  obtain ⟨hb2, _, _, _, hl2, _, hu2, _⟩ := endpoint_bounds c hc Amin2 Amax2 Gmax2 Gmax2
    hAmin2 (hAmin.trans hAlo) (hAhi.trans hAmax) hG2 le_rfl
  have hlow : lambdaLow c.M c.sigmaLow c.sigma Gmax2 ≤ lambdaLow c.M c.sigmaLow c.sigma Gmax1 := by
    unfold lambdaLow
    apply min_le_min le_rfl
    apply div_le_div_of_nonneg_left
    · have hs := hc.sigma_lt_one
      have hl := hc.low_pos
      positivity
    · have hM := hc.M_pos
      positivity
    · have hM := hc.M_pos
      have hh := mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 2 * c.M)
      nlinarith only [hh]
  have hlow2 := (lambdaLow_positive c.M c.sigmaLow c.sigma Gmax2
    hc.M_pos hc.low_pos hc.sigma_lt_one hG2).1
  have hbeta : betaFloor c Amax2 Gmax2 ≤ betaFloor c Amax1 Gmax1 := by
    unfold betaFloor betaLow
    apply min_le_min le_rfl
    calc
      _ ≤ lambdaLow c.M c.sigmaLow c.sigma Gmax2 / (4 * (1 + Amax1)) :=
        div_le_div_of_nonneg_left hlow2.le (by positivity) (by linarith only [hAmax])
      _ ≤ _ := div_le_div_of_nonneg_right hlow (by positivity)
  have hlo : lambdaFloor c Amin2 Amax2 Gmax2 ≤ lambdaFloor c Amin1 Amax1 Gmax1 := by
    unfold lambdaFloor
    exact mul_le_mul hAmin ((sq_le_sq₀ hb2.le hb1.le).mpr hbeta) (sq_nonneg _) hAmin1.le
  have hup : lambdaCeiling c Amax1 ≤ lambdaCeiling c Amax2 := by
    unfold lambdaCeiling
    linarith only [hAmax]
  have hcenter : centerPrecisionFloor c Amin2 Amax2 Gmax2 ≤ centerPrecisionFloor c Amin1 Amax1 Gmax1 := by
    exact uniform_tolerance_mono c.mu c.Lg c.M (lambdaFloor c Amin2 Amax2 Gmax2)
      (lambdaCeiling c Amax2) (lambdaFloor c Amin1 Amax1 Gmax1) (lambdaCeiling c Amax1)
      c.sigma c.rho hc.mu_pos hc.Lg_nonneg hc.M_pos.le hl2 hlo hu1 hup hc.sigma_pos hc.rho_pos
  have heta := (RobustAHPE.chosenSlack_properties (c.sigma + c.sigmaUp) sigma0
    (add_nonneg hc.sigma_pos.le (hc.low_pos.trans hc.low_lt_up).le) hmargin).1
  have houtput : outputPrecisionFloor c Amax2 sigma0 ≤ outputPrecisionFloor c Amax1 sigma0 := by
    exact min_le_min le_rfl (uniform_output_tolerance_antitone c.mu c.M (lambdaCeiling c Amax2)
      (lambdaCeiling c Amax1) (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow
      hc.mu_pos hc.M_pos hu1 hup heta.le hc.low_pos.le)
  refine ⟨(all_query_precision_bounds c hc Amin2 Amax2 Gmax2 Gmax2 sigma0 hAmin2
    (hAmin.trans hAlo) (hAhi.trans hAmax) hG2 le_rfl hmargin).1, ?_⟩
  exact min_le_min le_rfl (min_le_min hcenter houtput)

end OriginalUniformBetaResources
end

section
-- Source component: PositiveWarmPhysicalResourceBox.lean

namespace OriginalPositiveWarmPhysicalResourceBox

open OriginalCoupledBetaSearch OriginalFirstCoupledStep OriginalRobustTrajectory
open OriginalUniformBetaResources

noncomputable section
set_option maxHeartbeats 3000000

def atPositiveWeight (c : Settings) (R : ℝ) : Settings := {atRadius c R with A := 1}

theorem positive_weight_legal (c : Settings) (hc : CommonLegal c) (R : ℝ) (hR : 0 < R) :
    Legal (atPositiveWeight c R) :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, by norm_num [atPositiveWeight], hc.sigma_pos,
    hc.sigma_lt_one, hc.low_pos, hc.low_lt_up, hc.gap, by
      change 0 < c.mu * R / 2
      exact div_pos (mul_pos hc.mu_pos hR) (by norm_num)⟩

def Amin (c : Settings) (Rmax : ℝ) := effectiveWeightFloor c Rmax

def Amax (c : Settings) (Rmin : ℝ) (nmax : ℕ) := weightCeiling (atRadius c Rmin) nmax

def Gmax (c : Settings) (Rmax : ℝ) := observedCeiling c Rmax

def precisionBox (c : Settings) (sigma0 Rmin Rmax : ℝ) (nmax : ℕ) :=
  queryPrecisionFloor (atPositiveWeight c Rmin) (Amin c Rmax) (Amax c Rmin nmax) (Gmax c Rmax) sigma0

def modulusBox (c : Settings) (Rmin Rmax : ℝ) (nmax : ℕ) :=
  modulusCeiling (atPositiveWeight c Rmin) (Amin c Rmax) (Amax c Rmin nmax)
    (Gmax c Rmax) (Rmax + stateRadius c Rmax)

theorem lambda_cap_radius_antitone (c : Settings) (hc : CommonLegal c) (Rmin R : ℝ)
    (hmin : 0 < Rmin) (hR : Rmin ≤ R) :
    lambdaCap (atRadius c R) ≤ lambdaCap (atRadius c Rmin) := by
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hRpos : 0 < R := hmin.trans_le hR
  have hM := hc.M_pos
  have hmu := hc.mu_pos
  have hsigma := hc.sigma_pos
  unfold lambdaCap atRadius
  dsimp only
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hR hmu.le) (by norm_num : (0 : ℝ) ≤ 2)) hM.le

theorem physical_parameter_box
    (c : Settings) (hc : CommonLegal c) (sigma0 Rmin R Rmax : ℝ) (n nmax : ℕ)
    (hmin : 0 < Rmin) (hlo : Rmin ≤ R) (hhi : R ≤ Rmax) (hn : n ≤ nmax)
    (hmargin : c.sigma + c.sigmaUp < sigma0) :
    0 < precisionBox c sigma0 Rmin Rmax nmax ∧
      precisionBox c sigma0 Rmin Rmax nmax ≤ uniformPrecisionFloor (atRadius c R) sigma0 R n ∧
      uniformModulusCeiling (atRadius c R) R n ≤ modulusBox c Rmin Rmax nmax := by
  have hR : 0 < R := hmin.trans_le hlo
  have hmax : 0 < Rmax := hR.trans_le hhi
  have hlegal := positive_weight_legal c hc R hR
  have hbase := positive_weight_legal c hc Rmin hmin
  have hcommon : CommonLegal (atRadius c R) :=
    ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, hc.sigma_pos, hc.sigma_lt_one,
      hc.low_pos, hc.low_lt_up, hc.gap, by
        change 0 < c.mu * R / 2
        exact div_pos (mul_pos hc.mu_pos hR) (by norm_num)⟩
  have hminA : 0 < Amin c Rmax := by
    unfold Amin effectiveWeightFloor
    exact lt_min (by norm_num) (firstWeightFloor_positive c hc Rmax hmax.le)
  have hAmin : Amin c Rmax ≤ effectiveWeightFloor (atRadius c R) R := by
    exact min_le_min le_rfl (firstWeightFloor_antitone c hc R Rmax hR.le hhi)
  have hloA : effectiveWeightFloor (atRadius c R) R ≤ (atPositiveWeight c R).A := min_le_left _ _
  have hhiA : (atPositiveWeight c R).A ≤ weightCeiling (atRadius c R) n := by
    have hcap := lambdaCap_positive (atRadius c R) hcommon
    change 1 ≤ 1 + lambdaCap (atRadius c R) * (n : ℝ) ^ 2
    exact le_add_of_nonneg_right (mul_nonneg hcap.le (sq_nonneg _))
  have hAmax : weightCeiling (atRadius c R) n ≤ Amax c Rmin nmax := by
    have hcap := lambda_cap_radius_antitone c hc Rmin R hmin hlo
    have hcap0 := (lambdaCap_positive (atRadius c R) hcommon).le
    have hcapMin0 := hcap0.trans hcap
    have hnpow : (n : ℝ) ^ 2 ≤ (nmax : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hn 2
    change 1 + lambdaCap (atRadius c R) * (n : ℝ) ^ 2 ≤
      1 + lambdaCap (atRadius c Rmin) * (nmax : ℝ) ^ 2
    gcongr
  have hG0 : 0 ≤ observedCeiling (atRadius c R) R := by
    have hstate : 0 ≤ stateRadius c R := (hR.le.trans (stateRadius_ge_D c hc R hR.le))
    change 0 ≤ 2 + c.Lg * (R + 2 * stateRadius c R)
    have hLg := hc.Lg_nonneg
    positivity
  have hstate := stateRadius_monotone c hc R Rmax hR.le hhi
  have hG : observedCeiling (atRadius c R) R ≤ Gmax c Rmax := by
    change 2 + c.Lg * (R + 2 * stateRadius c R) ≤ 2 + c.Lg * (Rmax + 2 * stateRadius c Rmax)
    have hLg := hc.Lg_nonneg
    gcongr
  have hmargin' : (atPositiveWeight c R).sigma + (atPositiveWeight c R).sigmaUp < sigma0 := hmargin
  have hprec := precision_box_antitone (atPositiveWeight c R) hlegal
    (effectiveWeightFloor (atRadius c R) R) (weightCeiling (atRadius c R) n)
    (observedCeiling (atRadius c R) R) (Amin c Rmax) (Amax c Rmin nmax) (Gmax c Rmax) sigma0
    hminA hAmin hloA hhiA hAmax hG0 hG hmargin'
  have hrho : (atPositiveWeight c Rmin).rho ≤ (atPositiveWeight c R).rho := by
    change c.mu * Rmin / 2 ≤ c.mu * R / 2
    gcongr
    exact hc.mu_pos.le
  have hbaseLo : Amin c Rmax ≤ (atPositiveWeight c Rmin).A := min_le_left _ _
  have hbaseHi : (atPositiveWeight c Rmin).A ≤ Amax c Rmin nmax := by
    have hcap := lambda_cap_radius_antitone c hc Rmin Rmin hmin le_rfl
    change 1 ≤ 1 + lambdaCap (atRadius c Rmin) * (nmax : ℝ) ^ 2
    have hpos : 0 < lambdaCap (atRadius c Rmin) := by
      unfold lambdaCap atRadius
      have hM := hc.M_pos
      have hm := hc.mu_pos
      have hs := hc.sigma_pos
      have hu := hc.low_pos.trans hc.low_lt_up
      positivity
    exact le_add_of_nonneg_right (mul_nonneg hpos.le (sq_nonneg _))
  have hbaseG : 0 ≤ Gmax c Rmax := hG0.trans hG
  have hprho := precision_rho_monotonicity (atPositiveWeight c Rmin) hbase (atPositiveWeight c R).rho
    (Amin c Rmax) (Amax c Rmin nmax) (Gmax c Rmax) sigma0 hrho hminA hbaseLo hbaseHi hbaseG hmargin
  have hpb : queryPrecisionFloor (atRho (atPositiveWeight c Rmin) (atPositiveWeight c R).rho)
      (Amin c Rmax) (Amax c Rmin nmax) (Gmax c Rmax) sigma0 =
      queryPrecisionFloor (atPositiveWeight c R) (Amin c Rmax) (Amax c Rmin nmax) (Gmax c Rmax) sigma0 := rfl
  rw [hpb] at hprho
  have hD0 : 0 ≤ R + stateRadius c R := by
    have hs : 0 ≤ stateRadius c R := hR.le.trans (stateRadius_ge_D c hc R hR.le)
    positivity
  have hD : R + stateRadius c R ≤ Rmax + stateRadius c Rmax := add_le_add hhi hstate
  have hmod := modulus_box_monotonicity (atPositiveWeight c R) hlegal
    (effectiveWeightFloor (atRadius c R) R) (weightCeiling (atRadius c R) n)
    (observedCeiling (atRadius c R) R) (R + stateRadius c R)
    (Amin c Rmax) (Amax c Rmin nmax) (Gmax c Rmax) (Rmax + stateRadius c Rmax)
    hminA hAmin hloA hhiA hAmax hG0 hG hD0 hD
  have hstateMax : 0 ≤ stateRadius c Rmax := hmax.le.trans (stateRadius_ge_D c hc Rmax hmax.le)
  have hmrho := modulus_rho_antitone (atPositiveWeight c Rmin) hbase (atPositiveWeight c R).rho
    (Amin c Rmax) (Amax c Rmin nmax) (Gmax c Rmax) (Rmax + stateRadius c Rmax)
    hrho hminA hbaseLo hbaseHi hbaseG (add_nonneg hmax.le hstateMax)
  have hmb : modulusCeiling (atRho (atPositiveWeight c Rmin) (atPositiveWeight c R).rho)
      (Amin c Rmax) (Amax c Rmin nmax) (Gmax c Rmax) (Rmax + stateRadius c Rmax) =
      modulusCeiling (atPositiveWeight c R) (Amin c Rmax) (Amax c Rmin nmax) (Gmax c Rmax)
        (Rmax + stateRadius c Rmax) := rfl
  rw [hmb] at hmrho
  exact ⟨hprho.1, hprho.2.trans hprec.2, hmod.trans hmrho⟩

end
end OriginalPositiveWarmPhysicalResourceBox
end

section
-- Source component: PositiveWarmRestartResourceBox.lean

namespace OriginalPositiveWarmPhysicalResourceBox

open OriginalCoupledBetaSearch OriginalFirstCoupledStep OriginalRobustTrajectory
open OriginalUniformBetaResources

noncomputable section
set_option maxHeartbeats 3000000

noncomputable def getterCountBox (c : Settings) (Rmin Rmax : ℝ) (nmax : ℕ) : ℕ :=
  Nat.ceil (7 + 2 * Real.logb 2 (max 1 (2 * modulusBox c Rmin Rmax nmax /
    (thresholdHigh c - thresholdLow c))))

theorem physical_getter_count_box
    (c : Settings) (hc : CommonLegal c) (sigma0 Rmin R Rmax : ℝ) (n nmax : ℕ)
    (hmin : 0 < Rmin) (hlo : Rmin ≤ R) (hhi : R ≤ Rmax) (hn : n ≤ nmax)
    (hmargin : c.sigma + c.sigmaUp < sigma0) :
    getterCountCeiling (atRadius c R) R n ≤ getterCountBox c Rmin Rmax nmax := by
  have hbox := (physical_parameter_box c hc sigma0 Rmin R Rmax n nmax hmin hlo hhi hn hmargin).2.2
  have hgap : 0 < thresholdHigh c - thresholdLow c := by
    apply sub_pos.mpr
    exact (div_lt_div_iff_of_pos_right hc.M_pos).mpr hc.gap
  have hquot := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbox (by norm_num : (0 : ℝ) ≤ 2)) hgap.le
  have hmax := max_le_max (le_refl (1 : ℝ)) hquot
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax
  apply Nat.ceil_le_ceil
  change 7 + 2 * Real.logb 2 (max 1 (2 * uniformModulusCeiling (atRadius c R) R n /
    (thresholdHigh c - thresholdLow c))) ≤ _
  linarith only [hlog]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A single physical resource box controls every actual positive restart stage.
The precision bound is an explicit inverse-polynomial formula evaluated only at the
fixed smallest radius and the fixed largest radius/iteration ceiling. -/
theorem whole_restart_physical_box
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → OriginalBetaATSTrial.Answer E}
    (H : Hypotheses g c sigma0 D getter)
    (Rmin Rmax : ℝ) (hmin : 0 < Rmin) (R : ℝ) (hR : 0 < R) (hhi : R ≤ Rmax)
    (r : ℕ) (hremain : Rmin ≤ R / (2 : ℝ) ^ r) :
    let nmax := contractionIterations c sigma0 Rmax
    0 < min 1 (precisionBox c sigma0 Rmin Rmax nmax) ∧
      min 1 (precisionBox c sigma0 Rmin Rmax nmax) ≤ precisionMinimum c sigma0 r R ∧
      coefficientMaximum (radiusGetterFactor c sigma0) r R ≤ getterCountBox c Rmin Rmax nmax := by
  let nmax := contractionIterations c sigma0 Rmax
  have hcurlo : Rmin ≤ R := hremain.trans (div_le_self hR.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have hn := contraction_iterations_monotone H R Rmax hR.le hhi
  have hbox := physical_parameter_box c H.common sigma0 Rmin R Rmax
    (contractionIterations c sigma0 R) nmax hmin hcurlo hhi hn H.margin
  have hfloor : 0 < min 1 (precisionBox c sigma0 Rmin Rmax nmax) := lt_min zero_lt_one hbox.1
  refine ⟨hfloor, ?_⟩
  clear hfloor hbox hn hcurlo
  induction r generalizing R with
  | zero => simp only [precisionMinimum, coefficientMaximum, min_le_left, Nat.zero_le, and_self]
  | succ r ih =>
      have hcurlo : Rmin ≤ R := hremain.trans
        (div_le_self hR.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
      have hn := contraction_iterations_monotone H R Rmax hR.le hhi
      have hbox := physical_parameter_box c H.common sigma0 Rmin R Rmax
        (contractionIterations c sigma0 R) nmax hmin hcurlo hhi hn H.margin
      have hcount := physical_getter_count_box c H.common sigma0 Rmin R Rmax
        (contractionIterations c sigma0 R) nmax hmin hcurlo hhi hn H.margin
      have hremain' : Rmin ≤ (R / 2) / (2 : ℝ) ^ r := by
        have he : (R / 2) / (2 : ℝ) ^ r = R / (2 : ℝ) ^ (r + 1) := by
          rw [pow_succ]
          field_simp
          <;> ring
        rwa [he]
      have ht := ih (R / 2) (by positivity) (by linarith only [hhi, hR]) hremain'
      constructor
      · change min 1 (precisionBox c sigma0 Rmin Rmax nmax) ≤
          min (radiusPrecision c sigma0 R) (precisionMinimum c sigma0 r (R / 2))
        exact le_min ((min_le_right _ _).trans hbox.2.1) ht.1
      · change max (radiusGetterFactor c sigma0 R)
          (coefficientMaximum (radiusGetterFactor c sigma0) r (R / 2)) ≤ _
        exact max_le hcount ht.2

end
end OriginalPositiveWarmPhysicalResourceBox
end

section
-- Source component: UniformPrimitiveWarmBudget.lean

namespace OriginalUniformPrimitiveWarmBudget

open OriginalSaddleImplicit OriginalDualGetterImplementation OriginalDualResidualQueryBound

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def ballNumber (L rho Obsmax Bmax floorBox : ℝ) : ℕ :=
  Nat.ceil (2 + 18 * Real.log (1 + 3 * (Obsmax + Bmax) / accuracyRadius L rho floorBox))

noncomputable def recoveryNumber (Obsmax Dmax tau : ℝ) : ℕ :=
  Nat.ceil (2 + 18 * Real.log (1 + 3 * (Obsmax + (Dmax + tau / 4)) / (tau / 4)))

theorem ball_budget_uniform (J : Joint E F → ℝ) (L rho Obsmax B Bmax floor floorBox : ℝ)
    (hL : 0 < L) (hrho : 0 ≤ rho) (hB : 0 ≤ B) (hBmax : B ≤ Bmax)
    (hfloor : 0 < floorBox) (hprecision : floorBox ≤ floor)
    (x u0 : E) (yin : F) (hobs : observedRadius J L x u0 yin ≤ Obsmax) :
    queryBallBudget J L rho x u0 yin B floor ≤ ballNumber L rho Obsmax Bmax floorBox := by
  have he := accuracyRadius_positive L rho floorBox hL hrho hfloor
  have he' := accuracyRadius_positive L rho floor hL hrho (hfloor.trans_le hprecision)
  have hemono := accuracyRadius_mono L rho floorBox floor hL hrho hprecision
  have hobs0 : 0 ≤ observedRadius J L x u0 yin := by unfold observedRadius; positivity
  have hnum : 0 ≤ 3 * (observedRadius J L x u0 yin + B) := by positivity
  have hquot : 3 * (observedRadius J L x u0 yin + B) / accuracyRadius L rho floor ≤
      3 * (Obsmax + Bmax) / accuracyRadius L rho floorBox := by
    calc
      _ ≤ 3 * (observedRadius J L x u0 yin + B) / accuracyRadius L rho floorBox :=
        div_le_div_of_nonneg_left hnum he hemono
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hobs hBmax) (by norm_num : (0 : ℝ) ≤ 3)) he.le
  have hlog := Real.log_le_log (show 0 < 1 + 3 * (observedRadius J L x u0 yin + B) /
    accuracyRadius L rho floor by positivity) (add_le_add le_rfl hquot)
  exact Nat.ceil_le_ceil (by linarith only [hlog])

theorem recovery_budget_uniform (J : Joint E F → ℝ) (L Obsmax D Dmax tau : ℝ)
    (hL : 0 < L) (hD : 0 ≤ D) (hDmax : D ≤ Dmax) (htau : 0 < tau)
    (x u0 : E) (yin : F) (hobs : observedRadius J L x u0 yin ≤ Obsmax) :
    OriginalDualPrimalRecovery.queryBudget J L D tau x u0 yin ≤ recoveryNumber Obsmax Dmax tau := by
  have hobs0 : 0 ≤ observedRadius J L x u0 yin := by unfold observedRadius; positivity
  have hquot := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add hobs (add_le_add_right hDmax (tau / 4)))
      (by norm_num : (0 : ℝ) ≤ 3)) (show 0 ≤ tau / 4 by positivity)
  have harg : 1 + 3 * (observedRadius J L x u0 yin + (D + tau / 4)) / (tau / 4) ≤
      1 + 3 * (Obsmax + (Dmax + tau / 4)) / (tau / 4) := by
    convert! add_le_add_left hquot 1 using 1 <;> ring
  have hlog := Real.log_le_log (show 0 < 1 + 3 * (observedRadius J L x u0 yin + (D + tau / 4)) /
    (tau / 4) by positivity) harg
  exact Nat.ceil_le_ceil (by linarith only [hlog])

end OriginalUniformPrimitiveWarmBudget
end

section
-- Source component: UniformFirstWarmLogFactor.lean

namespace OriginalUniformFirstWarmLog

noncomputable section
set_option maxHeartbeats 3000000

open OriginalMinimumWarmSolver OriginalSaddleFirstOrder

def uniformFactor (mu L rho Dmax tau Obsmax : ℝ) : ℝ :=
  (2 + 18 * Real.log (1 + 24 * Obsmax / tau)) +
    (36 * Real.sqrt 2 * primitiveUniformCost mu L rho (2 * Dmax) (tau / 2) +
      (2 + 18 * Real.log 145)) * (1 + Real.logb 2 (max 1 (2 * Dmax / tau)))

theorem primitive_cost_nonnegative (mu L rho R d : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (hR : 0 ≤ R) (hd : 0 < d) :
    0 ≤ primitiveUniformCost mu L rho R d := by
  have hf := (CertifiedFirstOrder.precision_floor_bounds mu (2 * L) (d / 2)
    hmu (by positivity) (by positivity)).1
  have he : 0 < OriginalDualFirstOrder.primalAccuracyFloor L rho
      (CertifiedFirstOrder.precisionFloor mu (2 * L) (d / 2)) := by
    unfold OriginalDualFirstOrder.primalAccuracyFloor
    positivity
  have hquery : 0 ≤ CertifiedFirstOrder.queryRadius mu (2 * L) R := by
    unfold CertifiedFirstOrder.queryRadius
    positivity
  have hlog : 0 ≤ Real.log (1 + 9 * (2 * R + R + 2 * CertifiedFirstOrder.queryRadius mu (2 * L) R) /
      OriginalDualFirstOrder.primalAccuracyFloor L rho
        (CertifiedFirstOrder.precisionFloor mu (2 * L) (d / 2))) := by
    apply Real.log_nonneg
    have hq : 0 ≤ 9 * (2 * R + R + 2 * CertifiedFirstOrder.queryRadius mu (2 * L) R) /
        OriginalDualFirstOrder.primalAccuracyFloor L rho
          (CertifiedFirstOrder.precisionFloor mu (2 * L) (d / 2)) := by positivity
    linarith only [hq]
  unfold primitiveUniformCost OriginalDualFirstOrder.perGradientCost
  positivity

theorem primitive_cost_radius_mono (mu L rho R S d : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (hR : 0 ≤ R) (hRS : R ≤ S) (hd : 0 < d) :
    primitiveUniformCost mu L rho R d ≤ primitiveUniformCost mu L rho S d := by
  have hf := (CertifiedFirstOrder.precision_floor_bounds mu (2 * L) (d / 2)
    hmu (by positivity) (by positivity)).1
  have hquery : CertifiedFirstOrder.queryRadius mu (2 * L) R ≤ CertifiedFirstOrder.queryRadius mu (2 * L) S := by
    unfold CertifiedFirstOrder.queryRadius
    gcongr
  have hquery0 : 0 ≤ CertifiedFirstOrder.queryRadius mu (2 * L) R := by
    unfold CertifiedFirstOrder.queryRadius
    positivity
  exact per_gradient_cost_mono L rho (2 * R) R (2 * CertifiedFirstOrder.queryRadius mu (2 * L) R)
    (CertifiedFirstOrder.precisionFloor mu (2 * L) (d / 2))
    (2 * S) S (2 * CertifiedFirstOrder.queryRadius mu (2 * L) S)
    (CertifiedFirstOrder.precisionFloor mu (2 * L) (d / 2)) hL hrho hf le_rfl (by positivity)
    (by linarith only [hRS, hquery])

theorem first_factor_uniform_bound (mu L rho D tau Obs Dmax Obsmax : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hD : 0 ≤ D) (hDmax : D ≤ Dmax) (htauMax : tau ≤ Dmax)
    (hObs : 0 ≤ Obs) (hObsMax : Obs ≤ Obsmax) :
    0 ≤ uniformFactor mu L rho Dmax tau Obsmax ∧
      firstLogFactor mu L rho D tau Obs ≤ uniformFactor mu L rho Dmax tau Obsmax := by
  let R := OriginalDualWarmFirstOrder.workingRadius D tau
  have hR : 0 < R := lt_of_lt_of_le (by positivity : 0 < tau / 2) (le_max_right _ _)
  have hRlo : tau / 2 ≤ R := le_max_right _ _
  have hRhi : R ≤ Dmax := max_le hDmax (by linarith only [htauMax, htau])
  have hmax : 0 < Dmax := htau.trans_le htauMax
  have hobsmax : 0 ≤ Obsmax := hObs.trans hObsMax
  have hmin : min (2 * R) tau = tau := min_eq_right (by linarith only [hRlo])
  have hC := primitive_cost_radius_mono mu L rho (2 * R) (2 * Dmax) (tau / 2)
    hmu hL hrho (by positivity) (by linarith only [hRhi]) (by positivity)
  have hC0 := primitive_cost_nonnegative mu L rho (2 * R) (tau / 2) hmu hL hrho (by positivity) (by positivity)
  have hCmax0 := primitive_cost_nonnegative mu L rho (2 * Dmax) (tau / 2) hmu hL hrho (by positivity) (by positivity)
  have hfrac : 12 * Obs / R ≤ 24 * Obsmax / tau := by
    calc
      _ ≤ 12 * Obsmax / R := by gcongr
      _ ≤ 12 * Obsmax / (tau / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hRlo
      _ = _ := by ring
  have hlog := Real.log_le_log (show 0 < 1 + 12 * Obs / R by positivity) (add_le_add le_rfl hfrac)
  have hratio := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRhi (by norm_num : (0 : ℝ) ≤ 2)) htau.le
  have hlogb := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (max_le_max (le_refl (1 : ℝ)) hratio)
  have hT0 : 0 ≤ 1 + Real.logb 2 (max 1 (2 * R / tau)) := by
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (le_max_left 1 (2 * R / tau))
    positivity
  have hTmax0 : 0 ≤ 1 + Real.logb 2 (max 1 (2 * Dmax / tau)) := by
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (le_max_left 1 (2 * Dmax / tau))
    positivity
  have h145 : 0 ≤ Real.log (145 : ℝ) := Real.log_nonneg (by norm_num)
  have hAmax0 : 0 ≤ 2 + 18 * Real.log (1 + 24 * Obsmax / tau) := by
    have hh := Real.log_nonneg (show 1 ≤ 1 + 24 * Obsmax / tau from le_add_of_nonneg_right (by positivity))
    positivity
  have hB0 : 0 ≤ 36 * Real.sqrt 2 * primitiveUniformCost mu L rho (2 * R) (tau / 2) + (2 + 18 * Real.log 145) := by positivity
  have hBmax0 : 0 ≤ 36 * Real.sqrt 2 * primitiveUniformCost mu L rho (2 * Dmax) (tau / 2) + (2 + 18 * Real.log 145) := by positivity
  have hB := add_le_add_right (mul_le_mul_of_nonneg_left hC (show 0 ≤ 36 * Real.sqrt 2 by positivity)) (2 + 18 * Real.log 145)
  have hT := add_le_add_left hlogb 1
  have hprod := mul_le_mul (by convert! hB using 1 <;> ring) (by convert! hT using 1 <;> ring) hT0 hBmax0
  unfold uniformFactor firstLogFactor
  change 0 ≤ _ ∧ (2 + 18 * Real.log (1 + 12 * Obs / R)) +
    (36 * Real.sqrt 2 * primitiveUniformCost mu L rho (2 * R) (min (2 * R) tau / 2) +
      (2 + 18 * Real.log 145)) * (1 + Real.logb 2 (max 1 (2 * R / tau))) ≤ _
  rw [hmin]
  exact ⟨by positivity, by nlinarith only [hlog, hprod]⟩

end
end OriginalUniformFirstWarmLog
end

section
-- Source component: UniformPositiveWarmLogFactor.lean

namespace OriginalUniformPositiveWarmLog

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalDualCurvature OriginalBetaATSTrial OriginalRobustTrajectory
open OriginalDualGetterImplementation OriginalDualResidualQueryBound
open OriginalPositiveWarmPhysicalResourceBox OriginalUniformPrimitiveWarmBudget

noncomputable section
set_option maxHeartbeats 4000000

def settings (mu L rho Dmax : ℝ) := OriginalActualDualPositiveContraction.parameters mu L rho Dmax

def iterationsMax (mu L rho Dmax : ℝ) : ℕ := contractionIterations (settings mu L rho Dmax) (1 / 2) Dmax

def precisionFloor (mu L rho Dmax tau : ℝ) : ℝ :=
  min 1 (precisionBox (settings mu L rho Dmax) (1 / 2) (tau / 8) Dmax (iterationsMax mu L rho Dmax))

def getterMaximum (mu L rho Dmax tau : ℝ) : ℕ :=
  getterCountBox (settings mu L rho Dmax) (tau / 8) Dmax (iterationsMax mu L rho Dmax)

def queryRadius (mu L rho Dmax : ℝ) : ℝ := uniformQueryRadius (settings mu L rho Dmax) Dmax + Dmax

def restartMaximum (Dmax tau : ℝ) : ℕ := FangqingHysteresis.halvingCount Dmax (tau / 4)

def uniformFactor (mu L rho Dmax tau Obsmax : ℝ) : ℝ :=
  OriginalMinimumWarmSolver.secondConstant *
    (ballNumber L rho Obsmax (queryRadius mu L rho Dmax) (precisionFloor mu L rho Dmax tau) *
      restartMaximum Dmax tau * getterMaximum mu L rho Dmax tau : ℕ) +
      (recoveryNumber Obsmax Dmax tau : ℕ)

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The genuine positive-curvature inner logarithmic factor has a parameter-only
uniform bound on a controlled physical radius interval. No whole-solver cost bound
is supplied as an assumption. -/
theorem positive_factor_uniform_bound
    (J : Joint E F → ℝ) (mu L rho D tau Dmax Obsmax : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (htau : 0 < tau)
    (hDlo : tau / 4 ≤ D) (hDhi : D ≤ Dmax)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hobs : observedRadius J L x uInit yin ≤ Obsmax) :
    0 ≤ uniformFactor mu L rho Dmax tau Obsmax ∧
      OriginalMinimumWarmSolver.positiveLogFactor J mu L rho D tau x uInit yin ≤
        uniformFactor mu L rho Dmax tau Obsmax := by
  have hD : 0 < D := lt_of_lt_of_le (by positivity : 0 < tau / 4) hDlo
  have hmax : 0 < Dmax := hD.trans_le hDhi
  let g := psi J L x
  let c := OriginalActualDualPositiveContraction.parameters mu L rho D
  let getter := actualGetter J L rho x uInit
  let r := FangqingHysteresis.halvingCount D (tau / 4)
  let nmax := contractionIterations c (1 / 2) Dmax
  have H : Hypotheses g c (1 / 2) D getter :=
    ⟨OriginalActualDualPositiveContraction.parameters_common mu L rho D hmu hL hrho hD,
      hD, by norm_num [c, OriginalActualDualPositiveContraction.parameters], by norm_num, rfl,
      psi_contDiff2 J L hL hC2 hLip x, psi_strongConvex J L mu hL hC2 hLip hsc x,
      psi_gradient_lipschitz J L hL hC2 hLip x,
      psi_hessian_lipschitz J L rho hL hrho.le hC2 hLip hHess x,
      actual_getter_accuracy J L rho hL hrho.le hC2 hLip hHess x uInit⟩
  have hremain : tau / 8 ≤ D / (2 : ℝ) ^ r := by
    have hh := OriginalSaddleFirstOrder.halving_remaining_lower_bound D (tau / 4) hD (by positivity)
    rw [min_eq_right hDlo] at hh
    convert! hh using 1 <;> ring
  have hbox := whole_restart_physical_box H (tau / 8) Dmax (by positivity) D hD hDhi r hremain
  have hfloor : 0 < precisionFloor mu L rho Dmax tau := hbox.1
  have hprecision : precisionFloor mu L rho Dmax tau ≤ precisionMinimum c (1 / 2) r D := hbox.2.1
  have hgetter : coefficientMaximum (radiusGetterFactor c (1 / 2)) r D ≤ getterMaximum mu L rho Dmax tau := hbox.2.2
  have hball0 : 0 ≤ uniformQueryRadius c D + D := by
    have hs : 0 ≤ stateRadius c D := hD.le.trans (stateRadius_ge_D c H.common D hD.le)
    have hobs0 : 0 ≤ observedCeiling c D := by
      change 0 ≤ 2 + (2 * L) * (D + 2 * stateRadius c D)
      positivity
    change 0 ≤ D + 2 * stateRadius c D + 2 * (observedCeiling c D + mu / 4) / mu + D
    positivity
  have hball : uniformQueryRadius c D + D ≤ queryRadius mu L rho Dmax :=
    add_le_add (uniformQueryRadius_monotone c H.common D Dmax hD.le hDhi) hDhi
  have hK := ball_budget_uniform J L rho Obsmax (uniformQueryRadius c D + D)
    (queryRadius mu L rho Dmax) (precisionMinimum c (1 / 2) r D) (precisionFloor mu L rho Dmax tau)
    hL hrho.le hball0 hball hfloor hprecision x uInit yin hobs
  have hP := recovery_budget_uniform J L Obsmax D Dmax tau hL hD.le hDhi htau x uInit yin hobs
  have hr : r ≤ restartMaximum Dmax tau := by
    have hratio := div_le_div_of_nonneg_right hDhi (show 0 ≤ tau / 4 by positivity)
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (max_le_max (le_refl (1 : ℝ)) hratio)
    exact Nat.ceil_le_ceil hlog
  have hproduct := Nat.mul_le_mul (Nat.mul_le_mul hK hr) hgetter
  have hproductR :
      ((queryBallBudget J L rho x uInit yin (uniformQueryRadius c D + D)
          (precisionMinimum c (1 / 2) r D) * r *
          coefficientMaximum (radiusGetterFactor c (1 / 2)) r D : ℕ) : ℝ) ≤
      ((ballNumber L rho Obsmax (queryRadius mu L rho Dmax) (precisionFloor mu L rho Dmax tau) *
        restartMaximum Dmax tau * getterMaximum mu L rho Dmax tau : ℕ) : ℝ) := by exact_mod_cast hproduct
  have hPR : (OriginalDualPrimalRecovery.queryBudget J L D tau x uInit yin : ℝ) ≤
      (recoveryNumber Obsmax Dmax tau : ℝ) := by exact_mod_cast hP
  have hconst := OriginalMinimumWarmSolver.second_constant_positive.le
  unfold uniformFactor OriginalMinimumWarmSolver.positiveLogFactor
  rw [if_pos hD]
  refine ⟨by positivity, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hproductR hconst
  exact add_le_add hm hPR


theorem positive_factor_uniform_all_radii
    (J : Joint E F → ℝ) (mu L rho D tau Dmax Obsmax : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (htau : 0 < tau)
    (hD : 0 ≤ D) (hDhi : D ≤ Dmax)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hobs : observedRadius J L x uInit yin ≤ Obsmax) :
    0 ≤ uniformFactor mu L rho Dmax tau Obsmax ∧
      OriginalMinimumWarmSolver.positiveLogFactor J mu L rho D tau x uInit yin ≤
        uniformFactor mu L rho Dmax tau Obsmax := by
  by_cases hlarge : tau / 4 ≤ D
  · exact positive_factor_uniform_bound J mu L rho D tau Dmax Obsmax hmu hL hrho htau
      hlarge hDhi hC2 hLip hHess hsc x uInit yin hobs
  · have hsmall : D ≤ tau / 4 := le_of_not_ge hlarge
    have hz : FangqingHysteresis.halvingCount D (tau / 4) = 0 := by
      have hq : D / (tau / 4) ≤ 1 := (div_le_one₀ (by positivity)).mpr hsmall
      simp only [FangqingHysteresis.halvingCount, max_eq_left hq, Real.logb_one, Nat.ceil_zero]
    have hP := recovery_budget_uniform J L Obsmax D Dmax tau hL hD hDhi htau x uInit yin hobs
    have hPR : (OriginalDualPrimalRecovery.queryBudget J L D tau x uInit yin : ℝ) ≤
        (recoveryNumber Obsmax Dmax tau : ℝ) := by exact_mod_cast hP
    have hnon : 0 ≤ uniformFactor mu L rho Dmax tau Obsmax := by
      unfold uniformFactor
      have hh := OriginalMinimumWarmSolver.second_constant_positive.le
      positivity
    have hrec : (recoveryNumber Obsmax Dmax tau : ℝ) ≤ uniformFactor mu L rho Dmax tau Obsmax := by
      unfold uniformFactor
      have hh := OriginalMinimumWarmSolver.second_constant_positive.le
      exact le_add_of_nonneg_left (by positivity)
    refine ⟨hnon, ?_⟩
    have he : OriginalMinimumWarmSolver.positiveLogFactor J mu L rho D tau x uInit yin =
        (OriginalDualPrimalRecovery.queryBudget J L D tau x uInit yin : ℝ) := by
      by_cases hp : 0 < D
      · simp only [OriginalMinimumWarmSolver.positiveLogFactor, if_pos hp, hz,
          Nat.mul_zero, Nat.zero_mul, Nat.cast_zero, mul_zero, zero_add]
      · simp only [OriginalMinimumWarmSolver.positiveLogFactor, if_neg hp]
    rw [he]
    exact hPR.trans hrec

end
end OriginalUniformPositiveWarmLog
end

section
-- Source component: UniformMinimumWarmLogFactor.lean

namespace OriginalUniformMinimumWarmLog

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalDualResidualQueryBound

noncomputable def uniformFactor (mu L rho Dmax tau Obsmax : ℝ) : ℝ :=
  max (OriginalUniformFirstWarmLog.uniformFactor mu L rho Dmax tau Obsmax)
    (OriginalUniformPositiveWarmLog.uniformFactor mu L rho Dmax tau Obsmax)

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 4000000

/-- A parameter-only logarithmic factor for the actual minimum warm solver on
controlled primal-residual and warm-radius data. These two analytic quantities are
proved from the original gap by the stateful outer caller. -/
theorem actual_minimum_log_factor_uniform
    (J : Joint E F → ℝ) (mu L rho D tau Dmax Obsmax : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (htau : 0 < tau)
    (hD : 0 ≤ D) (hDhi : D ≤ Dmax) (htauMax : tau ≤ Dmax)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hobs : observedRadius J L x uInit yin ≤ Obsmax) :
    0 ≤ uniformFactor mu L rho Dmax tau Obsmax ∧
      OriginalMinimumWarmSolver.logFactor J mu L rho D tau x uInit yin ≤
        uniformFactor mu L rho Dmax tau Obsmax := by
  have hobs0 : 0 ≤ observedRadius J L x uInit yin := by unfold observedRadius; positivity
  have hfirst := OriginalUniformFirstWarmLog.first_factor_uniform_bound mu L rho D tau
    (observedRadius J L x uInit yin) Dmax Obsmax hmu hL hrho.le htau hD hDhi htauMax hobs0 hobs
  have hsecond := OriginalUniformPositiveWarmLog.positive_factor_uniform_all_radii J mu L rho D tau Dmax Obsmax
    hmu hL hrho htau hD hDhi hC2 hLip hHess hsc x uInit yin hobs
  unfold uniformFactor OriginalMinimumWarmSolver.logFactor OriginalMinimumWarmSolver.secondLogFactor
  rw [if_pos hrho]
  exact ⟨hfirst.1.trans (le_max_left _ _), max_le_max hfirst.2 hsecond.2⟩

end
end OriginalUniformMinimumWarmLog
end

section
-- Source component: StatefulGDUniformMainBranches.lean

namespace OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000

def initialRadius (mu L Delta Ry : ℝ) := Ry + (L / mu) * Real.sqrt (Delta / L)

def globalWarmRadius (mu L Delta Ry eps : ℝ) :=
  max (initialRadius mu L Delta Ry)
    (callerTolerance mu L eps + 2 * Real.sqrt (L / mu) * Real.sqrt (2 * Delta / L))

def globalObservedRadius (mu L Delta Ry eps : ℝ) :=
  3 * (Real.sqrt (Delta / L) + globalWarmRadius mu L Delta Ry eps)

def globalLogFactor (mu L rho Delta Ry eps : ℝ) :=
  OriginalUniformMinimumWarmLog.uniformFactor mu L rho (globalWarmRadius mu L Delta Ry eps)
    (callerTolerance mu L eps) (globalObservedRadius mu L Delta Ry eps)

def initializationPolynomial (mu L rho Delta Ry : ℝ) :=
  1 + min (Real.sqrt (L / mu)) ((rho * initialRadius mu L Delta Ry / mu) ^ (2 / 7 : ℝ))

theorem maximum_log_le_of_all (J : Joint E F → ℝ) (mu L rho tau U : ℝ)
    (hU : 1 ≤ U) (moves : List (Move E F))
    (hall : ∀ m ∈ moves, moveLog J mu L rho tau m ≤ U) :
    maximumLog J mu L rho tau moves ≤ U := by
  induction moves with
  | nil => exact hU
  | cons m moves ih =>
      exact max_le (hall m List.mem_cons_self)
        (ih (fun a ha => hall a (List.mem_cons_of_mem _ ha)))

theorem uniform_minimum_factor_ge_one (mu L rho Dmax tau Obsmax : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hmax : 0 ≤ Dmax) (hobs : 0 ≤ Obsmax) :
    1 ≤ OriginalUniformMinimumWarmLog.uniformFactor mu L rho Dmax tau Obsmax := by
  apply le_trans ?_ (le_max_left _ _)
  have hC := OriginalUniformFirstWarmLog.primitive_cost_nonnegative mu L rho (2 * Dmax) (tau / 2)
    hmu hL hrho (by positivity) (by positivity)
  have hA : 0 ≤ Real.log (1 + 24 * Obsmax / tau) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have h145 : 0 ≤ Real.log (145 : ℝ) := Real.log_nonneg (by norm_num)
  have hT := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (le_max_left 1 (2 * Dmax / tau))
  change 1 ≤ (2 + 18 * Real.log (1 + 24 * Obsmax / tau)) +
    (36 * Real.sqrt 2 * OriginalSaddleFirstOrder.primitiveUniformCost mu L rho (2 * Dmax) (tau / 2) +
      (2 + 18 * Real.log 145)) * (1 + Real.logb 2 (max 1 (2 * Dmax / tau)))
  have hprod : 0 ≤ (36 * Real.sqrt 2 * OriginalSaddleFirstOrder.primitiveUniformCost mu L rho (2 * Dmax) (tau / 2) +
      (2 + 18 * Real.log 145)) * (1 + Real.logb 2 (max 1 (2 * Dmax / tau))) := by positivity
  linarith only [hA, hprod]

/-- Both GD upper branches are realized by one actual stateful original bundled
oracle program, with an explicit common parameter-only product of logarithmic factors.
This theorem is a main-upper sub-result for rho>0, rather than the cubic/zero-rho branch. -/
theorem actual_uniform_gradient_main_branches
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    let U := globalLogFactor mu L rho Delta Ry eps
    1 ≤ U ∧ run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.2 : ℝ) ≤ U * (initializationPolynomial mu L rho Delta Ry +
      512 * OriginalGDRateNormalization.A1 Delta L eps *
        (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ))) ∧
    (run.2 : ℝ) ≤ U * (initializationPolynomial mu L rho Delta Ry +
      256 * Real.sqrt (L / mu) * OriginalGDRateNormalization.A1 Delta L eps) := by
  let tau := callerTolerance mu L eps
  let D0 := initialRadius mu L Delta Ry
  let R := globalWarmRadius mu L Delta Ry eps
  let Obs := globalObservedRadius mu L Delta Ry eps
  let U := globalLogFactor mu L rho Delta Ry eps
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  have htau : 0 < tau := by dsimp [tau, callerTolerance]; positivity
  have hRtau : tau ≤ R := by
    apply le_trans ?_ (le_max_right _ _)
    exact le_add_of_nonneg_right (by positivity)
  have hR0 : D0 ≤ R := le_max_left _ _
  have hR : 0 < R := htau.trans_le hRtau
  have hObs : 0 ≤ Obs := by dsimp [Obs, globalObservedRadius]; positivity
  have hU : 1 ≤ U := uniform_minimum_factor_ge_one mu L rho R tau Obs hmu hL hrho.le htau hR.le hObs
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hbase := actual_gradient_caller_from_original_inputs J mu L rho Delta Ry eps hmu hLmu hrho.le heps
    hC2 hLip hHess hsc hbelow start yin hgap hdual
  change run.1.success = true ∧ _ at hbase
  rcases hbase with ⟨htrue, hstationary, hcount, hsquares, hcost, htrace⟩
  have hfront := actual_gradient_frontier_with_explicit_logs J mu L rho Delta Ry eps hmu hLmu hrho.le heps
    hC2 hLip hHess hsc hbelow start yin hgap hdual
  change run.1.success = true ∧ _ at hfront
  have hrad : ∀ m ∈ run.1.moves, m.radius ≤ R := by
    intro m hm
    exact ((hfront.2.2.2 m hm)).trans (le_max_right _ _)
  have hlogs : ∀ m ∈ run.1.moves, moveLog J mu L rho tau m ≤ U := by
    intro m hm
    obtain ⟨hlegal, _, hobs⟩ := htrace m hm
    have hD : 0 ≤ m.radius := (norm_nonneg _).trans hlegal
    have hobsR : OriginalDualResidualQueryBound.observedRadius J L m.next m.next m.warm ≤ Obs := by
      exact hobs.trans (by dsimp [Obs, globalObservedRadius]; linarith only [hrad m hm])
    exact (OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform J mu L rho m.radius tau R Obs
      hmu hL hrho htau hD (hrad m hm) hRtau hC2 hLip hHess hsc m.next m.next m.warm hobsR).2
  have hM := maximum_log_le_of_all J mu L rho tau U hU run.1.moves hlogs
  have hinit := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hD0 : 0 ≤ D0 := (norm_nonneg _).trans hinit
  have hinitObs := OriginalInitialSaddleRadius.actual_initial_primal_residual J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hinitObsR : OriginalDualResidualQueryBound.observedRadius J L start start yin ≤ Obs := by
    have hh : 3 * (Real.sqrt (Delta / L) + D0) ≤ Obs := by
      change 3 * (Real.sqrt (Delta / L) + D0) ≤ 3 * (Real.sqrt (Delta / L) + R)
      linarith only [hR0]
    exact hinitObs.trans hh
  have hinitLog := (OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform J mu L rho D0 tau R Obs
    hmu hL hrho htau hD0 hR0 hRtau hC2 hLip hHess hsc start start yin hinitObsR).2
  have hI0 : 0 ≤ initializationPolynomial mu L rho Delta Ry := by
    dsimp [initializationPolynomial]
    have hp : 0 ≤ rho * initialRadius mu L Delta Ry / mu := by change 0 ≤ rho * D0 / mu; positivity
    positivity
  have hinitCost : initialCost J mu L rho D0 tau start yin ≤ initializationPolynomial mu L rho Delta Ry * U :=
    mul_le_mul_of_nonneg_left hinitLog hI0
  have hDelta : 0 ≤ Delta := by
    have hi := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap, hi]
  have ha : 0 ≤ OriginalGDRateNormalization.A1 Delta L eps := by unfold OriginalGDRateNormalization.A1; positivity
  have hr : 0 ≤ OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ) := by
    unfold OriginalGDRateNormalization.ratio
    positivity
  have hmiddle := hfront.2.2.1
  change (run.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin +
    512 * maximumLog J mu L rho tau run.1.moves * OriginalGDRateNormalization.A1 Delta L eps *
      (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ)) at hmiddle
  change (run.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin + costSum J mu L rho tau run.1.moves at hcost
  have hMscale := mul_le_mul_of_nonneg_right hM
    (show 0 ≤ 512 * OriginalGDRateNormalization.A1 Delta L eps * (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ)) by positivity)
  have hmiddleBound : (run.2 : ℝ) ≤ U * (initializationPolynomial mu L rho Delta Ry +
      512 * OriginalGDRateNormalization.A1 Delta L eps * (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ))) := by
    nlinarith only [hmiddle, hMscale, hinitCost]
  have hcap := actual_cost_sum_first_order_cap J mu L rho tau hmu hL hrho.le run.1.moves
    (fun m hm => (norm_nonneg _).trans (htrace m hm).1)
  have hsqrt : 1 ≤ Real.sqrt (L / mu) := by
    have hratio : 1 ≤ L / mu := (le_div_iff₀ hmu).mpr (by simpa using hLmu)
    nlinarith [Real.sq_sqrt (show 0 ≤ L / mu by positivity), Real.sqrt_nonneg (L / mu)]
  have hcountA : (run.1.moves.length : ℝ) ≤ 128 * OriginalGDRateNormalization.A1 Delta L eps := by
    convert! hcount using 1 <;> unfold OriginalGDRateNormalization.A1 <;> ring
  have hscalar : (run.1.moves.length : ℝ) * (1 + Real.sqrt (L / mu)) ≤
      256 * Real.sqrt (L / mu) * OriginalGDRateNormalization.A1 Delta L eps := by
    have hn := mul_le_mul_of_nonneg_right hcountA (show 0 ≤ 1 + Real.sqrt (L / mu) by positivity)
    have hp := mul_nonneg ha (sub_nonneg.mpr hsqrt)
    nlinarith only [hn, hp]
  have hcap2 : costSum J mu L rho tau run.1.moves ≤
      U * (256 * Real.sqrt (L / mu) * OriginalGDRateNormalization.A1 Delta L eps) := hcap.trans (by
    have hN0 : 0 ≤ (run.1.moves.length : ℝ) * (1 + Real.sqrt (L / mu)) := by positivity
    have hMa := mul_le_mul_of_nonneg_right hM hN0
    have hUb := mul_le_mul_of_nonneg_left hscalar hU0
    nlinarith only [hMa, hUb])
  refine ⟨hU, htrue, hstationary, hmiddleBound, ?_⟩
  nlinarith only [hcost, hinitCost, hcap2]

end
end OriginalStatefulEnvelopeGD
end

section
-- Source component: OuterCubicModel.lean

namespace OriginalOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section

def model (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) : ℝ :=
  inner ℝ v s + (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3

theorem model_hasGradientAt (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) :
    HasGradientAt (model v H M) (v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s) s := by
  have heq : CertifiedATS.model v H M 0 = model v H M := by
    funext d
    simp only [CertifiedATS.model, model, mul_zero, div_zero, zero_mul, add_zero]
  have hh := CertifiedATS.model_hasGradientAt v H M 0 s
  rw [heq] at hh
  simpa only [inv_zero, zero_smul, add_zero] using hh

theorem model_lower_bound (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) :
    -‖v‖ * ‖s‖ - ‖H‖ / 2 * ‖s‖ ^ 2 + M / 6 * ‖s‖ ^ 3 ≤ model v H M s := by
  have hv := real_inner_le_norm (-v) s
  rw [inner_neg_left, norm_neg] at hv
  have hH := real_inner_le_norm (-(H s)) s
  rw [inner_neg_left, norm_neg] at hH
  have hn := mul_le_mul_of_nonneg_right (H.le_opNorm s) (norm_nonneg s)
  unfold model
  nlinarith only [hv, hH, hn]

def modelRadius (v : E) (H : E →L[ℝ] E) (M : ℝ) : ℝ :=
  1 + 12 * (‖v‖ + ‖H‖) / M

theorem model_nonnegative_outside (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M)
    (s : E) (hout : modelRadius v H M ≤ ‖s‖) : 0 ≤ model v H M s := by
  have hR : 1 ≤ modelRadius v H M := by
    have hh : 0 ≤ 12 * (‖v‖ + ‖H‖) / M := by positivity
    unfold modelRadius
    linarith only [hh]
  have hr : 1 ≤ ‖s‖ := hR.trans hout
  have hMr : 12 * (‖v‖ + ‖H‖) ≤ M * ‖s‖ := by
    have hh := mul_le_mul_of_nonneg_left hout hM.le
    dsimp only [modelRadius] at hh
    have hid : M * (1 + 12 * (‖v‖ + ‖H‖) / M) = M + 12 * (‖v‖ + ‖H‖) := by
      field_simp <;> ring
    rw [hid] at hh
    linarith only [hh, hM]
  have hmul := mul_le_mul_of_nonneg_right hMr (sq_nonneg ‖s‖)
  have hvr : ‖v‖ * ‖s‖ ≤ ‖v‖ * ‖s‖ ^ 2 := by
    have hh : ‖s‖ ≤ ‖s‖ ^ 2 := by nlinarith only [hr]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg v)
  have hH0 := mul_nonneg (norm_nonneg H) (sq_nonneg ‖s‖)
  have hv0 := mul_nonneg (norm_nonneg v) (sq_nonneg ‖s‖)
  have hlower := model_lower_bound v H M s
  nlinarith only [hmul, hvr, hH0, hv0, hlower]

theorem exists_model_minimizer (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    ∃ s : E, ∀ t : E, model v H M s ≤ model v H M t := by
  let R := modelRadius v H M
  have hR : 0 < R := by dsimp only [R, modelRadius]; positivity
  have hzero : (0 : E) ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_self] using hR.le
  have hcont : Continuous (model v H M) :=
    (show Differentiable ℝ (model v H M) from fun s => (model_hasGradientAt v H M s).differentiableAt).continuous
  obtain ⟨s, hs, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn ⟨0, hzero⟩ hcont.continuousOn
  refine ⟨s, ?_⟩
  intro t
  by_cases ht : t ∈ Metric.closedBall 0 R
  · exact hmin ht
  · have hout : modelRadius v H M ≤ ‖t‖ := by
      have hh : R < ‖t‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using ht
      exact hh.le
    have hs0 : model v H M s ≤ model v H M 0 := hmin hzero
    have h0 : model v H M 0 = 0 := by simp only [model, inner_zero_right, norm_zero]; ring
    rw [h0] at hs0
    exact hs0.trans (model_nonnegative_outside v H M hM t hout)

def minimizer (v : E) (H : E →L[ℝ] E) (M : ℝ) : E :=
  Classical.epsilon (fun s : E => ∀ t : E, model v H M s ≤ model v H M t)

theorem minimizer_is_actual (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    ∀ t : E, model v H M (minimizer v H M) ≤ model v H M t :=
  Classical.epsilon_spec (exists_model_minimizer v H M hM)

theorem minimizer_equation_and_decrease (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    let s := minimizer v H M
    v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s = 0 ∧
      model v H M s ≤ -(M / 12) * ‖s‖ ^ 3 := by
  dsimp only
  let s := minimizer v H M
  have hmin := minimizer_is_actual v H M hM
  have hloc : IsLocalMin (model v H M) s := Filter.Eventually.of_forall hmin
  have hg := hloc.hasFDerivAt_eq_zero (model_hasGradientAt v H M s).hasFDerivAt
  have heq : v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s = 0 := by
    have hh := congrArg (fun D : E →L[ℝ] ℝ => D (v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s)) hg
    simpa only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.zero_apply,
      real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] using hh
  have hinner := congrArg (fun w : E => inner ℝ w s) heq
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
    real_inner_self_eq_norm_sq] at hinner
  have hsym : inner ℝ (CertifiedATS.sympart H s) s = inner ℝ (H s) s := by
    simp only [CertifiedATS.sympart, smul_apply, add_apply, real_inner_smul_left,
      inner_add_left, ContinuousLinearMap.adjoint_inner_left, real_inner_comm s (H s)]
    ring
  rw [hsym] at hinner
  have hmirror := hmin (-s)
  have hneg : model v H M (-s) = -inner ℝ v s + (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3 := by
    simp only [model, inner_neg_right, map_neg, inner_neg_left, neg_neg, norm_neg]
  rw [hneg] at hmirror
  dsimp only [model] at hmirror ⊢
  refine ⟨heq, ?_⟩
  nlinarith only [hinner, hmirror]

end
end OriginalOuterCubic
end

section
-- Source component: OuterCubicTaylor.lean

namespace OriginalOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem cubic_taylor_upper
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (z s : E) :
    f (z + s) ≤ f z + inner ℝ (gradient f z) s +
      (1 / 2 : ℝ) * inner ℝ (fderiv ℝ (gradient f) z s) s + M / 6 * ‖s‖ ^ 3 := by
  let H := fderiv ℝ (gradient f) z
  let phi : ℝ → ℝ := fun t => f (z + t • s) - f z - t * inner ℝ (gradient f z) s -
    t ^ 2 / 2 * inner ℝ (H s) s - (M / 6 * ‖s‖ ^ 3) * t ^ 3
  let phi' : ℝ → ℝ := fun t => inner ℝ (gradient f (z + t • s)) s -
    inner ℝ (gradient f z) s - t * inner ℝ (H s) s - (M / 2 * ‖s‖ ^ 3) * t ^ 2
  have hdiff : Differentiable ℝ f := hC2.differentiable (by norm_num)
  have hderiv : ∀ t : ℝ, HasDerivAt phi (phi' t) t := by
    intro t
    have hcurve : HasDerivAt (fun t : ℝ => z + t • s) s t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const s).const_add z
    have hgcurve : HasDerivAt (fun t : ℝ => f (z + t • s))
        (inner ℝ (gradient f (z + t • s)) s) t := by
      simpa only [Function.comp_def, inner_gradient_left] using
        ((hdiff (z + t • s)).hasFDerivAt.comp_hasDerivAt t hcurve)
    have hlin := (hasDerivAt_id t).mul_const (inner ℝ (gradient f z) s)
    have hquad := (((hasDerivAt_id t).pow 2).div_const 2).mul_const (inner ℝ (H s) s)
    have hcubic := ((hasDerivAt_id t).pow 3).const_mul (M / 6 * ‖s‖ ^ 3)
    simp only [id_eq, Pi.pow_apply] at hlin hquad hcubic
    have hh := (((hgcurve.sub_const (f z)).sub hlin).sub hquad).sub hcubic
    convert! hh using 1 <;> dsimp only [phi, phi'] <;> ring
  have hnonpos : phi' ≤ 0 := by
    intro t
    let R := gradient f (z + t • s) - gradient f z - H (t • s)
    have hR := RobustAHPE.gradient_taylor_remainder f hC2 M hM hH z (t • s)
    change ‖R‖ ≤ M / 2 * ‖t • s‖ ^ 2 at hR
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hR
    have hinner := real_inner_le_norm R s
    have hm := mul_le_mul_of_nonneg_right hR (norm_nonneg s)
    have he : inner ℝ R s = inner ℝ (gradient f (z + t • s)) s -
        inner ℝ (gradient f z) s - t * inner ℝ (H s) s := by
      simp only [R, inner_sub_left, map_smul, real_inner_smul_left]
    rw [he] at hinner
    change inner ℝ (gradient f (z + t • s)) s - inner ℝ (gradient f z) s -
      t * inner ℝ (H s) s - (M / 2 * ‖s‖ ^ 3) * t ^ 2 ≤ 0
    nlinarith only [hinner, hm]
  have hanti := antitone_of_hasDerivAt_nonpos hderiv hnonpos
  have hh := hanti (by norm_num : (0 : ℝ) ≤ 1)
  dsimp only [phi] at hh
  simp only [zero_smul, add_zero, one_smul, zero_mul, one_mul, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), one_pow, sub_self, sub_zero, zero_div] at hh
  change f (z + s) ≤ _
  nlinarith only [hh]

end OriginalOuterCubic
end

section
-- Source component: OuterCubicInexactStep.lean

namespace OriginalOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem inexact_step_bounds
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (z v : E) (Ht : E →L[ℝ] E) (deltaG deltaH : ℝ)
    (hG : ‖v - gradient f z‖ ≤ deltaG)
    (hHt : ‖Ht - fderiv ℝ (gradient f) z‖ ≤ deltaH) :
    let s := minimizer v Ht (2 * M)
    f (z + s) - f z ≤ -(M / 3) * ‖s‖ ^ 3 + deltaG * ‖s‖ + deltaH / 2 * ‖s‖ ^ 2 ∧
      ‖gradient f (z + s)‖ ≤ (3 * M / 2) * ‖s‖ ^ 2 + deltaH * ‖s‖ + deltaG := by
  dsimp only
  let s := minimizer v Ht (2 * M)
  let H := fderiv ℝ (gradient f) z
  have hm := minimizer_equation_and_decrease v Ht (2 * M) (by positivity)
  change v + CertifiedATS.sympart Ht s + (2 * M / 2 * ‖s‖) • s = 0 ∧
    model v Ht (2 * M) s ≤ -(2 * M / 12) * ‖s‖ ^ 3 at hm
  have htaylor := cubic_taylor_upper f hC2 M hM hH z s
  have hg : ‖gradient f z - v‖ ≤ deltaG := by simpa only [norm_sub_rev] using hG
  have hgnorm := real_inner_le_norm (gradient f z - v) s
  have hgmul := mul_le_mul_of_nonneg_right hg (norm_nonneg s)
  simp only [inner_sub_left] at hgnorm
  have hdiff : ‖H - Ht‖ ≤ deltaH := by simpa only [norm_sub_rev] using hHt
  have hnorm := ((H - Ht).le_opNorm s).trans (mul_le_mul_of_nonneg_right hdiff (norm_nonneg s))
  have hinner := real_inner_le_norm ((H - Ht) s) s
  have hhmul := mul_le_mul_of_nonneg_right hnorm (norm_nonneg s)
  simp only [sub_apply, inner_sub_left] at hinner
  have hmodel := hm.2
  dsimp only [model] at hmodel
  simp only [sub_apply] at hhmul
  change f (z + s) ≤ f z + inner ℝ (gradient f z) s +
    (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3 at htaylor
  refine ⟨?_, ?_⟩
  · change f (z + s) - f z ≤ -(M / 3) * ‖s‖ ^ 3 + deltaG * ‖s‖ + deltaH / 2 * ‖s‖ ^ 2
    nlinarith only [htaylor, hmodel, hgnorm, hgmul, hinner, hhmul]
  · change ‖gradient f (z + s)‖ ≤ (3 * M / 2) * ‖s‖ ^ 2 + deltaH * ‖s‖ + deltaG
    have hself := CertifiedATS.gradient_derivative_selfadjoint f hC2 z
    have hsym : ‖H - CertifiedATS.sympart Ht‖ ≤ deltaH := by
      rw [norm_sub_rev]
      exact (CertifiedATS.sympart_error_bound Ht H hself).trans hHt
    have hsymnorm := ((H - CertifiedATS.sympart Ht).le_opNorm s).trans
      (mul_le_mul_of_nonneg_right hsym (norm_nonneg s))
    let R := gradient f (z + s) - gradient f z - H s
    have hR := RobustAHPE.gradient_taylor_remainder f hC2 M hM hH z s
    change ‖R‖ ≤ M / 2 * ‖s‖ ^ 2 at hR
    have hzero : v + CertifiedATS.sympart Ht s + (M * ‖s‖) • s = 0 := by
      convert! hm.1 using 1 <;> ring
    have he : gradient f (z + s) = R + (gradient f z - v) + (H - CertifiedATS.sympart Ht) s - (M * ‖s‖) • s := by
      calc
        _ = gradient f (z + s) - (v + CertifiedATS.sympart Ht s + (M * ‖s‖) • s) := by rw [hzero, sub_zero]
        _ = _ := by simp only [R, sub_apply]; module
    have hn1 := norm_sub_le (R + (gradient f z - v) + (H - CertifiedATS.sympart Ht) s) ((M * ‖s‖) • s)
    have hn2 := norm_add_le (R + (gradient f z - v)) ((H - CertifiedATS.sympart Ht) s)
    have hn3 := norm_add_le R (gradient f z - v)
    have hsmul : ‖(M * ‖s‖) • s‖ = M * ‖s‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM.le (norm_nonneg _))]
      ring
    rw [← he, hsmul] at hn1
    nlinarith only [hn1, hn2, hn3, hR, hg, hsymnorm]

theorem nonterminal_scalar_decrease (M eps r q Gnew Fchange : ℝ)
    (hM : 0 < M) (heps : 0 < eps) (hr : 0 ≤ r) (hq : 0 ≤ q) (hqsq : q ^ 2 = M * eps)
    (hnew : eps / 3 < Gnew)
    (hgrad : Gnew ≤ (3 * M / 2) * r ^ 2 + (q / 1024) * r + eps / 1024)
    (hchange : Fchange ≤ -(M / 3) * r ^ 3 + (eps / 1024) * r + (q / 1024) / 2 * r ^ 2) :
    eps / 16 ≤ M * r ^ 2 ∧ Fchange ≤ -(M / 4) * r ^ 3 := by
  have hyoung : 2 * r * q ≤ M * r ^ 2 + eps := by
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith only [sq_nonneg (M * r - q), hqsq]
  have hradius : eps / 16 ≤ M * r ^ 2 := by
    nlinarith only [hgrad, hyoung, hnew, heps]
  have hMmul := mul_le_mul_of_nonneg_left hradius hM.le
  have hqr : q ≤ 4 * M * r := by
    nlinarith only [hMmul, hqsq, hq, mul_nonneg hM.le hr]
  have hepsr := mul_le_mul_of_nonneg_right hradius hr
  have hqrr := mul_le_mul_of_nonneg_right hqr (sq_nonneg r)
  refine ⟨hradius, ?_⟩
  nlinarith only [hchange, hepsr, hqrr, mul_nonneg hM.le (pow_nonneg hr 3)]

end OriginalOuterCubic
end

section
-- Source component: OuterCubicSeparatedTolerances.lean

open OriginalOuterCubic



namespace OriginalOuterCubicSeparateErrors

open OriginalBetaATSTrial (Answer GetterProgram execute)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section

def tolerance (M eps : ℝ) : ℝ := min (eps / 1024) (Real.sqrt (M * eps) / 1024)
def stepRadius (M eps : ℝ) : ℝ := Real.sqrt (eps / (16 * M))
def stepCharge (M eps : ℝ) : ℝ := M / 4 * stepRadius M eps ^ 3

structure CubicOutput (E : Type*) where
  point : E
  success : Bool
  moves : ℕ
  charged : ℕ
  cubicSteps : ℝ

def appendCharged (s : E) (out : CubicOutput E) : CubicOutput E :=
  ⟨out.point, out.success, out.moves + 1, out.charged + 1, ‖s‖ ^ 3 + out.cubicSteps⟩

def loop (M eps : ℝ) : ℕ → E → Answer E → GetterProgram (E × ℝ) (Answer E) (CubicOutput E)
  | 0, x, _ => .pure ⟨x, false, 0, 0, 0⟩
  | n + 1, x, a =>
      if ‖a.grad‖ ≤ eps / 2 then .pure ⟨x, true, 0, 0, 0⟩
      else
        let s := minimizer a.grad a.hess (2 * M)
        let y := x + s
        .ask (y, tolerance M eps) (fun ay =>
          if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
          else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))

def program (M eps : ℝ) (n : ℕ) (start : E) : GetterProgram (E × ℝ) (Answer E) (CubicOutput E) :=
  .ask (start, tolerance M eps) (fun a => loop M eps n start a)

theorem radius_properties (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    0 < tolerance M eps ∧ 0 < stepRadius M eps ∧
      M * stepRadius M eps ^ 2 = eps / 16 ∧ 0 < stepCharge M eps := by
  have ht : 0 < tolerance M eps := by unfold tolerance; positivity
  have hr : 0 < stepRadius M eps := by unfold stepRadius; positivity
  have hs := Real.sq_sqrt (by positivity : 0 ≤ eps / (16 * M))
  have hid : M * stepRadius M eps ^ 2 = eps / 16 := by
    unfold stepRadius
    rw [hs]
    field_simp
  exact ⟨ht, hr, hid, by unfold stepCharge; positivity⟩

def Accurate (f : E → ℝ) (M eps : ℝ) (x : E) (a : Answer E) : Prop :=
  ‖a.grad - gradient f x‖ ≤ eps / 1024 ∧
    ‖a.hess - fderiv ℝ (gradient f) x‖ ≤ Real.sqrt (M * eps) / 1024

theorem accurate_stop (f : E → ℝ) (M eps : ℝ) (heps : 0 < eps) (x : E) (a : Answer E)
    (ha : Accurate f M eps x a) (hstop : ‖a.grad‖ ≤ eps / 2) : ‖gradient f x‖ ≤ eps := by
  have he : ‖a.grad - gradient f x‖ ≤ eps / 1024 := ha.1
  have ht := norm_sub_le a.grad (a.grad - gradient f x)
  have hid : a.grad - (a.grad - gradient f x) = gradient f x := by abel
  rw [hid] at ht
  linarith only [ht, he, hstop, heps]

theorem accurate_nonterminal (f : E → ℝ) (M eps : ℝ) (heps : 0 < eps) (x : E) (a : Answer E)
    (ha : Accurate f M eps x a) (hstop : ¬ ‖a.grad‖ ≤ eps / 2) : eps / 3 < ‖gradient f x‖ := by
  have he : ‖a.grad - gradient f x‖ ≤ eps / 1024 := ha.1
  have ht := norm_add_le (a.grad - gradient f x) (gradient f x)
  have hid : (a.grad - gradient f x) + gradient f x = a.grad := by abel
  rw [hid] at ht
  linarith only [ht, he, lt_of_not_ge hstop, heps]

theorem large_radius_scalar_decrease (M eps r q Fchange : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hqsq : q ^ 2 = M * eps)
    (hradius : eps / 16 ≤ M * r ^ 2)
    (hchange : Fchange ≤ -(M / 3) * r ^ 3 + (eps / 1024) * r + (q / 1024) / 2 * r ^ 2) :
    Fchange ≤ -(M / 4) * r ^ 3 := by
  have hMmul := mul_le_mul_of_nonneg_left hradius hM.le
  have hqr : q ≤ 4 * M * r := by
    nlinarith only [hMmul, hqsq, mul_nonneg hM.le hr]
  have hepsr := mul_le_mul_of_nonneg_right hradius hr
  have hqrr := mul_le_mul_of_nonneg_right hqr (sq_nonneg r)
  nlinarith only [hchange, hepsr, hqrr, mul_nonneg hM.le (pow_nonneg hr 3)]

theorem actual_step_radius_and_descent
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (x : E) (a : Answer E) (ha : Accurate f M eps x a) :
    let s := minimizer a.grad a.hess (2 * M)
    (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ f x - f (x + s)) ∧
    (∀ ay : Answer E, Accurate f M eps (x + s) ay → ¬ ‖ay.grad‖ ≤ eps / 2 →
      stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ f x - f (x + s)) := by
  dsimp only
  let s := minimizer a.grad a.hess (2 * M)
  have hp := radius_properties M eps hM heps
  have hs := inexact_step_bounds f hC2 M hM hH x a.grad a.hess (eps / 1024) (Real.sqrt (M * eps) / 1024)
    (ha.1) ha.2
  have hqsq := Real.sq_sqrt (by positivity : 0 ≤ M * eps)
  have hq : 0 ≤ Real.sqrt (M * eps) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · intro hr
    have hsq := (sq_le_sq₀ hp.2.1.le (norm_nonneg s)).mpr hr
    have hm := mul_le_mul_of_nonneg_left hsq hM.le
    have hradius : eps / 16 ≤ M * ‖s‖ ^ 2 := by linarith only [hm, hp.2.2.1]
    have hd := large_radius_scalar_decrease M eps ‖s‖ (Real.sqrt (M * eps)) (f (x + s) - f x)
      hM (norm_nonneg _) hqsq hradius hs.1
    linarith only [hd]
  · intro ay hay haway
    have hlarge := accurate_nonterminal f M eps heps (x + s) ay hay haway
    have hscalar := nonterminal_scalar_decrease M eps ‖s‖ (Real.sqrt (M * eps))
      ‖gradient f (x + s)‖ (f (x + s) - f x) hM heps (norm_nonneg _) hq hqsq hlarge hs.2 hs.1
    have hsq : stepRadius M eps ^ 2 ≤ ‖s‖ ^ 2 := by
      apply (mul_le_mul_iff_right₀ hM).mp
      linarith only [hp.2.2.1, hscalar.1]
    exact ⟨(sq_le_sq₀ hp.2.1.le (norm_nonneg s)).mp hsq, by linarith only [hscalar.2]⟩

end
end OriginalOuterCubicSeparateErrors




namespace OriginalOuterCubicSeparateErrors

open OriginalBetaATSTrial (Answer GetterProgram execute)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

def LoopSpec (f : E → ℝ) (M eps lower : ℝ) (n : ℕ) (x : E) (run : CubicOutput E × ℕ) : Prop :=
  stepCharge M eps * (run.1.charged : ℝ) ≤ f x - lower ∧
  M / 4 * run.1.cubicSteps ≤ f x - lower + stepCharge M eps ∧
  run.1.moves ≤ run.1.charged + 1 ∧
  (run.1.success = true → ‖gradient f run.1.point‖ ≤ eps) ∧
  (run.1.success = false → run.1.charged = n) ∧ run.2 = run.1.moves

theorem actual_cubic_loop_spec
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (n : ℕ) (x : E) (a : Answer E) (ha : Accurate f M eps x a) :
    LoopSpec f M eps lower n x (execute getter (loop M eps n x a)) := by
  have hp := radius_properties M eps hM heps
  have hradius0 := hp.2.1.le
  induction n generalizing x a with
  | zero =>
      simp only [loop, execute, LoopSpec]
      refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
        by simpa only [mul_zero] using add_nonneg (sub_nonneg.mpr (hbelow x)) hp.2.2.2.le,
        by omega, ?_, fun _ => by trivial, by trivial⟩
      intro hf
      cases hf
  | succ n ih =>
      by_cases hstop : ‖a.grad‖ ≤ eps / 2
      · rw [loop, if_pos hstop]
        simp only [execute, LoopSpec]
        refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
          by simpa only [mul_zero] using add_nonneg (sub_nonneg.mpr (hbelow x)) hp.2.2.2.le,
          by omega, fun _ => accurate_stop f M eps heps x a ha hstop, ?_, by trivial⟩
        intro hf
        cases hf
      · let s := minimizer a.grad a.hess (2 * M)
        let y := x + s
        let ay := getter (y, tolerance M eps)
        have hay : Accurate f M eps y ay := hvalid y
        have hstep := actual_step_radius_and_descent f hC2 M eps hM heps hH x a ha
        change (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ f x - f y) ∧
          (∀ ay : Answer E, Accurate f M eps y ay → ¬ ‖ay.grad‖ ≤ eps / 2 →
            stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ f x - f y) at hstep
        rw [loop, if_neg hstop]
        change LoopSpec f M eps lower (n + 1) x
          (execute getter (.ask (y, tolerance M eps) (fun ay =>
            if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))))
        simp only [execute]
        change LoopSpec f M eps lower (n + 1) x
          ((execute getter (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))).1,
           (execute getter (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))).2 + 1)
        by_cases hnextstop : ‖ay.grad‖ ≤ eps / 2
        · have hbudget : M / 4 * ‖s‖ ^ 3 ≤ f x - lower + stepCharge M eps := by
            by_cases hr : stepRadius M eps ≤ ‖s‖
            · have hd := hstep.1 hr
              linarith only [hd, hbelow y, hp.2.2.2]
            · have hrle : ‖s‖ ≤ stepRadius M eps := (lt_of_not_ge hr).le
              have hcube : ‖s‖ ^ 3 ≤ stepRadius M eps ^ 3 := by gcongr
              have hh := mul_le_mul_of_nonneg_left hcube (by positivity : 0 ≤ M / 4)
              change M / 4 * ‖s‖ ^ 3 ≤ f x - lower + M / 4 * stepRadius M eps ^ 3
              linarith only [hh, hbelow x]
          simp only [if_pos hnextstop, execute, LoopSpec]
          refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
            hbudget, by omega, fun _ => accurate_stop f M eps heps y ay hay hnextstop, ?_, by trivial⟩
          intro hf
          cases hf
        · have hd := hstep.2 ay hay hnextstop
          have hradius := hd.1
          have hcube : stepRadius M eps ^ 3 ≤ ‖s‖ ^ 3 := by gcongr
          have hcharge : stepCharge M eps ≤ M / 4 * ‖s‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hcube (by positivity)
          have hi := ih y ay hay
          simp only [LoopSpec] at hi
          simp only [if_neg hnextstop, FangqingGetterComposition.execute_map,
            LoopSpec, appendCharged, Nat.cast_add, Nat.cast_one]
          refine ⟨by nlinarith only [hi.1, hd.2, hcharge],
            by nlinarith only [hi.2.1, hd.2], ?_, hi.2.2.2.1, ?_, ?_⟩
          · have hh := hi.2.2.1
            omega
          · intro hf
            have hh := hi.2.2.2.2.1 hf
            omega
          · have hh := hi.2.2.2.2.2
            omega

noncomputable def fuel (Delta M eps : ℝ) : ℕ := Nat.ceil (Delta / stepCharge M eps) + 1

theorem actual_finite_cubic_termination
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower Delta : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (start : E) (hgap : f start - lower ≤ Delta) :
    let run := execute getter (program M eps (fuel Delta M eps) start)
    run.1.success = true ∧ ‖gradient f run.1.point‖ ≤ eps ∧
      (run.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
      run.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧
      (run.2 : ℝ) ≤ 2 + Delta / stepCharge M eps := by
  dsimp only
  let a := getter (start, tolerance M eps)
  let rest := execute getter (loop M eps (fuel Delta M eps) start a)
  have hp := radius_properties M eps hM heps
  have hs := actual_cubic_loop_spec f hC2 M eps lower hM heps hH hbelow getter hvalid
    (fuel Delta M eps) start a (hvalid start)
  change LoopSpec f M eps lower (fuel Delta M eps) start rest at hs
  dsimp only [LoopSpec] at hs
  have hc : (rest.1.charged : ℝ) ≤ Delta / stepCharge M eps :=
    (le_div_iff₀ hp.2.2.2).mpr (by nlinarith only [hs.1, hgap])
  have hsuccess : rest.1.success = true := by
    cases hb : rest.1.success with
    | true => rfl
    | false =>
        have hn := hs.2.2.2.2.1 hb
        rw [hn] at hc
        have hceil : Delta / stepCharge M eps ≤ (Nat.ceil (Delta / stepCharge M eps) : ℝ) := Nat.le_ceil _
        unfold fuel at hc
        push_cast at hc
        linarith only [hc, hceil]
  have hmoves : (rest.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps := by
    have hh : (rest.1.moves : ℝ) ≤ (rest.1.charged : ℝ) + 1 := by exact_mod_cast hs.2.2.1
    linarith only [hh, hc]
  have hcubic : rest.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < M / 4)).mp
    have hid : M / 4 * (4 * Delta / M + stepRadius M eps ^ 3) = Delta + stepCharge M eps := by
      unfold stepCharge
      field_simp <;> ring
    rw [hid]
    nlinarith only [hs.2.1, hgap]
  change rest.1.success = true ∧ ‖gradient f rest.1.point‖ ≤ eps ∧
    (rest.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
    rest.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧ ((rest.2 + 1 : ℕ) : ℝ) ≤ _
  refine ⟨hsuccess, hs.2.2.2.1 hsuccess, hmoves, hcubic, ?_⟩
  rw [hs.2.2.2.2.2]
  push_cast
  linarith only [hmoves]

end OriginalOuterCubicSeparateErrors




namespace OriginalOuterCubicSeparateErrors

theorem radius_and_charge_identities (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    stepRadius M eps ^ 3 = eps ^ (3 / 2 : ℝ) / (64 * M * Real.sqrt M) ∧
      stepCharge M eps = eps ^ (3 / 2 : ℝ) / (256 * Real.sqrt M) := by
  have hr : stepRadius M eps = Real.sqrt eps / (4 * Real.sqrt M) := by
    unfold stepRadius
    rw [Real.sqrt_div heps.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have he3 : Real.sqrt eps ^ 3 = eps * Real.sqrt eps := by rw [pow_succ, Real.sq_sqrt heps.le]
  have hM3 : Real.sqrt M ^ 3 = M * Real.sqrt M := by rw [pow_succ, Real.sq_sqrt hM.le]
  have hepow : eps ^ (3 / 2 : ℝ) = eps * Real.sqrt eps := by
    calc
      _ = eps ^ (1 + 1 / 2 : ℝ) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add heps, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hcube : stepRadius M eps ^ 3 = eps ^ (3 / 2 : ℝ) / (64 * M * Real.sqrt M) := by
    rw [hr, div_pow, mul_pow, he3, hM3, hepow]
    norm_num
    ring
  refine ⟨hcube, ?_⟩
  unfold stepCharge
  rw [hcube]
  field_simp [ne_of_gt hM, ne_of_gt (Real.sqrt_pos.mpr hM)]
  <;> ring

theorem reciprocal_charge_identity (Delta M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    Delta / stepCharge M eps = 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) := by
  rw [(radius_and_charge_identities M eps hM heps).2, div_div_eq_mul_div]
  ring

noncomputable def epsilonThreshold (Delta M : ℝ) : ℝ := (Delta * Real.sqrt M) ^ (2 / 3 : ℝ)

theorem epsilon_threshold_properties (Delta M eps : ℝ) (hDelta : 0 < Delta) (hM : 0 < M)
    (heps : 0 < eps) (hsmall : eps ≤ epsilonThreshold Delta M) :
    0 < epsilonThreshold Delta M ∧ eps ^ (3 / 2 : ℝ) ≤ Delta * Real.sqrt M := by
  have hx : 0 < Delta * Real.sqrt M := by positivity
  have hpos : 0 < epsilonThreshold Delta M := by unfold epsilonThreshold; positivity
  have hp := Real.rpow_le_rpow heps.le hsmall (by norm_num : (0 : ℝ) ≤ 3 / 2)
  change eps ^ (3 / 2 : ℝ) ≤ ((Delta * Real.sqrt M) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) at hp
  rw [← Real.rpow_mul hx.le] at hp
  norm_num only [show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one] at hp
  exact ⟨hpos, hp⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

open OriginalBetaATSTrial (Answer execute)

theorem cubic_asymptotic_rate_and_full_step_budget
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower Delta : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (start : E) (hgap : f start - lower ≤ Delta)
    (hsmall : eps ^ (3 / 2 : ℝ) ≤ Delta * Real.sqrt M) :
    let run := execute getter (program M eps (fuel Delta M eps) start)
    ‖gradient f run.1.point‖ ≤ eps ∧
      (run.1.moves : ℝ) ≤ 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) ∧
      run.1.cubicSteps ≤ 5 * Delta / M ∧
      (run.2 : ℝ) ≤ 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) := by
  dsimp only
  have hDelta : 0 ≤ Delta := by linarith only [hgap, hbelow start]
  have hpow : 0 < eps ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos heps _
  have hs := actual_finite_cubic_termination f hC2 M eps lower Delta hM heps hH hbelow getter hvalid start hgap
  have hrate : 1 ≤ Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) :=
    (le_div_iff₀ hpow).mpr (by simpa only [one_mul] using hsmall)
  let t := Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ)
  change 1 ≤ t at hrate
  rw [reciprocal_charge_identity Delta M eps hM heps] at hs
  have hcube : stepRadius M eps ^ 3 ≤ Delta / (64 * M) := by
    rw [(radius_and_charge_identities M eps hM heps).1]
    calc
      _ ≤ (Delta * Real.sqrt M) / (64 * M * Real.sqrt M) :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ = _ := by field_simp [ne_of_gt (Real.sqrt_pos.mpr hM)]
  refine ⟨hs.2.1, ?_, ?_, ?_⟩
  · have hh := hs.2.2.1
    rw [show 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 256 * t by dsimp [t]; ring] at hh
    rw [show 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 512 * t by dsimp [t]; ring]
    nlinarith only [hh, hrate]
  · have hh := hs.2.2.2.1
    have hn : 0 ≤ Delta / M := by positivity
    rw [show 4 * Delta / M = 4 * (Delta / M) by ring] at hh
    rw [show Delta / (64 * M) = (Delta / M) / 64 by ring] at hcube
    rw [show 5 * Delta / M = 5 * (Delta / M) by ring]
    nlinarith only [hh, hcube, hn]
  · have hh := hs.2.2.2.2
    rw [show 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 256 * t by dsimp [t]; ring] at hh
    rw [show 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 512 * t by dsimp [t]; ring]
    nlinarith only [hh, hrate]

end OriginalOuterCubicSeparateErrors
end

section
-- Source component: StatefulCubicStepValue.lean

namespace OriginalStatefulEnvelopeCubic

open OriginalOuterCubic OriginalOuterCubicSeparateErrors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section
set_option maxHeartbeats 3000000

/-- Every actual cubic step increases the value by at most one explicit terminal
charge. Large steps decrease it. This controls the genuine terminal query's envelope
gap without invoking the refuted unconditional all-step cube budget. -/
theorem actual_step_value_upper
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (x : E) (a : OriginalBetaATSTrial.Answer E) (ha : Accurate f M eps x a) :
    let s := minimizer a.grad a.hess (2 * M)
    f (x + s) ≤ f x + stepCharge M eps := by
  let s := minimizer a.grad a.hess (2 * M)
  let R := stepRadius M eps
  have hp := radius_properties M eps hM heps
  have hcharge : 0 ≤ stepCharge M eps := hp.2.2.2.le
  by_cases hlarge : R ≤ ‖s‖
  · have hd := (actual_step_radius_and_descent f hC2 M eps hM heps hH x a ha).1 hlarge
    have hnon : 0 ≤ M / 4 * ‖s‖ ^ 3 := by positivity
    change f (x + s) ≤ f x + _
    linarith only [hd, hnon, hcharge]
  · have hr : ‖s‖ ≤ R := (lt_of_not_ge hlarge).le
    have hR : 0 < R := hp.2.1
    have hRsq : M * R ^ 2 = eps / 16 := hp.2.2.1
    have hq0 := Real.sqrt_nonneg (M * eps)
    have hqsq := Real.sq_sqrt (show 0 ≤ M * eps by positivity)
    have hQ : Real.sqrt (M * eps) = 4 * M * R := by
      have hh := congrArg (fun t : ℝ => 16 * M * t) hRsq
      have hh' : (4 * M * R) ^ 2 = M * eps := by nlinarith only [hh]
      have hMR : 0 < 4 * M * R := by positivity
      nlinarith only [hh', hqsq, hq0, hMR]
    have hEps : eps = 16 * M * R ^ 2 := by linarith only [hRsq]
    have herr : eps / 1024 * R + (Real.sqrt (M * eps) / 1024) / 2 * R ^ 2 ≤ stepCharge M eps := by
      have heq : eps / 1024 * R + (Real.sqrt (M * eps) / 1024) / 2 * R ^ 2 =
          (9 / 512 : ℝ) * M * R ^ 3 := by rw [hQ, hEps]; ring
      rw [heq]
      change (9 / 512 : ℝ) * M * R ^ 3 ≤ M / 4 * R ^ 3
      have hn : 0 ≤ M * R ^ 3 := by positivity
      nlinarith only [hn]
    have hs := (inexact_step_bounds f hC2 M hM hH x a.grad a.hess (eps / 1024)
      (Real.sqrt (M * eps) / 1024) ha.1 ha.2).1
    have hlin := mul_le_mul_of_nonneg_left hr (show 0 ≤ eps / 1024 by positivity)
    have hsq := pow_le_pow_left₀ (norm_nonneg s) hr 2
    have hquad := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ (Real.sqrt (M * eps) / 1024) / 2 by positivity)
    have hcube : 0 ≤ M * ‖s‖ ^ 3 := by positivity
    change f (x + s) ≤ f x + _
    change f (x + s) - f x ≤ -(M / 3) * ‖s‖ ^ 3 + eps / 1024 * ‖s‖ +
      (Real.sqrt (M * eps) / 1024) / 2 * ‖s‖ ^ 2 at hs
    nlinarith only [hs, hlin, hquad, herr, hcube]

end
end OriginalStatefulEnvelopeCubic
end

section
-- Source component: StatefulEnvelopeCubicProgram.lean

namespace OriginalStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalEnvelopeOracleProgram
open OriginalOuterCubic OriginalOuterCubicSeparateErrors

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def estimateProgram (mu L rho D tau : ℝ) (x : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Estimate E F) :=
  OriginalEnvelopeOracleProgram.program L x (OriginalMinimumWarmSolver.program mu L rho D tau x x yin)

def asAnswer (a : Estimate E F) : Answer E := ⟨a.grad, a.hess⟩

theorem actual_estimate
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (estimateProgram mu L rho D tau x yin)
    ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
    ‖run.1.grad - gradient (saddleEnvelope (JointSliceRegularity.curry J) L) x‖ ≤ 2 * L * tau ∧
    ‖run.1.hess - fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x‖ ≤
      4 * rho * (1 + L / mu) ^ 2 * tau ∧
    (run.2 : ℝ) ≤ (1 + min (Real.sqrt (L / mu)) ((rho * D / mu) ^ (2 / 7 : ℝ))) *
      OriginalMinimumWarmSolver.logFactor J mu L rho D tau x x yin + 1 := by
  let p := OriginalMinimumWarmSolver.program mu L rho D tau x x yin
  let w := (execute (OriginalDualOracleProgram.actualOracle J) p).1
  have hw := OriginalMinimumWarmSolver.actual_minimum_warm_solver J mu L rho D tau
    hmu hLmu hrho htau hC2 hLip hHess hsc x x yin hwarm
  have he := OriginalEnvelopeOracle.envelope_oracle_from_joint_negative_slice J L mu rho
    (hmu.trans_le hLmu) hmu hrho hC2 hsc hLip hHess x w tau hw.1
  unfold estimateProgram
  rw [OriginalEnvelopeOracleProgram.actual_execution]
  refine ⟨hw.1, he.1, he.2, ?_⟩
  simp only [Nat.cast_add, Nat.cast_one]
  exact add_le_add hw.2 (le_refl (1 : ℝ))

structure Result (E F : Type*) where
  point : E
  saddle : Joint E F
  success : Bool
  charged : ℕ
  moves : List (OriginalStatefulEnvelopeGD.Move E F)

def cubedMovement (moves : List (OriginalStatefulEnvelopeGD.Move E F)) : ℝ :=
  (moves.map (fun m => ‖m.next - m.previous‖ ^ 3)).sum

def appendCharged (m : OriginalStatefulEnvelopeGD.Move E F) (out : Result E F) : Result E F :=
  { out with charged := out.charged + 1, moves := m :: out.moves }

/-- Actual cubic execution with a previous returned saddle kept as inner warm state. -/
def loop (mu L rho tau M eps : ℝ) : ℕ → E → Estimate E F →
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F)
  | 0, x, a => .pure ⟨x, a.saddle, false, 0, []⟩
  | n + 1, x, a =>
      if ‖a.grad‖ ≤ eps / 2 then .pure ⟨x, a.saddle, true, 0, []⟩
      else
        let s := minimizer a.grad a.hess (2 * M)
        let y := x + s
        let D := tau + 2 * Real.sqrt (L / mu) * ‖s‖
        let m : OriginalStatefulEnvelopeGD.Move E F := ⟨x, y, a.saddle.snd, D⟩
        bind (estimateProgram mu L rho D tau y a.saddle.snd) (fun ay =>
          if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
          else map (appendCharged m) (loop mu L rho tau M eps n y ay))

end
end OriginalStatefulEnvelopeCubic
end

section
-- Source component: StatefulEnvelopeCubicTrajectory.lean

namespace OriginalStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalEnvelopeOracleProgram
open OriginalOuterCubic OriginalOuterCubicSeparateErrors

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

structure LoopSpec (J : Joint E F → ℝ) (mu L rho tau M eps lower : ℝ)
    (n : ℕ) (x : E) (run : Result E F × ℕ) : Prop where
  close : ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L run.1.point‖ ≤ tau
  charged_budget : stepCharge M eps * (run.1.charged : ℝ) ≤ saddleEnvelope (JointSliceRegularity.curry J) L x - lower
  cube_budget : M / 4 * cubedMovement run.1.moves ≤ saddleEnvelope (JointSliceRegularity.curry J) L x - lower + stepCharge M eps
  length_bound : run.1.moves.length ≤ run.1.charged + 1
  terminal : run.1.success = true → ‖gradient (saddleEnvelope (JointSliceRegularity.curry J) L) run.1.point‖ ≤ eps
  exhausted : run.1.success = false → run.1.charged = n
  original_cost : (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ)
  value_upper : saddleEnvelope (JointSliceRegularity.curry J) L run.1.point ≤ saddleEnvelope (JointSliceRegularity.curry J) L x + stepCharge M eps
  legal_moves : ∀ m ∈ run.1.moves,
    ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
    m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
    saddleEnvelope (JointSliceRegularity.curry J) L m.previous ≤ saddleEnvelope (JointSliceRegularity.curry J) L x ∧
    saddleEnvelope (JointSliceRegularity.curry J) L m.next ≤ saddleEnvelope (JointSliceRegularity.curry J) L x + stepCharge M eps

theorem actual_loop_spec
    (J : Joint E F → ℝ) (mu L rho tau M eps lower : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau) (hM : 0 < M) (heps : 0 < eps)
    (htolG : 2 * L * tau ≤ eps / 1024)
    (htolH : 4 * rho * (1 + L / mu) ^ 2 * tau ≤ Real.sqrt (M * eps) / 1024)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hEHess : ∀ x y : E,
      ‖fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x -
        fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ saddleEnvelope (JointSliceRegularity.curry J) L x)
    (n : ℕ) (x : E) (a : Estimate E F)
    (hclose : ‖a.saddle - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau)
    (ha : Accurate (saddleEnvelope (JointSliceRegularity.curry J) L) M eps x (asAnswer a)) :
    LoopSpec J mu L rho tau M eps lower n x
      (execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps n x a)) := by
  let Ef := saddleEnvelope (JointSliceRegularity.curry J) L
  have hL : 0 < L := hmu.trans_le hLmu
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hEC2 : ContDiff ℝ 2 Ef := OriginalEnvelopeRegularity.actual_envelope_contDiff2 J L mu hL hmu hC2 hsc hLip
  have hp := radius_properties M eps hM heps
  have hcharge : 0 < stepCharge M eps := hp.2.2.2
  induction n generalizing x a with
  | zero =>
      rw [loop]
      simp only [execute]
      refine ⟨hclose, ?_, ?_, by norm_num, ?_, fun _ => rfl, ?_, ?_, ?_⟩
      · simp only [Nat.cast_zero, mul_zero]
        change 0 ≤ Ef x - lower
        linarith only [hbelow x]
      · change M / 4 * (0 : ℝ) ≤ Ef x - lower + stepCharge M eps
        linarith only [hbelow x, hcharge]
      · intro hh
        cases hh
      · simp [OriginalStatefulEnvelopeGD.costSum]
      · change Ef x ≤ Ef x + stepCharge M eps
        linarith only [hcharge]
      · intro m hm
        cases hm
  | succ n ih =>
      by_cases hstop : ‖a.grad‖ ≤ eps / 2
      · rw [loop, if_pos hstop]
        simp only [execute]
        refine ⟨hclose, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Nat.cast_zero, mul_zero]
          change 0 ≤ Ef x - lower
          linarith only [hbelow x]
        · change M / 4 * (0 : ℝ) ≤ Ef x - lower + stepCharge M eps
          linarith only [hbelow x, hcharge]
        · intro _
          exact accurate_stop Ef M eps heps x (asAnswer a) ha hstop
        · intro hh
          cases hh
        · simp [OriginalStatefulEnvelopeGD.costSum]
        · change Ef x ≤ Ef x + stepCharge M eps
          linarith only [hcharge]
        · intro m hm
          cases hm
      · let s := minimizer a.grad a.hess (2 * M)
        let y := x + s
        let D := tau + 2 * Real.sqrt (L / mu) * ‖s‖
        let m : OriginalStatefulEnvelopeGD.Move E F := ⟨x, y, a.saddle.snd, D⟩
        let first := execute (OriginalDualOracleProgram.actualOracle J) (estimateProgram mu L rho D tau y a.saddle.snd)
        let ay := first.1
        have hs : y - x = s := by dsimp only [y]; abel
        have hprevious : ‖a.saddle.snd - vStar (JointSliceRegularity.curry J) L x‖ ≤ tau :=
          (WithLp.norm_snd_le E (a.saddle - zStar (JointSliceRegularity.curry J) L x)).trans hclose
        have hwarm : ‖a.saddle.snd - vStar (JointSliceRegularity.curry J) L y‖ ≤ D := by
          have hh := OriginalWarmAmortization.actual_warm_dual_distance J L mu hL hmu hJ hLip hsc x y a.saddle.snd tau hprevious
          simpa only [hs] using hh
        have hfirst := actual_estimate J mu L rho D tau hmu hLmu hrho htau hC2 hLip hHess hsc y a.saddle.snd hwarm
        have hayClose : ‖ay.saddle - zStar (JointSliceRegularity.curry J) L y‖ ≤ tau := hfirst.1
        have hay : Accurate Ef M eps y (asAnswer ay) :=
          ⟨hfirst.2.1.trans htolG, hfirst.2.2.1.trans htolH⟩
        have hfirstCost : (first.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.moveCost J mu L rho tau m + 1 := hfirst.2.2.2
        have hstep := actual_step_radius_and_descent Ef hEC2 M eps hM heps hEHess x (asAnswer a) ha
        change (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ Ef x - Ef y) ∧
          (∀ ay' : Answer E, Accurate Ef M eps y ay' → ¬ ‖ay'.grad‖ ≤ eps / 2 →
            stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ Ef x - Ef y) at hstep
        have hvalue : Ef y ≤ Ef x + stepCharge M eps := actual_step_value_upper Ef hEC2 M eps hM heps hEHess x (asAnswer a) ha
        by_cases hnext : ‖ay.grad‖ ≤ eps / 2
        · have hexec : execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps (n + 1) x a) =
              (⟨y, ay.saddle, true, 0, [m]⟩, first.2) := by
            simp only [loop, if_neg hstop, execute_bind]
            change ((execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).1,
              first.2 + (execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).2) = _
            rw [if_pos hnext]
            rfl

          have hbudget : M / 4 * ‖s‖ ^ 3 ≤ Ef x - lower + stepCharge M eps := by
            by_cases hlarge : stepRadius M eps ≤ ‖s‖
            · have hd := hstep.1 hlarge
              linarith only [hd, hbelow y, hcharge]
            · have hr : ‖s‖ ≤ stepRadius M eps := (lt_of_not_ge hlarge).le
              have hc : ‖s‖ ^ 3 ≤ stepRadius M eps ^ 3 := by gcongr
              have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ M / 4 by positivity)
              unfold stepCharge
              linarith only [hh, hbelow x]
          rw [hexec]
          refine ⟨hayClose, ?_, ?_, by norm_num, ?_, ?_, ?_, hvalue, ?_⟩
          · simp only [Nat.cast_zero, mul_zero]
            change 0 ≤ Ef x - lower
            linarith only [hbelow x]
          · change M / 4 * (‖y - x‖ ^ 3 + 0) ≤ Ef x - lower + stepCharge M eps
            simpa only [hs, add_zero] using hbudget
          · intro _
            exact accurate_stop Ef M eps heps y (asAnswer ay) hay hnext
          · intro hh
            cases hh
          · simpa only [OriginalStatefulEnvelopeGD.costSum, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, add_zero, List.length_singleton, Nat.cast_one] using hfirstCost
          · intro move hmem
            have he : move = m := List.mem_singleton.mp hmem
            subst move
            refine ⟨hwarm, ?_, le_refl _, hvalue⟩
            change D = tau + 2 * Real.sqrt (L / mu) * ‖y - x‖
            rw [hs]
        · let rest := execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps n y ay)
          have hrec := ih y ay hayClose hay
          change LoopSpec J mu L rho tau M eps lower n y rest at hrec
          have hd := hstep.2 (asAnswer ay) hay hnext
          have hc : stepRadius M eps ^ 3 ≤ ‖s‖ ^ 3 := by exact pow_le_pow_left₀ hp.2.1.le hd.1 3
          have hpaid : stepCharge M eps ≤ M / 4 * ‖s‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hc (show 0 ≤ M / 4 by positivity)
          have hdescent : Ef y ≤ Ef x := by
            have hn : 0 ≤ M / 4 * ‖s‖ ^ 3 := by positivity
            linarith only [hd.2, hn]
          have hexec : execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps (n + 1) x a) =
              (appendCharged m rest.1, first.2 + rest.2) := by
            simp only [loop, if_neg hstop, execute_bind]
            change ((execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).1,
              first.2 + (execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).2) = _
            rw [if_neg hnext, execute_map]
          rw [hexec]
          have hcube : cubedMovement (m :: rest.1.moves) = ‖s‖ ^ 3 + cubedMovement rest.1.moves := by
            simp only [cubedMovement, List.map_cons, List.sum_cons]
            change ‖y - x‖ ^ 3 + _ = _
            rw [hs]
          refine ⟨hrec.close, ?_, ?_, ?_, hrec.terminal, ?_, ?_, ?_, ?_⟩
          · change stepCharge M eps * ((rest.1.charged + 1 : ℕ) : ℝ) ≤ Ef x - lower
            push_cast
            have hh := hrec.charged_budget
            nlinarith only [hh, hd.2, hpaid]
          · change M / 4 * cubedMovement (m :: rest.1.moves) ≤ Ef x - lower + stepCharge M eps
            rw [hcube]
            have hh := hrec.cube_budget
            nlinarith only [hh, hd.2]
          · have hh := hrec.length_bound
            change (m :: rest.1.moves).length ≤ rest.1.charged + 1 + 1
            simp only [List.length_cons]
            omega
          · intro hh
            exact congrArg Nat.succ (hrec.exhausted hh)
          · change ((first.2 + rest.2 : ℕ) : ℝ) ≤ OriginalStatefulEnvelopeGD.costSum J mu L rho tau (m :: rest.1.moves) + ((m :: rest.1.moves).length : ℝ)
            simp only [Nat.cast_add, OriginalStatefulEnvelopeGD.costSum, List.map_cons, List.sum_cons,
              List.length_cons, Nat.cast_one]
            have hh := hrec.original_cost
            dsimp only [OriginalStatefulEnvelopeGD.costSum] at hh
            linarith only [hh, hfirstCost]
          · have hh := hrec.value_upper
            exact hh.trans (add_le_add hdescent le_rfl)
          · intro move hmem
            rcases List.mem_cons.mp hmem with he | he
            · subst move
              refine ⟨hwarm, ?_, le_refl _, ?_⟩
              · change D = tau + 2 * Real.sqrt (L / mu) * ‖y - x‖
                rw [hs]
              · exact hdescent.trans (le_add_of_nonneg_right hcharge.le)
            · obtain ⟨hlegal, hradius, hprev, hnext⟩ := hrec.legal_moves move he
              exact ⟨hlegal, hradius, hprev.trans hdescent, hnext.trans (add_le_add hdescent le_rfl)⟩

end
end OriginalStatefulEnvelopeCubic
end

section
-- Source component: StatefulCubicFiniteProgram.lean

namespace OriginalStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalEnvelopeOracleProgram
open OriginalOuterCubic OriginalOuterCubicSeparateErrors

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def program (mu L rho D0 tau M eps Delta : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F) :=
  bind (estimateProgram mu L rho D0 tau start yin) (fun a =>
    loop mu L rho tau M eps (OriginalOuterCubicSeparateErrors.fuel Delta M eps) start a)

/-- The complete stateful cubic execution halts. The extra terminal cube and its
slightly larger level set are retained explicitly, including when the gap is zero. -/
theorem actual_finite_termination_with_warm_trace
    (J : Joint E F → ℝ) (mu L rho D0 tau M eps Delta lower : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hM : 0 < M) (heps : 0 < eps)
    (htolG : 2 * L * tau ≤ eps / 1024)
    (htolH : 4 * rho * (1 + L / mu) ^ 2 * tau ≤ Real.sqrt (M * eps) / 1024)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hEHess : ∀ x y : E,
      ‖fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x -
        fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ saddleEnvelope (JointSliceRegularity.curry J) L x)
    (start : E) (yin : F)
    (hgap : saddleEnvelope (JointSliceRegularity.curry J) L start - lower ≤ Delta)
    (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L start‖ ≤ D0) :
    let run := execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D0 tau M eps Delta start yin)
    run.1.success = true ∧
    ‖gradient (saddleEnvelope (JointSliceRegularity.curry J) L) run.1.point‖ ≤ eps ∧
    ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L run.1.point‖ ≤ tau ∧
    (run.1.moves.length : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
    cubedMovement run.1.moves ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧
    (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin +
      1 + OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ) ∧
    (∀ m ∈ run.1.moves,
      ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
      m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
      saddleEnvelope (JointSliceRegularity.curry J) L m.previous - lower ≤ Delta ∧
      saddleEnvelope (JointSliceRegularity.curry J) L m.next - lower ≤ Delta + stepCharge M eps) := by
  let first := execute (OriginalDualOracleProgram.actualOracle J)
    (estimateProgram mu L rho D0 tau start yin)
  let n := OriginalOuterCubicSeparateErrors.fuel Delta M eps
  let rest := execute (OriginalDualOracleProgram.actualOracle J)
    (loop mu L rho tau M eps n start first.1)
  have hp := radius_properties M eps hM heps
  have hcharge : 0 < stepCharge M eps := hp.2.2.2
  have hfirst := actual_estimate J mu L rho D0 tau hmu hLmu hrho htau hC2 hLip hHess hsc start yin hwarm
  have hclose : ‖first.1.saddle - zStar (JointSliceRegularity.curry J) L start‖ ≤ tau := hfirst.1
  have ha : Accurate (saddleEnvelope (JointSliceRegularity.curry J) L) M eps start (asAnswer first.1) :=
    ⟨hfirst.2.1.trans htolG, hfirst.2.2.1.trans htolH⟩
  have hcost0 : (first.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin + 1 := hfirst.2.2.2
  have hs := actual_loop_spec J mu L rho tau M eps lower hmu hLmu hrho htau hM heps htolG htolH
    hC2 hLip hHess hsc hEHess hbelow n start first.1 hclose ha
  change LoopSpec J mu L rho tau M eps lower n start rest at hs
  have hc : (rest.1.charged : ℝ) ≤ Delta / stepCharge M eps := by
    apply (le_div_iff₀ hcharge).mpr
    have hh := hs.charged_budget
    nlinarith only [hh, hgap]
  have hsuccess : rest.1.success = true := by
    cases hb : rest.1.success with
    | true => rfl
    | false =>
        have hcount := hs.exhausted hb
        rw [hcount] at hc
        dsimp [n, OriginalOuterCubicSeparateErrors.fuel] at hc
        push_cast at hc
        have hceil := Nat.le_ceil (Delta / stepCharge M eps)
        linarith only [hc, hceil]
  have hlength : (rest.1.moves.length : ℝ) ≤ 1 + Delta / stepCharge M eps := by
    have hh : (rest.1.moves.length : ℝ) ≤ (rest.1.charged : ℝ) + 1 := by exact_mod_cast hs.length_bound
    linarith only [hc, hh]
  have hcubes : cubedMovement rest.1.moves ≤ 4 * Delta / M + stepRadius M eps ^ 3 := by
    have hh := hs.cube_budget
    have hm : M * (4 * Delta / M + stepRadius M eps ^ 3) = 4 * Delta + 4 * stepCharge M eps := by
      unfold stepCharge
      field_simp
      <;> ring
    have hmul : M * cubedMovement rest.1.moves ≤ M * (4 * Delta / M + stepRadius M eps ^ 3) := by
      nlinarith only [hh, hgap, hm]
    exact (mul_le_mul_iff_right₀ hM).mp hmul
  have hexec : execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D0 tau M eps Delta start yin) = (rest.1, first.2 + rest.2) := by
    simp only [program, execute_bind]
    rfl
  rw [hexec]
  refine ⟨hsuccess, hs.terminal hsuccess, hs.close, hlength, hcubes, ?_, ?_⟩
  · simp only [Nat.cast_add]
    have hh := hs.original_cost
    linarith only [hh, hcost0]
  · intro m hm
    obtain ⟨hw, hr, hp, hn⟩ := hs.legal_moves m hm
    exact ⟨hw, hr, by linarith only [hp, hgap], by linarith only [hn, hgap]⟩

end
end OriginalStatefulEnvelopeCubic
end

section
-- Source component: StatefulEnvelopeCubicCaller.lean

namespace OriginalStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalOuterCubicSeparateErrors

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

def curvature (mu L rho : ℝ) := 8 * rho * (1 + L / mu) ^ (3 / 2 : ℝ)

def callerTolerance (mu L rho eps : ℝ) :=
  min (eps / (4096 * L))
    (min (Real.sqrt (curvature mu L rho * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2))
      (min (mu / rho) (OriginalStatefulEnvelopeGD.callerTolerance mu L eps)))

def caller (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F) :=
  program mu L rho (Ry + (L / mu) * Real.sqrt (Delta / L)) (callerTolerance mu L rho eps)
    (curvature mu L rho) (eps / 2) Delta start yin

theorem actual_cubic_caller_from_original_inputs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let M := curvature mu L rho
    let tau := callerTolerance mu L rho eps
    let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.1.moves.length : ℝ) ≤ 1 + Delta / stepCharge M (eps / 2) ∧
    cubedMovement run.1.moves ≤ 4 * Delta / M + stepRadius M (eps / 2) ^ 3 ∧
    (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin + 1 +
      OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ) ∧
    (∀ m ∈ run.1.moves,
      ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
      m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
      OriginalDualResidualQueryBound.observedRadius J L m.next m.next m.warm ≤
        3 * (Real.sqrt ((Delta + stepCharge M (eps / 2)) / L) + m.radius)) := by
  let f := JointSliceRegularity.curry J
  let lower := sInf (Set.range (phi f))
  let tau := callerTolerance mu L rho eps
  let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  let M := curvature mu L rho
  have hM : 0 < M := by dsimp [M, curvature]; positivity
  have hratio : 0 < L / mu := by positivity
  have htau : 0 < tau := by
    have hsq : 0 < Real.sqrt (M * (eps / 2)) := Real.sqrt_pos.mpr (by positivity)
    have hgd : 0 < OriginalStatefulEnvelopeGD.callerTolerance mu L eps := by
      unfold OriginalStatefulEnvelopeGD.callerTolerance
      positivity
    change 0 < min (eps / (4096 * L))
      (min (Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2))
        (min (mu / rho) (OriginalStatefulEnvelopeGD.callerTolerance mu L eps)))
    positivity
  have htolG : 2 * L * tau ≤ (eps / 2) / 1024 := by
    have ht : tau ≤ eps / (4096 * L) := min_le_left _ _
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * L by positivity)
    have he : 2 * L * (eps / (4096 * L)) = (eps / 2) / 1024 := by field_simp; ring
    exact hh.trans_eq he
  have htolH : 4 * rho * (1 + L / mu) ^ 2 * tau ≤ Real.sqrt (M * (eps / 2)) / 1024 := by
    have ht : tau ≤ Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 4 * rho * (1 + L / mu) ^ 2 by positivity)
    have he : 4 * rho * (1 + L / mu) ^ 2 *
        (Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2)) = Real.sqrt (M * (eps / 2)) / 1024 := by
      field_simp
      <;> ring
    exact hh.trans_eq he
  have htoutput : tau ≤ OriginalStatefulEnvelopeGD.callerTolerance mu L eps :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdx := JointSliceRegularity.differentiable_x_slice J hJ
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y
  have hxy := fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v
  obtain ⟨hPhi, hweak⟩ := phi_regular_from_slices f L mu hL hmu hdx hdy hsc hxx hxy
  have hE := saddleEnvelope_eq_moreau f L mu hmu hsc hdy
  have hElower : ∀ x, lower ≤ saddleEnvelope f L x := by
    intro x
    rw [hE, MoreauTransfer.envelope_eq_prox_objective (phi f) L hL hPhi hweak]
    have hp := csInf_le hbelow (Set.mem_range_self (MoreauTransfer.prox (phi f) L x))
    unfold MoreauTransfer.objective
    have hn : 0 ≤ L * ‖MoreauTransfer.prox (phi f) L x - x‖ ^ 2 := by positivity
    change lower ≤ phi f (MoreauTransfer.prox (phi f) L x) + _
    linarith only [hp, hn]
  have hEgap : saddleEnvelope f L start - lower ≤ Delta := by
    have hh := MoreauTransfer.envelope_le_original (phi f) L hL hPhi hweak start
    rw [← hE] at hh
    linarith only [hh, hgap]
  have hinit := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry
    hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hEHess := (OriginalEnvelopeRegularity.envelope_regularity_from_joint_negative_slice
    J L mu rho hL hmu hrho.le hC2 hsc hLip hHess).2.2
  have hh := actual_finite_termination_with_warm_trace J mu L rho D0 tau M (eps / 2) Delta lower
    hmu hLmu hrho.le htau hM (by positivity) htolG htolH hC2 hLip hHess hsc hEHess hElower start yin hEgap hinit
  change run.1.success = true ∧ _ at hh
  rcases hh with ⟨htrue, hgradE, hclose, hcount, hcubes, hcost, htrace⟩
  change ‖gradient (saddleEnvelope f L) run.1.point‖ ≤ eps / 2 at hgradE
  have htransfer := exact_transfer_from_slices f L mu hL hmu hdx hdy hsc hxx hxy hbelow start Delta hgap
  have hPhiLip := OriginalStatefulEnvelopeGD.actual_phi_gradient_lipschitz J mu L hmu hL hC2 hLip hsc
  have hfirst : ‖run.1.saddle.fst - uStar f L run.1.point‖ ≤ tau := by
    exact (WithLp.norm_fst_le E (run.1.saddle - zStar f L run.1.point)).trans hclose
  have houtput : ‖gradient (phi f) run.1.saddle.fst‖ ≤ eps := by
    have hd := hPhiLip run.1.saddle.fst (uStar f L run.1.point)
    have hm := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ L * (1 + L / mu) by positivity)
    have hn := norm_le_norm_sub_add (gradient (phi f) run.1.saddle.fst)
      (gradient (phi f) (uStar f L run.1.point))
    change ‖gradient (phi f) run.1.saddle.fst - gradient (phi f) (uStar f L run.1.point)‖ ≤ _ at hd
    rw [← (htransfer.1 run.1.point).2] at hn hd
    have hmul := mul_le_mul_of_nonneg_left htoutput (show 0 ≤ L * (1 + L / mu) by positivity)
    have he : L * (1 + L / mu) * OriginalStatefulEnvelopeGD.callerTolerance mu L eps = eps / 128 := by
      unfold OriginalStatefulEnvelopeGD.callerTolerance
      field_simp
      <;> ring
    rw [he] at hmul
    linarith only [hd, hm, hn, hgradE, hmul, heps]
  refine ⟨htrue, houtput, hcount, hcubes, hcost, ?_⟩
  · intro m hm
    obtain ⟨hlegal, hradius, hprev, hnext⟩ := htrace m hm
    have hb := (OriginalOuterPrimalInitialization.standing_primal_residual_bound J L mu lower (Delta + stepCharge M (eps / 2)) m.radius
      hL hmu hC2 hLip hsc (fun u => csInf_le hbelow ⟨u, rfl⟩) m.next m.warm hnext hlegal).2.2
    exact ⟨hlegal, hradius, hb⟩


end
end OriginalStatefulEnvelopeCubic
end

section
-- Source component: WarmCubedAmortization.lean

namespace OriginalWarmAmortization
open scoped BigOperators

variable {ι : Type*}

theorem warm_cost_sum_from_cubed_steps
    (s : Finset ι) (steps radius : ι → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hstep : ∀ i ∈ s, 0 ≤ steps i)
    (hradius : ∀ i ∈ s, 0 ≤ radius i) (hwarm : ∀ i ∈ s, radius i ≤ a + b * steps i) :
    ∑ i ∈ s, (1 + (radius i) ^ (2 / 7 : ℝ)) ≤
      (s.card : ℝ) * (1 + a ^ (2 / 7 : ℝ)) +
      b ^ (2 / 7 : ℝ) * (s.card : ℝ) ^ (19 / 21 : ℝ) * (∑ i ∈ s, (steps i) ^ 3) ^ (2 / 21 : ℝ) := by
  have hpoint : ∀ i ∈ s, (radius i) ^ (2 / 7 : ℝ) ≤ a ^ (2 / 7 : ℝ) +
      b ^ (2 / 7 : ℝ) * (steps i) ^ (2 / 7 : ℝ) := by
    intro i hi
    calc
      _ ≤ (a + b * steps i) ^ (2 / 7 : ℝ) := Real.rpow_le_rpow (hradius i hi) (hwarm i hi) (by norm_num)
      _ ≤ a ^ (2 / 7 : ℝ) + (b * steps i) ^ (2 / 7 : ℝ) :=
        Real.rpow_add_le_add_rpow ha (mul_nonneg hb (hstep i hi)) (by norm_num) (by norm_num)
      _ = _ := by rw [Real.mul_rpow hb (hstep i hi)]
  have hsum := Finset.sum_le_sum (fun i hi => add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) (hpoint i hi))
  have heq : ∑ i ∈ s, (1 + (a ^ (2 / 7 : ℝ) + b ^ (2 / 7 : ℝ) * (steps i) ^ (2 / 7 : ℝ))) =
      (s.card : ℝ) * (1 + a ^ (2 / 7 : ℝ)) + b ^ (2 / 7 : ℝ) * ∑ i ∈ s, (steps i) ^ (2 / 7 : ℝ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hholder := mul_le_mul_of_nonneg_left (holder_cubed_step_movement s steps hstep)
    (Real.rpow_nonneg hb (2 / 7 : ℝ))
  calc
    _ ≤ (s.card : ℝ) * (1 + a ^ (2 / 7 : ℝ)) + b ^ (2 / 7 : ℝ) * ∑ i ∈ s, (steps i) ^ (2 / 7 : ℝ) :=
      hsum.trans_eq heq
    _ ≤ _ := add_le_add le_rfl (by simpa only [mul_assoc] using hholder)

section ActualSaddle
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem actual_cubic_warm_polynomial_sum
    (J : Joint E F → ℝ) (L mu rho tau : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hrho : 0 ≤ rho) (htau : 0 ≤ tau) (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (s : Finset ι) (previous current : ι → E) (approximate : ι → F)
    (hprevious : ∀ i ∈ s, ‖approximate i - vStar (JointSliceRegularity.curry J) L (previous i)‖ ≤ tau) :
    ∑ i ∈ s, (1 + (rho * ‖approximate i - vStar (JointSliceRegularity.curry J) L (current i)‖ / mu) ^ (2 / 7 : ℝ)) ≤
      (s.card : ℝ) * (1 + (rho * tau / mu) ^ (2 / 7 : ℝ)) +
      (rho / mu * (2 * Real.sqrt (L / mu))) ^ (2 / 7 : ℝ) *
        (s.card : ℝ) ^ (19 / 21 : ℝ) * (∑ i ∈ s, ‖current i - previous i‖ ^ 3) ^ (2 / 21 : ℝ) := by
  apply warm_cost_sum_from_cubed_steps s (fun i => ‖current i - previous i‖)
    (fun i => rho * ‖approximate i - vStar (JointSliceRegularity.curry J) L (current i)‖ / mu)
    (rho * tau / mu) (rho / mu * (2 * Real.sqrt (L / mu))) (by positivity) (by positivity)
    (fun _ _ => norm_nonneg _) (fun _ _ => by positivity)
  intro i hi
  have hd := actual_warm_dual_distance J L mu hL hmu hJ hLip hsc (previous i) (current i)
    (approximate i) tau (hprevious i hi)
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ rho / mu by positivity)
  convert hh using 1 <;> first | rfl | ring

end ActualSaddle
end OriginalWarmAmortization
end

section
-- Source component: StatefulCubicResourceAmortization.lean

open scoped BigOperators
namespace OriginalStatefulEnvelopeCubic
open OriginalStatefulEnvelopeGD
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
noncomputable section
set_option maxHeartbeats 4000000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def cubicPolynomialBound (mu L rho tau : ℝ) (moves : List (Move E F)) : ℝ :=
  (moves.length : ℝ) * (1 + (rho * tau / mu) ^ (2 / 7 : ℝ)) +
    (rho / mu * (2 * Real.sqrt (L / mu))) ^ (2 / 7 : ℝ) *
      (moves.length : ℝ) ^ (19 / 21 : ℝ) * cubedMovement moves ^ (2 / 21 : ℝ)

/-- Actual per-move costs are amortized over the actual physical step trace.
The finite maximum of log-factors is retained explicitly, rather than assumed to be
uniformly polylogarithmic. -/
theorem actual_cubic_cost_sum_holder_bound
    (J : Joint E F → ℝ) (mu L rho tau : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hrho : 0 ≤ rho) (htau : 0 ≤ tau) (moves : List (Move E F))
    (hradii : ∀ m ∈ moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖) :
    costSum J mu L rho tau moves ≤
      maximumLog J mu L rho tau moves * cubicPolynomialBound mu L rho tau moves := by
  let N := moves.length
  let step : Fin N → ℝ := fun i => ‖(moves.get i).next - (moves.get i).previous‖
  let radius : Fin N → ℝ := fun i => rho * (moves.get i).radius / mu
  have hradius : ∀ i : Fin N, 0 ≤ (moves.get i).radius := by
    intro i
    rw [hradii (moves.get i) (List.get_mem _ _)]
    positivity
  have hM : 0 ≤ maximumLog J mu L rho tau moves :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (maximum_log_positive J mu L rho tau moves)
  have hpoint : ∀ i : Fin N,
      moveCost J mu L rho tau (moves.get i) ≤
        maximumLog J mu L rho tau moves * (1 + radius i ^ (2 / 7 : ℝ)) := by
    intro i
    have hlog : moveLog J mu L rho tau (moves.get i) ≤ maximumLog J mu L rho tau moves := by
      exact List.le_max_of_le' 1 (List.mem_map.mpr ⟨moves.get i, List.get_mem _ _, rfl⟩) le_rfl
    have hscale : 0 ≤ 1 + min (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ)) := by
      have hp : 0 ≤ radius i := div_nonneg (mul_nonneg hrho (hradius i)) hmu.le
      exact add_nonneg zero_le_one (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg hp _))
    have ha := mul_le_mul_of_nonneg_left hlog hscale
    have hb := mul_le_mul_of_nonneg_left
      (add_le_add_left (min_le_right (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ))) 1) hM
    change (1 + min (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ))) *
      moveLog J mu L rho tau (moves.get i) ≤ _
    exact ha.trans (by nlinarith only [hb])
  have hholder := OriginalWarmAmortization.warm_cost_sum_from_cubed_steps
    (Finset.univ : Finset (Fin N)) step radius (rho * tau / mu)
    (rho / mu * (2 * Real.sqrt (L / mu))) (by positivity) (by positivity)
    (fun _ _ => norm_nonneg _) (fun i _ => div_nonneg (mul_nonneg hrho (hradius i)) hmu.le) (by
      intro i _
      have hi := hradii (moves.get i) (List.get_mem _ _)
      change rho * (moves.get i).radius / mu ≤ rho * tau / mu +
        rho / mu * (2 * Real.sqrt (L / mu)) * ‖(moves.get i).next - (moves.get i).previous‖
      rw [hi]
      ring_nf
      exact le_rfl)
  have hcubes : ∑ i : Fin N, step i ^ 3 = cubedMovement moves :=
    (list_sum_as_fin moves (fun m => ‖m.next - m.previous‖ ^ 3)).symm
  have hpoly : ∑ i : Fin N, (1 + radius i ^ (2 / 7 : ℝ)) ≤ cubicPolynomialBound mu L rho tau moves := by
    simpa only [Finset.card_univ, Fintype.card_fin, hcubes, N, cubicPolynomialBound] using hholder
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [← Finset.mul_sum] at hsum
  rw [costSum, list_sum_as_fin]
  exact hsum.trans (mul_le_mul_of_nonneg_left hpoly hM)


theorem cubed_movement_nonnegative (moves : List (Move E F)) : 0 ≤ cubedMovement moves := by
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
    positivity)

theorem one_step_cubed_le_total (moves : List (Move E F)) (m : Move E F) (hm : m ∈ moves) :
    ‖m.next - m.previous‖ ^ 3 ≤ cubedMovement moves := by
  induction moves with
  | nil => cases hm
  | cons head tail ih =>
      simp only [cubedMovement, List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hm with h | h
      · subst m
        exact le_add_of_nonneg_right (cubed_movement_nonnegative tail)
      · exact (ih h).trans (le_add_of_nonneg_left (by positivity))

theorem norm_le_one_add_cube (v : E) : ‖v‖ ≤ 1 + ‖v‖ ^ 3 := by
  by_cases h : ‖v‖ ≤ 1
  · have hc : 0 ≤ ‖v‖ ^ 3 := by positivity
    linarith only [h, hc]
  · have h1 : 1 ≤ ‖v‖ := (lt_of_not_ge h).le
    have hh := mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ ‖v‖ ^ 2 + ‖v‖ by positivity)
    nlinarith only [hh]

theorem cubic_warm_radii_uniform_bound (L mu tau B : ℝ)
    (moves : List (Move E F)) (hcubes : cubedMovement moves ≤ B)
    (hradii : ∀ m ∈ moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖) :
    ∀ m ∈ moves, m.radius ≤ tau + 2 * Real.sqrt (L / mu) * (1 + B) := by
  intro m hm
  have hstep := (one_step_cubed_le_total moves m hm).trans hcubes
  have hn := norm_le_one_add_cube (m.next - m.previous)
  have hh := mul_le_mul_of_nonneg_left (show ‖m.next - m.previous‖ ≤ 1 + B by linarith only [hn,hstep])
    (show 0 ≤ 2 * Real.sqrt (L / mu) by positivity)
  rw [hradii m hm]
  linarith only [hh]

end
end OriginalStatefulEnvelopeCubic
end

section
-- Source component: CubicHolderTerminalNormalization.lean

namespace OriginalCubicHolderNormalization

set_option maxHeartbeats 3000000

/-- The terminal cube is charged to the same `1 + gap / charge` factor as the
actual number of moves. No small-epsilon premise or unconditional cube-sum bound
is used. -/
theorem holder_with_terminal_budget
    (N C B R a b : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C) (hB : 0 < B) (hR : 0 < R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hNB : N ≤ B) (hCB : C ≤ B * R ^ 3)
    (ha1 : a ≤ 1) (hbR : b * R ≤ 1) :
    N * (1 + a ^ (2 / 7 : ℝ)) +
      b ^ (2 / 7 : ℝ) * N ^ (19 / 21 : ℝ) * C ^ (2 / 21 : ℝ) ≤ 3 * B := by
  have haPow : a ^ (2 / 7 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow ha ha1 (by norm_num : (0 : ℝ) ≤ 2 / 7)
  have hNPow := Real.rpow_le_rpow hN hNB (by norm_num : (0 : ℝ) ≤ 19 / 21)
  have hCPow := Real.rpow_le_rpow hC hCB (by norm_num : (0 : ℝ) ≤ 2 / 21)
  have hRPow : (R ^ 3) ^ (2 / 21 : ℝ) = R ^ (2 / 7 : ℝ) := by
    rw [← Real.rpow_natCast R 3, ← Real.rpow_mul hR.le]
    norm_num
  have hBPow : B ^ (19 / 21 : ℝ) * B ^ (2 / 21 : ℝ) = B := by
    rw [← Real.rpow_add hB]
    norm_num
  have hprod : b ^ (2 / 7 : ℝ) * N ^ (19 / 21 : ℝ) * C ^ (2 / 21 : ℝ) ≤ B := by
    have h1 := mul_le_mul_of_nonneg_left hNPow (Real.rpow_nonneg hb (2 / 7 : ℝ))
    have h2 := mul_le_mul h1 hCPow (Real.rpow_nonneg hC (2 / 21 : ℝ))
      (mul_nonneg (Real.rpow_nonneg hb _) (Real.rpow_nonneg hB.le _))
    have hid : b ^ (2 / 7 : ℝ) * B ^ (19 / 21 : ℝ) * (B * R ^ 3) ^ (2 / 21 : ℝ) =
        B * (b * R) ^ (2 / 7 : ℝ) := by
      rw [Real.mul_rpow hB.le (pow_nonneg hR.le 3), hRPow, Real.mul_rpow hb hR.le]
      calc
        _ = (B ^ (19 / 21 : ℝ) * B ^ (2 / 21 : ℝ)) *
            (b ^ (2 / 7 : ℝ) * R ^ (2 / 7 : ℝ)) := by ring
        _ = _ := by rw [hBPow]
    rw [hid] at h2
    have h3 : (b * R) ^ (2 / 7 : ℝ) ≤ 1 := by
      simpa using Real.rpow_le_rpow (mul_nonneg hb hR.le) hbR (by norm_num : (0 : ℝ) ≤ 2 / 7)
    exact h2.trans (by nlinarith only [mul_le_mul_of_nonneg_left h3 hB.le])
  have hfirst := mul_le_mul hNB (show 1 + a ^ (2 / 7 : ℝ) ≤ 2 by linarith only [haPow])
    (show 0 ≤ 1 + a ^ (2 / 7 : ℝ) by positivity) hB.le
  nlinarith only [hfirst, hprod]

end OriginalCubicHolderNormalization
end

section
-- Source component: CubicSelectedRegimeNormalization.lean

namespace OriginalCubicSelectedRegime
noncomputable section
set_option maxHeartbeats 3000000

theorem warm_coefficient_times_step_radius_le_one
    (mu L rho eps : ℝ) (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1) :
    (rho / mu * (2 * Real.sqrt (L / mu))) *
      OriginalOuterCubicSeparateErrors.stepRadius (OriginalStatefulEnvelopeCubic.curvature mu L rho) (eps / 2) ≤ 1 := by
  let s := Real.sqrt (L / mu)
  let M := OriginalStatefulEnvelopeCubic.curvature mu L rho
  let R := OriginalOuterCubicSeparateErrors.stepRadius M (eps / 2)
  let b := rho / mu * (2 * s)
  have hL : 0 < L := hmu.trans_le hLmu
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = L / mu := Real.sq_sqrt (by positivity)
  have hLeq : L = mu * s ^ 2 := by rw [hs2]; field_simp
  have hM : 0 < M := by dsimp [M, OriginalStatefulEnvelopeCubic.curvature]; positivity
  have hp := OriginalOuterCubicSeparateErrors.radius_properties M (eps / 2) hM (by positivity)
  have hR : 0 < R := hp.2.1
  have hMR0 := hp.2.2.1
  have hMR : M * R ^ 2 = eps / 32 := by change M * R ^ 2 = eps / 2 / 16 at hMR0; linarith only [hMR0]
  have hpower : (L / mu) ^ (3 / 2 : ℝ) = s ^ 3 := by
    dsimp only [s]
    symm
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ L / mu by positivity)]
    norm_num
  have hMLower : 8 * rho * s ^ 3 ≤ M := by
    have hpow := Real.rpow_le_rpow (show 0 ≤ L / mu by positivity)
      (show L / mu ≤ 1 + L / mu by linarith) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [hpower] at hpow
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hRbound : R ^ 2 ≤ eps / (256 * rho * s ^ 3) := by
    apply (le_div_iff₀ (show 0 < 256 * rho * s ^ 3 by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hMLower (sq_nonneg R)
    nlinarith only [hh, hMR]
  have hb2 := mul_le_mul_of_nonneg_left hRbound (sq_nonneg b)
  have hid : b ^ 2 * (eps / (256 * rho * s ^ 3)) =
      OriginalGDRateNormalization.ratio mu L rho eps / 64 := by
    dsimp only [b, OriginalGDRateNormalization.ratio]
    change (rho / mu * (2 * s)) ^ 2 * (eps / (256 * rho * s ^ 3)) =
      (rho * s ^ 3 * eps / L ^ 2) / 64
    rw [hLeq]
    field_simp
    <;> ring
  rw [hid] at hb2
  have hb : 0 ≤ b * R := by dsimp [b]; positivity
  change b * R ≤ 1
  nlinarith only [hb2, hr, hb]

theorem terminal_cube_budget_factorization (Delta M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    4 * Delta / M + OriginalOuterCubicSeparateErrors.stepRadius M eps ^ 3 =
      (1 + Delta / OriginalOuterCubicSeparateErrors.stepCharge M eps) *
        OriginalOuterCubicSeparateErrors.stepRadius M eps ^ 3 := by
  have hp := OriginalOuterCubicSeparateErrors.radius_properties M eps hM heps
  have hR : OriginalOuterCubicSeparateErrors.stepRadius M eps ≠ 0 := ne_of_gt hp.2.1
  unfold OriginalOuterCubicSeparateErrors.stepCharge
  field_simp
  <;> ring

end
end OriginalCubicSelectedRegime
end

section
-- Source component: StatefulCubicUniformMainBranch.lean

namespace OriginalStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial OriginalOuterCubicSeparateErrors
open OriginalStatefulEnvelopeGD

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

def cubicBudget (mu L rho Delta eps : ℝ) :=
  1 + Delta / stepCharge (curvature mu L rho) (eps / 2)

def cubeBound (mu L rho Delta eps : ℝ) :=
  4 * Delta / curvature mu L rho + stepRadius (curvature mu L rho) (eps / 2) ^ 3

def queryGap (mu L rho Delta eps : ℝ) := Delta + stepCharge (curvature mu L rho) (eps / 2)

def globalWarmRadius (mu L rho Delta Ry eps : ℝ) :=
  max (OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry)
    (callerTolerance mu L rho eps + 2 * Real.sqrt (L / mu) * (1 + cubeBound mu L rho Delta eps))

def globalObservedRadius (mu L rho Delta Ry eps : ℝ) :=
  3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + globalWarmRadius mu L rho Delta Ry eps)

def globalLogFactor (mu L rho Delta Ry eps : ℝ) :=
  OriginalUniformMinimumWarmLog.uniformFactor mu L rho (globalWarmRadius mu L rho Delta Ry eps)
    (callerTolerance mu L rho eps) (globalObservedRadius mu L rho Delta Ry eps)

/-- The genuine cubic caller has a parameter-only logarithmic factor and a full
original-oracle budget in the selected `r ≤ 1` regime. Both the terminal move and
its extra envelope query are included. -/
theorem actual_uniform_cubic_selected_branch
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    let U := globalLogFactor mu L rho Delta Ry eps
    1 ≤ U ∧ run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.2 : ℝ) ≤ U * (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry +
      1 + 4 * cubicBudget mu L rho Delta eps) := by
  let tau := callerTolerance mu L rho eps
  let M := curvature mu L rho
  let D0 := OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry
  let B := cubicBudget mu L rho Delta eps
  let R := globalWarmRadius mu L rho Delta Ry eps
  let Obs := globalObservedRadius mu L rho Delta Ry eps
  let U := globalLogFactor mu L rho Delta Ry eps
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  have hM : 0 < M := by dsimp [M, curvature]; positivity
  have hp := radius_properties M (eps / 2) hM (by positivity)
  have hcharge : 0 < stepCharge M (eps / 2) := hp.2.2.2
  have hDelta : 0 ≤ Delta := by
    have hi := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap, hi]
  have hB : 0 < B := by dsimp [B,cubicBudget]; positivity
  have hCB : 0 ≤ cubeBound mu L rho Delta eps := by
    change 0 ≤ 4 * Delta / M + stepRadius M (eps / 2) ^ 3
    exact add_nonneg (by positivity) (pow_nonneg hp.2.1.le 3)
  have htau : 0 < tau := by
    have hsq : 0 < Real.sqrt (M * (eps / 2)) := Real.sqrt_pos.mpr (by positivity)
    have hgd : 0 < OriginalStatefulEnvelopeGD.callerTolerance mu L eps := by
      unfold OriginalStatefulEnvelopeGD.callerTolerance
      positivity
    change 0 < min (eps / (4096 * L))
      (min (Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2))
        (min (mu / rho) (OriginalStatefulEnvelopeGD.callerTolerance mu L eps)))
    positivity
  have hRtau : tau ≤ R := by
    apply le_trans ?_ (le_max_right _ _)
    exact le_add_of_nonneg_right (by positivity)
  have hR0 : D0 ≤ R := le_max_left _ _
  have hR : 0 < R := htau.trans_le hRtau
  have hObs : 0 ≤ Obs := by dsimp [Obs, globalObservedRadius]; positivity
  have hU : 1 ≤ U := OriginalStatefulEnvelopeGD.uniform_minimum_factor_ge_one
    mu L rho R tau Obs hmu hL hrho.le htau hR.le hObs
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hbase := actual_cubic_caller_from_original_inputs J mu L rho Delta Ry eps hmu hLmu hrho heps
    hC2 hLip hHess hsc hbelow start yin hgap hdual
  change run.1.success = true ∧ _ at hbase
  rcases hbase with ⟨htrue, hstationary, hcount, hcubes, hcost, htrace⟩
  have hrad : ∀ m ∈ run.1.moves, m.radius ≤ R := by
    intro m hm
    have hh := cubic_warm_radii_uniform_bound L mu tau (cubeBound mu L rho Delta eps) run.1.moves
      hcubes (fun m hm => (htrace m hm).2.1) m hm
    exact hh.trans (le_max_right _ _)
  have hlogs : ∀ m ∈ run.1.moves, OriginalStatefulEnvelopeGD.moveLog J mu L rho tau m ≤ U := by
    intro m hm
    obtain ⟨hlegal, _, hobs⟩ := htrace m hm
    have hD : 0 ≤ m.radius := (norm_nonneg _).trans hlegal
    have hobsR : OriginalDualResidualQueryBound.observedRadius J L m.next m.next m.warm ≤ Obs :=
      hobs.trans (by
        change 3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + m.radius) ≤
          3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + R)
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hrad m hm)) (by norm_num))
    exact (OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform J mu L rho m.radius tau R Obs
      hmu hL hrho htau hD (hrad m hm) hRtau hC2 hLip hHess hsc m.next m.next m.warm hobsR).2
  have hMax := OriginalStatefulEnvelopeGD.maximum_log_le_of_all J mu L rho tau U hU run.1.moves hlogs
  have hinit := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hD0 : 0 ≤ D0 := (norm_nonneg _).trans hinit
  have hinitObs := OriginalInitialSaddleRadius.actual_initial_primal_residual J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hSQ : Real.sqrt (Delta / L) ≤ Real.sqrt (queryGap mu L rho Delta eps / L) := by
    apply Real.sqrt_le_sqrt
    apply (div_le_div_iff_of_pos_right hL).mpr
    change Delta ≤ Delta + stepCharge M (eps / 2)
    linarith only [hcharge]
  have hinitObsR : OriginalDualResidualQueryBound.observedRadius J L start start yin ≤ Obs :=
    hinitObs.trans (by
      change 3 * (Real.sqrt (Delta / L) + D0) ≤
        3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + R)
      exact mul_le_mul_of_nonneg_left (add_le_add hSQ hR0) (by norm_num))
  have hinitLog := (OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform J mu L rho D0 tau R Obs
    hmu hL hrho htau hD0 hR0 hRtau hC2 hLip hHess hsc start start yin hinitObsR).2
  have hI0 : 0 ≤ OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry := by
    dsimp [OriginalStatefulEnvelopeGD.initializationPolynomial]
    have hp : 0 ≤ rho * OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry / mu := by
      change 0 ≤ rho * D0 / mu
      positivity
    positivity
  have hinitCost : OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin ≤
      OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry * U :=
    mul_le_mul_of_nonneg_left hinitLog hI0
  have htauSmall : rho * tau / mu ≤ 1 := by
    have ht : tau ≤ mu / rho :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ rho / mu by positivity)
    have he : (rho / mu) * (mu / rho) = 1 := by field_simp
    rw [he] at hh
    calc
      rho * tau / mu = (rho / mu) * tau := by ring
      _ ≤ 1 := hh
  have hfactor := OriginalCubicSelectedRegime.terminal_cube_budget_factorization Delta M (eps / 2) hM (by positivity)
  have hcubesB : cubedMovement run.1.moves ≤ B * stepRadius M (eps / 2) ^ 3 := hcubes.trans_eq hfactor
  have hpoly := OriginalCubicHolderNormalization.holder_with_terminal_budget
    (run.1.moves.length : ℝ) (cubedMovement run.1.moves) B (stepRadius M (eps / 2))
    (rho * tau / mu) (rho / mu * (2 * Real.sqrt (L / mu)))
    (by positivity) (cubed_movement_nonnegative _) hB hp.2.1 (by positivity) (by positivity)
    hcount hcubesB htauSmall
    (OriginalCubicSelectedRegime.warm_coefficient_times_step_radius_le_one mu L rho eps hmu hLmu hrho heps hr)
  have hholder := actual_cubic_cost_sum_holder_bound J mu L rho tau hmu hL hrho.le htau.le run.1.moves
    (fun m hm => (htrace m hm).2.1)
  have hcostMoves : OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves ≤ U * (3 * B) := by
    have hP0 : 0 ≤ cubicPolynomialBound mu L rho tau run.1.moves := by
      have hC0 := cubed_movement_nonnegative run.1.moves
      unfold cubicPolynomialBound
      positivity
    have h1 := mul_le_mul_of_nonneg_right hMax hP0
    have h2 := mul_le_mul_of_nonneg_left hpoly hU0
    exact hholder.trans (h1.trans h2)
  change (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin +
    1 + OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ) at hcost
  refine ⟨hU,htrue,hstationary,?_⟩
  change (run.2 : ℝ) ≤ U * (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry + 1 + 4 * B)
  have hlen : (run.1.moves.length : ℝ) ≤ B := hcount
  have h1 := mul_nonneg (sub_nonneg.mpr hU) (show 0 ≤ 1 + B by positivity)
  nlinarith only [hcost,hinitCost,hcostMoves,hlen,h1]

end
end OriginalStatefulEnvelopeCubic
end

section
-- Source component: CubicPaperRateNormalization.lean

namespace OriginalCubicPaperRate
noncomputable section
set_option maxHeartbeats 3000000

def A2 (mu L rho Delta eps : ℝ) :=
  Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) / eps ^ (3 / 2 : ℝ)

theorem sqrt_curvature_upper (mu L rho : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) :
    Real.sqrt (OriginalStatefulEnvelopeCubic.curvature mu L rho) ≤
      8 * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) := by
  have hL : 0 < L := hmu.trans_le hLmu
  have hk : 1 ≤ L / mu := (le_div_iff₀ hmu).mpr (by simpa using hLmu)
  have hk0 : 0 ≤ L / mu := by positivity
  have ht : Real.sqrt ((1 + L / mu) ^ (3 / 2 : ℝ)) = (1 + L / mu) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (show 0 ≤ 1 + L / mu by positivity)]
    norm_num
  have hroot : Real.sqrt (OriginalStatefulEnvelopeCubic.curvature mu L rho) =
      Real.sqrt 8 * Real.sqrt rho * (1 + L / mu) ^ (3 / 4 : ℝ) := by
    unfold OriginalStatefulEnvelopeCubic.curvature
    rw [Real.sqrt_mul (show 0 ≤ 8 * rho by positivity),Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8),ht]
  have hp := Real.rpow_le_rpow (show 0 ≤ 1 + L / mu by positivity)
    (show 1 + L / mu ≤ 2 * (L / mu) by linarith only [hk]) (by norm_num : (0 : ℝ) ≤ 3 / 4)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hk0] at hp
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have h8 : Real.sqrt (8 : ℝ) ≤ 4 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8),Real.sqrt_nonneg (8 : ℝ)]
  rw [hroot]
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hk0 (3 / 4 : ℝ))
  have h4 := mul_le_mul h8 (hp.trans h3) (Real.rpow_nonneg (show 0 ≤ 1 + L / mu by positivity) _)
    (by norm_num : (0 : ℝ) ≤ 4)
  have h5 := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg rho)
  nlinarith only [h5]

theorem cubic_budget_le_paper_rate (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (hDelta : 0 ≤ Delta) (heps : 0 < eps) :
    OriginalStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps ≤ 1 + 8192 * A2 mu L rho Delta eps := by
  have hL : 0 < L := hmu.trans_le hLmu
  let M := OriginalStatefulEnvelopeCubic.curvature mu L rho
  have hM : 0 < M := by dsimp [M,OriginalStatefulEnvelopeCubic.curvature]; positivity
  have hcharge := OriginalOuterCubicSeparateErrors.reciprocal_charge_identity Delta M (eps / 2) hM (by positivity)
  have hsqrt := sqrt_curvature_upper mu L rho hmu hLmu hrho
  have hscale : eps ^ (3 / 2 : ℝ) ≤ 4 * (eps / 2) ^ (3 / 2 : ℝ) := by
    have hid : eps = 2 * (eps / 2) := by ring
    have hh : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
      have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (3 / 2 : ℝ) ≤ 2)
      norm_num at ht
      exact ht
    calc
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (eps / 2) ^ (3 / 2 : ℝ) := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ eps / 2)]
        congr 1
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (by positivity)
  have hpow : 0 < eps ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos heps _
  have hhalf : 0 < (eps / 2) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hnum := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 256 * Delta by positivity)
  have h1 := div_le_div_of_nonneg_right hnum hhalf.le
  have h2 : (2048 * Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ)) / (eps / 2) ^ (3 / 2 : ℝ) ≤
      8192 * A2 mu L rho Delta eps := by
    unfold A2
    rw [show 8192 * (Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) / eps ^ (3 / 2 : ℝ)) =
      (8192 * Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ)) / eps ^ (3 / 2 : ℝ) by ring]
    apply (div_le_div_iff₀ hhalf hpow).mpr
    have hmul := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ 2048 * Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) by positivity)
    nlinarith only [hmul]
  change 1 + Delta / OriginalOuterCubicSeparateErrors.stepCharge M (eps / 2) ≤ _
  rw [hcharge]
  have h3 : 256 * Delta * Real.sqrt M / (eps / 2) ^ (3 / 2 : ℝ) ≤
      8192 * A2 mu L rho Delta eps := h1.trans (by convert! h2 using 1 <;> ring)
  linarith only [h3]

end
end OriginalCubicPaperRate
end

section
-- Source component: MainUpperRateComparison.lean

namespace OriginalMainUpperRates
noncomputable section
set_option maxHeartbeats 3000000

def cubic (mu L rho Delta eps : ℝ) :=
  OriginalCubicPaperRate.A2 mu L rho Delta eps *
    (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (1 / 7 : ℝ))

def middle (mu L rho Delta eps : ℝ) :=
  OriginalGDRateNormalization.A1 Delta L eps *
    (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ))

def first (mu L Delta eps : ℝ) :=
  Real.sqrt (L / mu) * OriginalGDRateNormalization.A1 Delta L eps

def frontier (mu L rho Delta eps : ℝ) :=
  min (cubic mu L rho Delta eps) (min (middle mu L rho Delta eps) (first mu L Delta eps))

theorem A2_eq_A1_sqrt_ratio (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (heps : 0 < eps) :
    OriginalCubicPaperRate.A2 mu L rho Delta eps =
      OriginalGDRateNormalization.A1 Delta L eps * Real.sqrt (OriginalGDRateNormalization.ratio mu L rho eps) := by
  have hk : 0 ≤ L / mu := by positivity
  have hr : 0 ≤ OriginalGDRateNormalization.ratio mu L rho eps := by
    unfold OriginalGDRateNormalization.ratio
    positivity
  have hp : ((L / mu) ^ (3 / 4 : ℝ)) ^ 2 = (L / mu) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk]
    norm_num
  let c := Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) * Real.sqrt eps / L
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcsq : c ^ 2 = OriginalGDRateNormalization.ratio mu L rho eps := by
    dsimp only [c]
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hrho,Real.sq_sqrt heps.le,hp,
      OriginalGDRateNormalization.ratio_eq_paper mu L rho eps hmu hL]
  have hroot : Real.sqrt (OriginalGDRateNormalization.ratio mu L rho eps) = c := by
    nlinarith only [Real.sq_sqrt hr,Real.sqrt_nonneg (OriginalGDRateNormalization.ratio mu L rho eps),hcsq,hc]
  have hepow : eps ^ (3 / 2 : ℝ) = eps * Real.sqrt eps := by
    calc
      _ = eps ^ (1 + 1 / 2 : ℝ) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add heps,Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [hroot]
  unfold OriginalCubicPaperRate.A2 OriginalGDRateNormalization.A1 c
  rw [hepow]
  field_simp
  <;> rw [Real.sq_sqrt heps.le]
  <;> ring

theorem A2_le_all_rates_in_small_regime (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (hDelta : 0 ≤ Delta) (heps : 0 < eps)
    (hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1) :
    OriginalCubicPaperRate.A2 mu L rho Delta eps ≤ frontier mu L rho Delta eps := by
  have hL : 0 < L := hmu.trans_le hLmu
  have ha1 : 0 ≤ OriginalGDRateNormalization.A1 Delta L eps := by unfold OriginalGDRateNormalization.A1; positivity
  have ha2 : 0 ≤ OriginalCubicPaperRate.A2 mu L rho Delta eps := by unfold OriginalCubicPaperRate.A2; positivity
  have hr0 : 0 ≤ OriginalGDRateNormalization.ratio mu L rho eps := by unfold OriginalGDRateNormalization.ratio; positivity
  have hsqrt : Real.sqrt (OriginalGDRateNormalization.ratio mu L rho eps) ≤ 1 := by
    have hh := Real.sqrt_le_sqrt hr
    simpa using hh
  have hk : 1 ≤ Real.sqrt (L / mu) := by
    have hh := Real.sqrt_le_sqrt ((le_div_iff₀ hmu).mpr (by simpa using hLmu) : 1 ≤ L / mu)
    simpa using hh
  have hA2 : OriginalCubicPaperRate.A2 mu L rho Delta eps ≤ OriginalGDRateNormalization.A1 Delta L eps := by
    rw [A2_eq_A1_sqrt_ratio mu L rho Delta eps hmu hL hrho heps]
    nlinarith only [mul_le_mul_of_nonneg_left hsqrt ha1]
  unfold frontier
  refine le_min ?_ (le_min ?_ ?_)
  · unfold cubic
    have hh := mul_nonneg ha2 (Real.rpow_nonneg hr0 (1 / 7 : ℝ))
    nlinarith only [hh]
  · unfold middle
    have hh := mul_nonneg ha1 (Real.rpow_nonneg hr0 (2 / 7 : ℝ))
    nlinarith only [hh,hA2]
  · unfold first
    have hh := mul_nonneg ha1 (sub_nonneg.mpr hk)
    nlinarith only [hh,hA2]

theorem middle_le_twice_cubic_in_large_regime (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (hDelta : 0 ≤ Delta) (heps : 0 < eps)
    (hr : 1 ≤ OriginalGDRateNormalization.ratio mu L rho eps) :
    middle mu L rho Delta eps ≤ 2 * cubic mu L rho Delta eps := by
  let r := OriginalGDRateNormalization.ratio mu L rho eps
  have ha1 : 0 ≤ OriginalGDRateNormalization.A1 Delta L eps := by unfold OriginalGDRateNormalization.A1; positivity
  have ha2 : 0 ≤ OriginalCubicPaperRate.A2 mu L rho Delta eps := by unfold OriginalCubicPaperRate.A2; positivity
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hpow : r ^ (2 / 7 : ℝ) ≤ Real.sqrt r := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hsqrt : 1 ≤ Real.sqrt r := by
    have hh := Real.sqrt_le_sqrt hr
    simpa using hh
  have hA2 := A2_eq_A1_sqrt_ratio mu L rho Delta eps hmu hL hrho heps
  change OriginalCubicPaperRate.A2 mu L rho Delta eps = OriginalGDRateNormalization.A1 Delta L eps * Real.sqrt r at hA2
  have h1 := mul_le_mul_of_nonneg_left (show 1 + r ^ (2 / 7 : ℝ) ≤ 2 * Real.sqrt r by linarith only [hpow,hsqrt]) ha1
  have h2 := mul_nonneg ha2 (Real.rpow_nonneg hr0 (1 / 7 : ℝ))
  unfold middle cubic
  change OriginalGDRateNormalization.A1 Delta L eps * (1 + r ^ (2 / 7 : ℝ)) ≤
    2 * (OriginalCubicPaperRate.A2 mu L rho Delta eps * (1 + r ^ (1 / 7 : ℝ)))
  nlinarith only [h1,h2,hA2]

end
end OriginalMainUpperRates
end

section
-- Source component: ZeroHessianOneQueryReconstruction.lean

namespace OriginalZeroHessianReconstruction

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial OriginalDualOracleProgram

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [FiniteDimensional ℝ Z]

def jet (J : Z → ℝ) (z : Z) : OracleAnswer Z :=
  ⟨J z, gradient J z, fderiv ℝ (gradient J) z⟩

/-- This is the explicit quadratic built from one exact bundle at zero. -/
def quadratic (a : OracleAnswer Z) (z : Z) : ℝ :=
  a.value + OriginalOuterCubic.model a.grad a.hess 0 z

def polynomialOracle (a : OracleAnswer Z) (z : Z) : OracleAnswer Z :=
  ⟨quadratic a z, a.grad + CertifiedATS.sympart a.hess z, CertifiedATS.sympart a.hess⟩

theorem polynomial_oracle_is_exact (a : OracleAnswer Z) :
    jet (quadratic a) = polynomialOracle a := by
  have hg (z : Z) : HasGradientAt (quadratic a) (a.grad + CertifiedATS.sympart a.hess z) z := by
    have hh := (OriginalOuterCubic.model_hasGradientAt a.grad a.hess 0 z).hasFDerivAt.const_add a.value
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert! hh using 1 <;> simp [quadratic]
  have hgrad : gradient (quadratic a) = fun z => a.grad + CertifiedATS.sympart a.hess z :=
    funext (fun z => (hg z).gradient)
  funext z
  have hfd : fderiv ℝ (gradient (quadratic a)) z = CertifiedATS.sympart a.hess := by
    rw [hgrad]
    exact ((CertifiedATS.sympart a.hess).hasFDerivAt.const_add a.grad).fderiv
  change (⟨quadratic a z, gradient (quadratic a) z,
    fderiv ℝ (gradient (quadratic a)) z⟩ : OracleAnswer Z) = _
  rw [hfd]
  congr 1
  exact congrFun hgrad z

theorem exact_global_quadratic_reconstruction (J : Z → ℝ) (hC2 : ContDiff ℝ 2 J)
    (hzero : ∀ z w : Z, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ 0 * ‖z - w‖) :
    quadratic (jet J 0) = J := by
  let H := fderiv ℝ (gradient J) 0
  have hJ : Differentiable ℝ J := hC2.differentiable (by norm_num)
  have hgrad : Differentiable ℝ (gradient J) :=
    (OriginalSaddleImplicit.contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
  have hconstant (z : Z) : fderiv ℝ (gradient J) z = H := by
    have hh := hzero z 0
    rw [zero_mul] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  have haffine : gradient J = fun z => gradient J 0 + H z := by
    apply eq_of_fderiv_eq hgrad (fun z => (H.hasFDerivAt.const_add (gradient J 0)).differentiableAt)
      (fun z => (hconstant z).trans (H.hasFDerivAt.const_add (gradient J 0)).fderiv.symm) 0
    simp only [map_zero,add_zero]
  have hsym : CertifiedATS.sympart H = H := by
    have hself := OriginalSaddleTangent.gradient_derivative_selfadjoint J hC2 (0 : Z)
    change H.adjoint = H at hself
    ext z
    simp only [CertifiedATS.sympart,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,hself]
    module
  let Q := quadratic (jet J 0)
  have hQ (z : Z) : HasGradientAt Q (gradient J 0 + H z) z := by
    have hh := (OriginalOuterCubic.model_hasGradientAt (gradient J 0) H 0 z).hasFDerivAt.const_add (J 0)
    rw [hsym] at hh
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert! hh using 1 <;> simp [Q,quadratic,jet,H]
  have heq : J = Q := by
    refine eq_of_fderiv_eq hJ (fun z => (hQ z).differentiableAt) ?_ 0 ?_
    · intro z
      rw [(hJ z).hasGradientAt.hasFDerivAt.fderiv,(hQ z).hasFDerivAt.fderiv,haffine]
      simp only [map_zero,add_zero]
    · simp [Q,quadratic,jet,OriginalOuterCubic.model]
  exact heq.symm

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Only the initial bundle is an original-oracle request. All later evaluations
are explicit evaluations of the reconstructed polynomial, hence free transcript
computation in the paper's model. The existing finite certified solver is reused
with this synthetic polynomial oracle. -/
def program (mu L Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OracleAnswer (Joint E F)) E :=
  .ask 0 (fun a => .pure
    ((OriginalBetaATSTrial.execute (polynomialOracle a)
      (OriginalStatefulEnvelopeGD.caller mu L 0 Delta Ry eps start yin)).1.saddle.fst))

theorem one_original_query_suffices_when_hessian_is_constant
    (J : Joint E F → ℝ) (mu L Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hzero : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ 0 * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := OriginalBetaATSTrial.execute (actualOracle J) (program mu L Delta Ry eps start yin)
    run.2 = 1 ∧ ‖gradient (phi (JointSliceRegularity.curry J)) run.1‖ ≤ eps := by
  have hmodel := exact_global_quadratic_reconstruction J hC2 hzero
  have horacle : polynomialOracle (actualOracle J 0) = actualOracle J := by
    change polynomialOracle (jet J 0) = jet J
    rw [← polynomial_oracle_is_exact,hmodel]
  have hrun := OriginalStatefulEnvelopeGD.actual_gradient_caller_from_original_inputs J mu L 0 Delta Ry eps
    hmu hLmu (by norm_num) heps hC2 hLip hzero hsc hbelow start yin hgap hdual
  simp only [program,OriginalBetaATSTrial.execute,horacle]
  exact ⟨trivial,hrun.2.1⟩

end
end OriginalZeroHessianReconstruction
end

section
-- Source component: ActualMainUpperProgram.lean

namespace OriginalActualMainUpper

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def positiveProgram (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) E :=
  if OriginalGDRateNormalization.ratio mu L rho eps ≤ 1 then
    map (fun out : OriginalStatefulEnvelopeCubic.Result E F => out.saddle.fst)
      (OriginalStatefulEnvelopeCubic.caller mu L rho Delta Ry eps start yin)
  else
    map (fun out : OriginalStatefulEnvelopeGD.Result E F => out.saddle.fst)
      (OriginalStatefulEnvelopeGD.caller mu L rho Delta Ry eps start yin)

def positiveLogFactor (mu L rho Delta Ry eps : ℝ) :=
  max (OriginalStatefulEnvelopeGD.globalLogFactor mu L rho Delta Ry eps)
    (OriginalStatefulEnvelopeCubic.globalLogFactor mu L rho Delta Ry eps)

def program (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) E :=
  if rho = 0 then OriginalZeroHessianReconstruction.program mu L Delta Ry eps start yin
  else positiveProgram mu L rho Delta Ry eps start yin

def logarithmicFactor (mu L rho Delta Ry eps : ℝ) :=
  if rho = 0 then 1 else positiveLogFactor mu L rho Delta Ry eps

theorem scalar_cost_domination (T u U I R c : ℝ)
    (hT : T ≤ u * (I + c * R)) (hu : u ≤ U) (hU : 0 ≤ U)
    (hI : 0 ≤ I) (hR : 0 ≤ R) (hc : 0 ≤ c) (hcmax : c ≤ 32768) :
    T ≤ 32768 * U * (I + R) := by
  have h1 := mul_le_mul_of_nonneg_right hu (show 0 ≤ I + c * R by positivity)
  have h2 := mul_nonneg hU (show 0 ≤ (32768 - c) * R by positivity)
  have h3 := mul_nonneg hU hI
  nlinarith only [hT,h1,h2,h3]

theorem cost_le_frontier_of_three_bounds (T K I mu L rho Delta eps : ℝ)
    (hc : T ≤ K * (I + OriginalMainUpperRates.cubic mu L rho Delta eps))
    (hm : T ≤ K * (I + OriginalMainUpperRates.middle mu L rho Delta eps))
    (hf : T ≤ K * (I + OriginalMainUpperRates.first mu L Delta eps)) :
    T ≤ K * (I + OriginalMainUpperRates.frontier mu L rho Delta eps) := by
  unfold OriginalMainUpperRates.frontier
  by_cases h : OriginalMainUpperRates.cubic mu L rho Delta eps ≤
      min (OriginalMainUpperRates.middle mu L rho Delta eps) (OriginalMainUpperRates.first mu L Delta eps)
  · rw [min_eq_left h]
    exact hc
  · rw [min_eq_right (le_of_not_ge h)]
    by_cases hm' : OriginalMainUpperRates.middle mu L rho Delta eps ≤ OriginalMainUpperRates.first mu L Delta eps
    · rw [min_eq_left hm']
      exact hm
    · rw [min_eq_right (le_of_not_ge hm')]
      exact hf

theorem positive_main_upper
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (positiveProgram mu L rho Delta Ry eps start yin)
    let U := positiveLogFactor mu L rho Delta Ry eps
    1 ≤ U ∧ ‖gradient (phi (JointSliceRegularity.curry J)) run.1‖ ≤ eps ∧
    (run.2 : ℝ) ≤ 32768 * U *
      (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry +
        OriginalMainUpperRates.frontier mu L rho Delta eps) := by
  let U := positiveLogFactor mu L rho Delta Ry eps
  let Ug := OriginalStatefulEnvelopeGD.globalLogFactor mu L rho Delta Ry eps
  let Uc := OriginalStatefulEnvelopeCubic.globalLogFactor mu L rho Delta Ry eps
  let I := OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry
  have hL : 0 < L := hmu.trans_le hLmu
  have hDelta : 0 ≤ Delta := by
    have hi := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap,hi]
  have hD0 : 0 ≤ OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry := by
    have hh := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
    exact (norm_nonneg _).trans hh
  have hI : 1 ≤ I := by
    change 1 ≤ 1 + min (Real.sqrt (L / mu))
      ((rho * OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry / mu) ^ (2 / 7 : ℝ))
    exact le_add_of_nonneg_right (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _))
  have hUgU : Ug ≤ U := le_max_left _ _
  have hUcU : Uc ≤ U := le_max_right _ _
  have hgd := OriginalStatefulEnvelopeGD.actual_uniform_gradient_main_branches J mu L rho Delta Ry eps
    hmu hLmu hrho heps hC2 hLip hHess hsc hbelow start yin hgap hdual
  have hUg : 1 ≤ Ug := hgd.1
  have hU : 1 ≤ U := hUg.trans hUgU
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  by_cases hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1
  · have hc := OriginalStatefulEnvelopeCubic.actual_uniform_cubic_selected_branch J mu L rho Delta Ry eps
      hmu hLmu hrho heps hr hC2 hLip hHess hsc hbelow start yin hgap hdual
    simp only [positiveProgram,if_pos hr,execute_map]
    refine ⟨hU,hc.2.2.1,?_⟩
    change ((execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalStatefulEnvelopeCubic.caller mu L rho Delta Ry eps start yin)).2 : ℝ) ≤
      32768 * U * (I + OriginalMainUpperRates.frontier mu L rho Delta eps)
    have hB := OriginalCubicPaperRate.cubic_budget_le_paper_rate mu L rho Delta eps hmu hLmu hrho hDelta heps
    have hA2 := OriginalMainUpperRates.A2_le_all_rates_in_small_regime mu L rho Delta eps hmu hLmu hrho.le hDelta heps hr
    have hraw : 0 ≤ I + 1 + 4 * OriginalStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps := by
      have hM : 0 < OriginalStatefulEnvelopeCubic.curvature mu L rho := by
        unfold OriginalStatefulEnvelopeCubic.curvature
        positivity
      have hcharge := (OriginalOuterCubicSeparateErrors.radius_properties
        (OriginalStatefulEnvelopeCubic.curvature mu L rho) (eps / 2) hM (by positivity)).2.2.2
      unfold OriginalStatefulEnvelopeCubic.cubicBudget
      positivity
    have h1 := mul_le_mul_of_nonneg_right hUcU hraw
    have h2 := mul_le_mul_of_nonneg_left
      (show I + 1 + 4 * OriginalStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps ≤
        32768 * (I + OriginalMainUpperRates.frontier mu L rho Delta eps) by nlinarith only [hB,hA2,hI]) hU0
    have hcCost := hc.2.2.2
    change ((execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalStatefulEnvelopeCubic.caller mu L rho Delta Ry eps start yin)).2 : ℝ) ≤
      Uc * (I + 1 + 4 * OriginalStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps) at hcCost
    nlinarith only [hcCost,h1,h2]
  · simp only [positiveProgram,if_neg hr,execute_map]
    refine ⟨hU,hgd.2.2.1,?_⟩
    let T := ((execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalStatefulEnvelopeGD.caller mu L rho Delta Ry eps start yin)).2 : ℝ)
    have hmiddle : T ≤ Ug * (I + 512 * OriginalMainUpperRates.middle mu L rho Delta eps) := by
      convert! hgd.2.2.2.1 using 1 <;> unfold OriginalMainUpperRates.middle <;> ring
    have hfirst : T ≤ Ug * (I + 256 * OriginalMainUpperRates.first mu L Delta eps) := by
      convert! hgd.2.2.2.2 using 1 <;> unfold OriginalMainUpperRates.first <;> ring
    have hmid0 : 0 ≤ OriginalMainUpperRates.middle mu L rho Delta eps := by
      unfold OriginalMainUpperRates.middle OriginalGDRateNormalization.A1 OriginalGDRateNormalization.ratio
      positivity
    have hfirst0 : 0 ≤ OriginalMainUpperRates.first mu L Delta eps := by
      unfold OriginalMainUpperRates.first OriginalGDRateNormalization.A1
      positivity
    have hcub0 : 0 ≤ OriginalMainUpperRates.cubic mu L rho Delta eps := by
      unfold OriginalMainUpperRates.cubic OriginalCubicPaperRate.A2 OriginalGDRateNormalization.ratio
      positivity
    have hcomp := OriginalMainUpperRates.middle_le_twice_cubic_in_large_regime mu L rho Delta eps hmu hL hrho.le hDelta heps (le_of_not_ge hr)
    have h1 : T ≤ Ug * (I + 1024 * OriginalMainUpperRates.cubic mu L rho Delta eps) := by
      have hh := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ 512 * Ug by positivity)
      nlinarith only [hmiddle,hh]
    have hc := scalar_cost_domination T Ug U I (OriginalMainUpperRates.cubic mu L rho Delta eps) 1024
      h1 hUgU hU0 (zero_le_one.trans hI) hcub0 (by norm_num) (by norm_num)
    have hm := scalar_cost_domination T Ug U I (OriginalMainUpperRates.middle mu L rho Delta eps) 512
      hmiddle hUgU hU0 (zero_le_one.trans hI) hmid0 (by norm_num) (by norm_num)
    have hf := scalar_cost_domination T Ug U I (OriginalMainUpperRates.first mu L Delta eps) 256
      hfirst hUgU hU0 (zero_le_one.trans hI) hfirst0 (by norm_num) (by norm_num)
    exact cost_le_frontier_of_three_bounds T (32768 * U) I mu L rho Delta eps hc hm hf

/-- Full actual original-oracle upper program: rho=0 reconstructs the whole
quadratic from one bundle; rho>0 selects cubic/GD using only known parameters.
The original theorem's randomized lower bound is a separate obligation. -/
theorem main_upper_from_original_standing_inputs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program mu L rho Delta Ry eps start yin)
    let U := logarithmicFactor mu L rho Delta Ry eps
    1 ≤ U ∧ ‖gradient (phi (JointSliceRegularity.curry J)) run.1‖ ≤ eps ∧
    (run.2 : ℝ) ≤ 32768 * U *
      (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry +
        OriginalMainUpperRates.frontier mu L rho Delta eps) := by
  by_cases hzero : rho = 0
  · subst rho
    have hh := OriginalZeroHessianReconstruction.one_original_query_suffices_when_hessian_is_constant
      J mu L Delta Ry eps hmu hLmu heps hC2 hLip hHess hsc hbelow start yin hgap hdual
    simp only [program,logarithmicFactor,if_pos rfl,ite_true]
    refine ⟨le_refl _,hh.2,?_⟩
    rw [hh.1]
    have hDelta : 0 ≤ Delta := by
      have hi := csInf_le hbelow (Set.mem_range_self start)
      linarith only [hgap,hi]
    have hL : 0 < L := hmu.trans_le hLmu
    have hF : 0 ≤ OriginalMainUpperRates.frontier mu L 0 Delta eps := by
      unfold OriginalMainUpperRates.frontier OriginalMainUpperRates.cubic OriginalMainUpperRates.middle
        OriginalMainUpperRates.first OriginalCubicPaperRate.A2 OriginalGDRateNormalization.A1 OriginalGDRateNormalization.ratio
      positivity
    have hI : 1 ≤ OriginalStatefulEnvelopeGD.initializationPolynomial mu L 0 Delta Ry := by
      unfold OriginalStatefulEnvelopeGD.initializationPolynomial
      simp only [zero_mul,zero_div,Real.zero_rpow (by norm_num : (2 / 7 : ℝ) ≠ 0)]
      exact le_add_of_nonneg_right (le_min (Real.sqrt_nonneg _) le_rfl)
    norm_num only [Nat.cast_one,mul_one]
    nlinarith only [hF,hI]
  · have hpos : 0 < rho := lt_of_le_of_ne hrho (Ne.symm hzero)
    simp only [program,logarithmicFactor,if_neg hzero]
    exact positive_main_upper J mu L rho Delta Ry eps hmu hLmu hpos heps hC2 hLip hHess hsc hbelow start yin hgap hdual

end
end OriginalActualMainUpper
end

section
-- Source component: MeasurableArgminSelectionV2.lean

open scoped Topology
open MeasureTheory Filter TopologicalSpace

namespace OriginalMeasurableArgmin
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 3000000

variable {P X : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
  [MetricSpace X] [CompleteSpace X] [ProperSpace X] [SecondCountableTopology X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]

def IsMin (F : P × X → ℝ) (p : P) (x : X) : Prop := ∀ y : X, F (p,x) ≤ F (p,y)

def HitsBall (F : P × X → ℝ) (c : X) (r : ℝ) (p : P) : Prop :=
  ∃ x ∈ Metric.closedBall c r, IsMin F p x

/-- A fixed compact ball removes the unbounded projection issue. This establishes
the measurable hit predicates used below directly from the actual model's closed
argmin graph, rather than assuming a measurable optimizer. -/
theorem closed_hits_ball (F : P × X → ℝ) (hF : Continuous F) (c : X) (r : ℝ) :
    IsClosed {p : P | HitsBall F c r p} := by
  let K := Metric.closedBall c r
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
  let S : Set (P × K) := {q | ∀ y : X, F (q.1,(q.2 : X)) ≤ F (q.1,y)}
  have hS : IsClosed S := by
    dsimp only [S]
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro y
    exact isClosed_le
      (hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      (hF.comp (continuous_fst.prodMk continuous_const))
  have hp := isClosedMap_fst_of_compactSpace S hS
  convert! hp using 1
  ext p
  constructor
  · rintro ⟨x,hx,hm⟩
    exact ⟨(p,⟨x,hx⟩),hm,rfl⟩
  · rintro ⟨⟨q,x⟩,hm,hp⟩
    change q = p at hp
    subst q
    exact ⟨x,x.property,hm⟩

theorem measurable_hits_ball (F : P × X → ℝ) (hF : Continuous F) (c : X) (r : ℝ) :
    MeasurableSet {p : P | HitsBall F c r p} :=
  (closed_hits_ball F hF c r).measurableSet

def radius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

structure Approximation (F : P × X → ℝ) (n : ℕ) where
  point : P → X
  measurable : Measurable point
  hits : ∀ p, HitsBall F (point p) (radius n) p

theorem exists_initial_index (F : P × X → ℝ) (hmin : ∀ p, ∃ x, IsMin F p x) (p : P) :
    ∃ k : ℕ, HitsBall F (denseSeq X k) (radius 0) p := by
  obtain ⟨x,hx⟩ := hmin p
  obtain ⟨k,hk⟩ := (denseRange_denseSeq X).exists_dist_lt x (radius_pos 0)
  exact ⟨k,x,hk.le,hx⟩

def initialApproximation (F : P × X → ℝ) (hF : Continuous F)
    (hmin : ∀ p, ∃ x, IsMin F p x) : Approximation F 0 where
  point p := denseSeq X (Nat.find (exists_initial_index F hmin p))
  measurable := Measurable.find (fun _ => measurable_const)
    (fun k => measurable_hits_ball F hF (denseSeq X k) (radius 0))
    (exists_initial_index F hmin)
  hits p := Nat.find_spec (exists_initial_index F hmin p)

def NextPredicate (F : P × X → ℝ) (n : ℕ) (prev : Approximation F n) (p : P) (k : ℕ) : Prop :=
  HitsBall F (denseSeq X k) (radius (n+1)) p ∧
    dist (denseSeq X k) (prev.point p) < radius n + radius (n+1)

theorem exists_next_index (F : P × X → ℝ) (n : ℕ) (prev : Approximation F n) (p : P) :
    ∃ k : ℕ, NextPredicate F n prev p k := by
  obtain ⟨x,hx,hm⟩ := prev.hits p
  obtain ⟨k,hk⟩ := (denseRange_denseSeq X).exists_dist_lt x (radius_pos (n+1))
  refine ⟨k,⟨x,hk.le,hm⟩,?_⟩
  have ht := dist_triangle (denseSeq X k) x (prev.point p)
  rw [dist_comm (denseSeq X k) x] at ht
  change dist x (prev.point p) ≤ radius n at hx
  linarith only [ht,hk,hx]

def nextApproximation (F : P × X → ℝ) (hF : Continuous F)
    (n : ℕ) (prev : Approximation F n) : Approximation F (n+1) where
  point p := denseSeq X (Nat.find (exists_next_index F n prev p))
  measurable := Measurable.find (fun _ => measurable_const) (fun k =>
    (measurable_hits_ball F hF (denseSeq X k) (radius (n+1))).inter
      (measurableSet_lt (measurable_const.dist prev.measurable) measurable_const))
    (exists_next_index F n prev)
  hits p := (Nat.find_spec (exists_next_index F n prev p)).1

def approximations (F : P × X → ℝ) (hF : Continuous F)
    (hmin : ∀ p, ∃ x, IsMin F p x) : (n : ℕ) → Approximation F n
  | 0 => initialApproximation F hF hmin
  | n+1 => nextApproximation F hF n (approximations F hF hmin n)

theorem approximation_step_bound (F : P × X → ℝ) (hF : Continuous F)
    (hmin : ∀ p, ∃ x, IsMin F p x) (p : P) (n : ℕ) :
    dist ((approximations F hF hmin n).point p)
      ((approximations F hF hmin (n+1)).point p) ≤ (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
  have hh := (Nat.find_spec (exists_next_index F n (approximations F hF hmin n) p)).2
  change dist (denseSeq X (Nat.find (exists_next_index F n (approximations F hF hmin n) p)))
    ((approximations F hF hmin n).point p) < radius n + radius (n+1) at hh
  rw [dist_comm] at hh
  have he : radius n + radius (n+1) = (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by unfold radius; rw [pow_succ]; ring
  exact hh.le.trans_eq he

theorem approximations_cauchy (F : P × X → ℝ) (hF : Continuous F)
    (hmin : ∀ p, ∃ x, IsMin F p x) (p : P) :
    CauchySeq (fun n => (approximations F hF hmin n).point p) :=
  cauchySeq_of_le_geometric (1/2) (3/2) (by norm_num)
    (approximation_step_bound F hF hmin p)

def selector (F : P × X → ℝ) (hF : Continuous F)
    (hmin : ∀ p, ∃ x, IsMin F p x) (p : P) : X :=
  limUnder atTop (fun n => (approximations F hF hmin n).point p)

theorem selector_tendsto (F : P × X → ℝ) (hF : Continuous F)
    (hmin : ∀ p, ∃ x, IsMin F p x) (p : P) :
    Tendsto (fun n => (approximations F hF hmin n).point p) atTop (𝓝 (selector F hF hmin p)) :=
  (approximations_cauchy F hF hmin p).tendsto_limUnder

theorem selector_measurable (F : P × X → ℝ) (hF : Continuous F)
    (hmin : ∀ p, ∃ x, IsMin F p x) : Measurable (selector F hF hmin) :=
  measurable_of_tendsto_metrizable (fun n => (approximations F hF hmin n).measurable)
    (tendsto_pi_nhds.mpr (selector_tendsto F hF hmin))

theorem selector_is_min (F : P × X → ℝ) (hF : Continuous F)
    (hmin : ∀ p, ∃ x, IsMin F p x) (p : P) : IsMin F p (selector F hF hmin p) := by
  have hex (n : ℕ) : ∃ x : X,
      dist x ((approximations F hF hmin n).point p) ≤ radius n ∧ IsMin F p x := by
    obtain ⟨x,hx,hm⟩ := (approximations F hF hmin n).hits p
    exact ⟨x,hx,hm⟩
  choose x hx hmx using hex
  have hr : Tendsto radius atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  have hd : Tendsto (fun n => dist ((approximations F hF hmin n).point p) (x n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hr
    simpa only [dist_comm] using hx n
  have hxt : Tendsto x atTop (𝓝 (selector F hF hmin p)) :=
    (selector_tendsto F hF hmin p).congr_dist hd
  intro y
  have ht : Tendsto (fun n => F (p,x n)) atTop (𝓝 (F (p,selector F hF hmin p))) :=
    hF.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds hxt)
  exact le_of_tendsto ht (Eventually.of_forall (fun n => hmx n y))

/-- A constructive Borel selection from the actual closed argmin graph. No
uniqueness, symmetry, convexity, or target measurable-selector premise is required. -/
theorem exists_measurable_argmin (F : P × X → ℝ) (hF : Continuous F)
    (hmin : ∀ p, ∃ x, IsMin F p x) :
    ∃ s : P → X, Measurable s ∧ ∀ p, IsMin F p (s p) :=
  ⟨selector F hF hmin,selector_measurable F hF hmin,selector_is_min F hF hmin⟩

end
end OriginalMeasurableArgmin
end

section
-- Source component: CubicBorelModelSelection.lean

namespace OriginalCubicBorelSelection
open MeasureTheory
noncomputable section
set_option maxHeartbeats 3000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

def family (M : ℝ) (q : (E × (E →L[ℝ] E)) × E) : ℝ :=
  OriginalOuterCubic.model q.1.1 q.1.2 M q.2

theorem family_continuous (M : ℝ) : Continuous (family (E := E) M) := by
  unfold family OriginalOuterCubic.model
  fun_prop

theorem family_has_min (M : ℝ) (hM : 0 < M) (p : E × (E →L[ℝ] E)) :
    ∃ x : E, OriginalMeasurableArgmin.IsMin (family M) p x :=
  OriginalOuterCubic.exists_model_minimizer p.1 p.2 M hM

/-- A fixed Borel optimizer of the actual cubic model, including its nonunique
hard cases. Its value depends solely on the finite transcript model coefficients. -/
def select (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) : E :=
  OriginalMeasurableArgmin.selector (family M) (family_continuous M) (family_has_min M hM) (v,H)

theorem select_is_actual (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    ∀ t : E, OriginalOuterCubic.model v H M (select v H M hM) ≤ OriginalOuterCubic.model v H M t :=
  OriginalMeasurableArgmin.selector_is_min (family M) (family_continuous M) (family_has_min M hM) (v,H)

theorem select_measurable (M : ℝ) (hM : 0 < M) :
    Measurable (fun p : E × (E →L[ℝ] E) => select p.1 p.2 M hM) :=
  OriginalMeasurableArgmin.selector_measurable (family M) (family_continuous M) (family_has_min M hM)

end
end OriginalCubicBorelSelection
end

section
-- Source component: MeasurableMainUpperCoreV2.lean

namespace OriginalBorelOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section

def model (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) : ℝ :=
  inner ℝ v s + (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3

theorem model_hasGradientAt (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) :
    HasGradientAt (model v H M) (v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s) s := by
  have heq : CertifiedATS.model v H M 0 = model v H M := by
    funext d
    simp only [CertifiedATS.model, model, mul_zero, div_zero, zero_mul, add_zero]
  have hh := CertifiedATS.model_hasGradientAt v H M 0 s
  rw [heq] at hh
  simpa only [inv_zero, zero_smul, add_zero] using hh

theorem model_lower_bound (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) :
    -‖v‖ * ‖s‖ - ‖H‖ / 2 * ‖s‖ ^ 2 + M / 6 * ‖s‖ ^ 3 ≤ model v H M s := by
  have hv := real_inner_le_norm (-v) s
  rw [inner_neg_left, norm_neg] at hv
  have hH := real_inner_le_norm (-(H s)) s
  rw [inner_neg_left, norm_neg] at hH
  have hn := mul_le_mul_of_nonneg_right (H.le_opNorm s) (norm_nonneg s)
  unfold model
  nlinarith only [hv, hH, hn]

def modelRadius (v : E) (H : E →L[ℝ] E) (M : ℝ) : ℝ :=
  1 + 12 * (‖v‖ + ‖H‖) / M

theorem model_nonnegative_outside (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M)
    (s : E) (hout : modelRadius v H M ≤ ‖s‖) : 0 ≤ model v H M s := by
  have hR : 1 ≤ modelRadius v H M := by
    have hh : 0 ≤ 12 * (‖v‖ + ‖H‖) / M := by positivity
    unfold modelRadius
    linarith only [hh]
  have hr : 1 ≤ ‖s‖ := hR.trans hout
  have hMr : 12 * (‖v‖ + ‖H‖) ≤ M * ‖s‖ := by
    have hh := mul_le_mul_of_nonneg_left hout hM.le
    dsimp only [modelRadius] at hh
    have hid : M * (1 + 12 * (‖v‖ + ‖H‖) / M) = M + 12 * (‖v‖ + ‖H‖) := by
      field_simp <;> ring
    rw [hid] at hh
    linarith only [hh, hM]
  have hmul := mul_le_mul_of_nonneg_right hMr (sq_nonneg ‖s‖)
  have hvr : ‖v‖ * ‖s‖ ≤ ‖v‖ * ‖s‖ ^ 2 := by
    have hh : ‖s‖ ≤ ‖s‖ ^ 2 := by nlinarith only [hr]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg v)
  have hH0 := mul_nonneg (norm_nonneg H) (sq_nonneg ‖s‖)
  have hv0 := mul_nonneg (norm_nonneg v) (sq_nonneg ‖s‖)
  have hlower := model_lower_bound v H M s
  nlinarith only [hmul, hvr, hH0, hv0, hlower]

theorem exists_model_minimizer (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    ∃ s : E, ∀ t : E, model v H M s ≤ model v H M t := by
  let R := modelRadius v H M
  have hR : 0 < R := by dsimp only [R, modelRadius]; positivity
  have hzero : (0 : E) ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_self] using hR.le
  have hcont : Continuous (model v H M) :=
    (show Differentiable ℝ (model v H M) from fun s => (model_hasGradientAt v H M s).differentiableAt).continuous
  obtain ⟨s, hs, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn ⟨0, hzero⟩ hcont.continuousOn
  refine ⟨s, ?_⟩
  intro t
  by_cases ht : t ∈ Metric.closedBall 0 R
  · exact hmin ht
  · have hout : modelRadius v H M ≤ ‖t‖ := by
      have hh : R < ‖t‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using ht
      exact hh.le
    have hs0 : model v H M s ≤ model v H M 0 := hmin hzero
    have h0 : model v H M 0 = 0 := by simp only [model, inner_zero_right, norm_zero]; ring
    rw [h0] at hs0
    exact hs0.trans (model_nonnegative_outside v H M hM t hout)

def minimizer (v : E) (H : E →L[ℝ] E) (M : ℝ) : E :=
  if hM : 0 < M then OriginalCubicBorelSelection.select v H M hM else 0

theorem minimizer_is_actual (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    ∀ t : E, model v H M (minimizer v H M) ≤ model v H M t := by
  unfold minimizer
  rw [dif_pos hM]
  exact OriginalCubicBorelSelection.select_is_actual v H M hM

theorem minimizer_equation_and_decrease (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    let s := minimizer v H M
    v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s = 0 ∧
      model v H M s ≤ -(M / 12) * ‖s‖ ^ 3 := by
  dsimp only
  let s := minimizer v H M
  have hmin := minimizer_is_actual v H M hM
  have hloc : IsLocalMin (model v H M) s := Filter.Eventually.of_forall hmin
  have hg := hloc.hasFDerivAt_eq_zero (model_hasGradientAt v H M s).hasFDerivAt
  have heq : v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s = 0 := by
    have hh := congrArg (fun D : E →L[ℝ] ℝ => D (v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s)) hg
    simpa only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.zero_apply,
      real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] using hh
  have hinner := congrArg (fun w : E => inner ℝ w s) heq
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
    real_inner_self_eq_norm_sq] at hinner
  have hsym : inner ℝ (CertifiedATS.sympart H s) s = inner ℝ (H s) s := by
    simp only [CertifiedATS.sympart, smul_apply, add_apply, real_inner_smul_left,
      inner_add_left, ContinuousLinearMap.adjoint_inner_left, real_inner_comm s (H s)]
    ring
  rw [hsym] at hinner
  have hmirror := hmin (-s)
  have hneg : model v H M (-s) = -inner ℝ v s + (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3 := by
    simp only [model, inner_neg_right, map_neg, inner_neg_left, neg_neg, norm_neg]
  rw [hneg] at hmirror
  dsimp only [model] at hmirror ⊢
  refine ⟨heq, ?_⟩
  nlinarith only [hinner, hmirror]

end
end OriginalBorelOuterCubic


namespace OriginalBorelOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem cubic_taylor_upper
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (z s : E) :
    f (z + s) ≤ f z + inner ℝ (gradient f z) s +
      (1 / 2 : ℝ) * inner ℝ (fderiv ℝ (gradient f) z s) s + M / 6 * ‖s‖ ^ 3 := by
  let H := fderiv ℝ (gradient f) z
  let phi : ℝ → ℝ := fun t => f (z + t • s) - f z - t * inner ℝ (gradient f z) s -
    t ^ 2 / 2 * inner ℝ (H s) s - (M / 6 * ‖s‖ ^ 3) * t ^ 3
  let phi' : ℝ → ℝ := fun t => inner ℝ (gradient f (z + t • s)) s -
    inner ℝ (gradient f z) s - t * inner ℝ (H s) s - (M / 2 * ‖s‖ ^ 3) * t ^ 2
  have hdiff : Differentiable ℝ f := hC2.differentiable (by norm_num)
  have hderiv : ∀ t : ℝ, HasDerivAt phi (phi' t) t := by
    intro t
    have hcurve : HasDerivAt (fun t : ℝ => z + t • s) s t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const s).const_add z
    have hgcurve : HasDerivAt (fun t : ℝ => f (z + t • s))
        (inner ℝ (gradient f (z + t • s)) s) t := by
      simpa only [Function.comp_def, inner_gradient_left] using
        ((hdiff (z + t • s)).hasFDerivAt.comp_hasDerivAt t hcurve)
    have hlin := (hasDerivAt_id t).mul_const (inner ℝ (gradient f z) s)
    have hquad := (((hasDerivAt_id t).pow 2).div_const 2).mul_const (inner ℝ (H s) s)
    have hcubic := ((hasDerivAt_id t).pow 3).const_mul (M / 6 * ‖s‖ ^ 3)
    simp only [id_eq, Pi.pow_apply] at hlin hquad hcubic
    have hh := (((hgcurve.sub_const (f z)).sub hlin).sub hquad).sub hcubic
    convert! hh using 1 <;> dsimp only [phi, phi'] <;> ring
  have hnonpos : phi' ≤ 0 := by
    intro t
    let R := gradient f (z + t • s) - gradient f z - H (t • s)
    have hR := RobustAHPE.gradient_taylor_remainder f hC2 M hM hH z (t • s)
    change ‖R‖ ≤ M / 2 * ‖t • s‖ ^ 2 at hR
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hR
    have hinner := real_inner_le_norm R s
    have hm := mul_le_mul_of_nonneg_right hR (norm_nonneg s)
    have he : inner ℝ R s = inner ℝ (gradient f (z + t • s)) s -
        inner ℝ (gradient f z) s - t * inner ℝ (H s) s := by
      simp only [R, inner_sub_left, map_smul, real_inner_smul_left]
    rw [he] at hinner
    change inner ℝ (gradient f (z + t • s)) s - inner ℝ (gradient f z) s -
      t * inner ℝ (H s) s - (M / 2 * ‖s‖ ^ 3) * t ^ 2 ≤ 0
    nlinarith only [hinner, hm]
  have hanti := antitone_of_hasDerivAt_nonpos hderiv hnonpos
  have hh := hanti (by norm_num : (0 : ℝ) ≤ 1)
  dsimp only [phi] at hh
  simp only [zero_smul, add_zero, one_smul, zero_mul, one_mul, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), one_pow, sub_self, sub_zero, zero_div] at hh
  change f (z + s) ≤ _
  nlinarith only [hh]

end OriginalBorelOuterCubic


namespace OriginalBorelOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem inexact_step_bounds
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (z v : E) (Ht : E →L[ℝ] E) (deltaG deltaH : ℝ)
    (hG : ‖v - gradient f z‖ ≤ deltaG)
    (hHt : ‖Ht - fderiv ℝ (gradient f) z‖ ≤ deltaH) :
    let s := minimizer v Ht (2 * M)
    f (z + s) - f z ≤ -(M / 3) * ‖s‖ ^ 3 + deltaG * ‖s‖ + deltaH / 2 * ‖s‖ ^ 2 ∧
      ‖gradient f (z + s)‖ ≤ (3 * M / 2) * ‖s‖ ^ 2 + deltaH * ‖s‖ + deltaG := by
  dsimp only
  let s := minimizer v Ht (2 * M)
  let H := fderiv ℝ (gradient f) z
  have hm := minimizer_equation_and_decrease v Ht (2 * M) (by positivity)
  change v + CertifiedATS.sympart Ht s + (2 * M / 2 * ‖s‖) • s = 0 ∧
    model v Ht (2 * M) s ≤ -(2 * M / 12) * ‖s‖ ^ 3 at hm
  have htaylor := cubic_taylor_upper f hC2 M hM hH z s
  have hg : ‖gradient f z - v‖ ≤ deltaG := by simpa only [norm_sub_rev] using hG
  have hgnorm := real_inner_le_norm (gradient f z - v) s
  have hgmul := mul_le_mul_of_nonneg_right hg (norm_nonneg s)
  simp only [inner_sub_left] at hgnorm
  have hdiff : ‖H - Ht‖ ≤ deltaH := by simpa only [norm_sub_rev] using hHt
  have hnorm := ((H - Ht).le_opNorm s).trans (mul_le_mul_of_nonneg_right hdiff (norm_nonneg s))
  have hinner := real_inner_le_norm ((H - Ht) s) s
  have hhmul := mul_le_mul_of_nonneg_right hnorm (norm_nonneg s)
  simp only [sub_apply, inner_sub_left] at hinner
  have hmodel := hm.2
  dsimp only [model] at hmodel
  simp only [sub_apply] at hhmul
  change f (z + s) ≤ f z + inner ℝ (gradient f z) s +
    (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3 at htaylor
  refine ⟨?_, ?_⟩
  · change f (z + s) - f z ≤ -(M / 3) * ‖s‖ ^ 3 + deltaG * ‖s‖ + deltaH / 2 * ‖s‖ ^ 2
    nlinarith only [htaylor, hmodel, hgnorm, hgmul, hinner, hhmul]
  · change ‖gradient f (z + s)‖ ≤ (3 * M / 2) * ‖s‖ ^ 2 + deltaH * ‖s‖ + deltaG
    have hself := CertifiedATS.gradient_derivative_selfadjoint f hC2 z
    have hsym : ‖H - CertifiedATS.sympart Ht‖ ≤ deltaH := by
      rw [norm_sub_rev]
      exact (CertifiedATS.sympart_error_bound Ht H hself).trans hHt
    have hsymnorm := ((H - CertifiedATS.sympart Ht).le_opNorm s).trans
      (mul_le_mul_of_nonneg_right hsym (norm_nonneg s))
    let R := gradient f (z + s) - gradient f z - H s
    have hR := RobustAHPE.gradient_taylor_remainder f hC2 M hM hH z s
    change ‖R‖ ≤ M / 2 * ‖s‖ ^ 2 at hR
    have hzero : v + CertifiedATS.sympart Ht s + (M * ‖s‖) • s = 0 := by
      convert! hm.1 using 1 <;> ring
    have he : gradient f (z + s) = R + (gradient f z - v) + (H - CertifiedATS.sympart Ht) s - (M * ‖s‖) • s := by
      calc
        _ = gradient f (z + s) - (v + CertifiedATS.sympart Ht s + (M * ‖s‖) • s) := by rw [hzero, sub_zero]
        _ = _ := by simp only [R, sub_apply]; module
    have hn1 := norm_sub_le (R + (gradient f z - v) + (H - CertifiedATS.sympart Ht) s) ((M * ‖s‖) • s)
    have hn2 := norm_add_le (R + (gradient f z - v)) ((H - CertifiedATS.sympart Ht) s)
    have hn3 := norm_add_le R (gradient f z - v)
    have hsmul : ‖(M * ‖s‖) • s‖ = M * ‖s‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM.le (norm_nonneg _))]
      ring
    rw [← he, hsmul] at hn1
    nlinarith only [hn1, hn2, hn3, hR, hg, hsymnorm]

theorem nonterminal_scalar_decrease (M eps r q Gnew Fchange : ℝ)
    (hM : 0 < M) (heps : 0 < eps) (hr : 0 ≤ r) (hq : 0 ≤ q) (hqsq : q ^ 2 = M * eps)
    (hnew : eps / 3 < Gnew)
    (hgrad : Gnew ≤ (3 * M / 2) * r ^ 2 + (q / 1024) * r + eps / 1024)
    (hchange : Fchange ≤ -(M / 3) * r ^ 3 + (eps / 1024) * r + (q / 1024) / 2 * r ^ 2) :
    eps / 16 ≤ M * r ^ 2 ∧ Fchange ≤ -(M / 4) * r ^ 3 := by
  have hyoung : 2 * r * q ≤ M * r ^ 2 + eps := by
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith only [sq_nonneg (M * r - q), hqsq]
  have hradius : eps / 16 ≤ M * r ^ 2 := by
    nlinarith only [hgrad, hyoung, hnew, heps]
  have hMmul := mul_le_mul_of_nonneg_left hradius hM.le
  have hqr : q ≤ 4 * M * r := by
    nlinarith only [hMmul, hqsq, hq, mul_nonneg hM.le hr]
  have hepsr := mul_le_mul_of_nonneg_right hradius hr
  have hqrr := mul_le_mul_of_nonneg_right hqr (sq_nonneg r)
  refine ⟨hradius, ?_⟩
  nlinarith only [hchange, hepsr, hqrr, mul_nonneg hM.le (pow_nonneg hr 3)]

end OriginalBorelOuterCubic


open OriginalBorelOuterCubic



namespace OriginalBorelOuterCubicSeparateErrors

open OriginalBetaATSTrial (Answer GetterProgram execute)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section

def tolerance (M eps : ℝ) : ℝ := min (eps / 1024) (Real.sqrt (M * eps) / 1024)
def stepRadius (M eps : ℝ) : ℝ := Real.sqrt (eps / (16 * M))
def stepCharge (M eps : ℝ) : ℝ := M / 4 * stepRadius M eps ^ 3

structure CubicOutput (E : Type*) where
  point : E
  success : Bool
  moves : ℕ
  charged : ℕ
  cubicSteps : ℝ

def appendCharged (s : E) (out : CubicOutput E) : CubicOutput E :=
  ⟨out.point, out.success, out.moves + 1, out.charged + 1, ‖s‖ ^ 3 + out.cubicSteps⟩

def loop (M eps : ℝ) : ℕ → E → Answer E → GetterProgram (E × ℝ) (Answer E) (CubicOutput E)
  | 0, x, _ => .pure ⟨x, false, 0, 0, 0⟩
  | n + 1, x, a =>
      if ‖a.grad‖ ≤ eps / 2 then .pure ⟨x, true, 0, 0, 0⟩
      else
        let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
        let y := x + s
        .ask (y, tolerance M eps) (fun ay =>
          if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
          else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))

def program (M eps : ℝ) (n : ℕ) (start : E) : GetterProgram (E × ℝ) (Answer E) (CubicOutput E) :=
  .ask (start, tolerance M eps) (fun a => loop M eps n start a)

theorem radius_properties (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    0 < tolerance M eps ∧ 0 < stepRadius M eps ∧
      M * stepRadius M eps ^ 2 = eps / 16 ∧ 0 < stepCharge M eps := by
  have ht : 0 < tolerance M eps := by unfold tolerance; positivity
  have hr : 0 < stepRadius M eps := by unfold stepRadius; positivity
  have hs := Real.sq_sqrt (by positivity : 0 ≤ eps / (16 * M))
  have hid : M * stepRadius M eps ^ 2 = eps / 16 := by
    unfold stepRadius
    rw [hs]
    field_simp
  exact ⟨ht, hr, hid, by unfold stepCharge; positivity⟩

def Accurate (f : E → ℝ) (M eps : ℝ) (x : E) (a : Answer E) : Prop :=
  ‖a.grad - gradient f x‖ ≤ eps / 1024 ∧
    ‖a.hess - fderiv ℝ (gradient f) x‖ ≤ Real.sqrt (M * eps) / 1024

theorem accurate_stop (f : E → ℝ) (M eps : ℝ) (heps : 0 < eps) (x : E) (a : Answer E)
    (ha : Accurate f M eps x a) (hstop : ‖a.grad‖ ≤ eps / 2) : ‖gradient f x‖ ≤ eps := by
  have he : ‖a.grad - gradient f x‖ ≤ eps / 1024 := ha.1
  have ht := norm_sub_le a.grad (a.grad - gradient f x)
  have hid : a.grad - (a.grad - gradient f x) = gradient f x := by abel
  rw [hid] at ht
  linarith only [ht, he, hstop, heps]

theorem accurate_nonterminal (f : E → ℝ) (M eps : ℝ) (heps : 0 < eps) (x : E) (a : Answer E)
    (ha : Accurate f M eps x a) (hstop : ¬ ‖a.grad‖ ≤ eps / 2) : eps / 3 < ‖gradient f x‖ := by
  have he : ‖a.grad - gradient f x‖ ≤ eps / 1024 := ha.1
  have ht := norm_add_le (a.grad - gradient f x) (gradient f x)
  have hid : (a.grad - gradient f x) + gradient f x = a.grad := by abel
  rw [hid] at ht
  linarith only [ht, he, lt_of_not_ge hstop, heps]

theorem large_radius_scalar_decrease (M eps r q Fchange : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hqsq : q ^ 2 = M * eps)
    (hradius : eps / 16 ≤ M * r ^ 2)
    (hchange : Fchange ≤ -(M / 3) * r ^ 3 + (eps / 1024) * r + (q / 1024) / 2 * r ^ 2) :
    Fchange ≤ -(M / 4) * r ^ 3 := by
  have hMmul := mul_le_mul_of_nonneg_left hradius hM.le
  have hqr : q ≤ 4 * M * r := by
    nlinarith only [hMmul, hqsq, mul_nonneg hM.le hr]
  have hepsr := mul_le_mul_of_nonneg_right hradius hr
  have hqrr := mul_le_mul_of_nonneg_right hqr (sq_nonneg r)
  nlinarith only [hchange, hepsr, hqrr, mul_nonneg hM.le (pow_nonneg hr 3)]

theorem actual_step_radius_and_descent
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (x : E) (a : Answer E) (ha : Accurate f M eps x a) :
    let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
    (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ f x - f (x + s)) ∧
    (∀ ay : Answer E, Accurate f M eps (x + s) ay → ¬ ‖ay.grad‖ ≤ eps / 2 →
      stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ f x - f (x + s)) := by
  dsimp only
  let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
  have hp := radius_properties M eps hM heps
  have hs := OriginalBorelOuterCubic.inexact_step_bounds f hC2 M hM hH x a.grad a.hess (eps / 1024) (Real.sqrt (M * eps) / 1024)
    (ha.1) ha.2
  have hqsq := Real.sq_sqrt (by positivity : 0 ≤ M * eps)
  have hq : 0 ≤ Real.sqrt (M * eps) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · intro hr
    have hsq := (sq_le_sq₀ hp.2.1.le (norm_nonneg s)).mpr hr
    have hm := mul_le_mul_of_nonneg_left hsq hM.le
    have hradius : eps / 16 ≤ M * ‖s‖ ^ 2 := by linarith only [hm, hp.2.2.1]
    have hd := large_radius_scalar_decrease M eps ‖s‖ (Real.sqrt (M * eps)) (f (x + s) - f x)
      hM (norm_nonneg _) hqsq hradius hs.1
    linarith only [hd]
  · intro ay hay haway
    have hlarge := accurate_nonterminal f M eps heps (x + s) ay hay haway
    have hscalar := OriginalBorelOuterCubic.nonterminal_scalar_decrease M eps ‖s‖ (Real.sqrt (M * eps))
      ‖gradient f (x + s)‖ (f (x + s) - f x) hM heps (norm_nonneg _) hq hqsq hlarge hs.2 hs.1
    have hsq : stepRadius M eps ^ 2 ≤ ‖s‖ ^ 2 := by
      apply (mul_le_mul_iff_right₀ hM).mp
      linarith only [hp.2.2.1, hscalar.1]
    exact ⟨(sq_le_sq₀ hp.2.1.le (norm_nonneg s)).mp hsq, by linarith only [hscalar.2]⟩

end
end OriginalBorelOuterCubicSeparateErrors




namespace OriginalBorelOuterCubicSeparateErrors

open OriginalBetaATSTrial (Answer GetterProgram execute)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

def LoopSpec (f : E → ℝ) (M eps lower : ℝ) (n : ℕ) (x : E) (run : CubicOutput E × ℕ) : Prop :=
  stepCharge M eps * (run.1.charged : ℝ) ≤ f x - lower ∧
  M / 4 * run.1.cubicSteps ≤ f x - lower + stepCharge M eps ∧
  run.1.moves ≤ run.1.charged + 1 ∧
  (run.1.success = true → ‖gradient f run.1.point‖ ≤ eps) ∧
  (run.1.success = false → run.1.charged = n) ∧ run.2 = run.1.moves

theorem actual_cubic_loop_spec
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (n : ℕ) (x : E) (a : Answer E) (ha : Accurate f M eps x a) :
    LoopSpec f M eps lower n x (execute getter (loop M eps n x a)) := by
  have hp := radius_properties M eps hM heps
  have hradius0 := hp.2.1.le
  induction n generalizing x a with
  | zero =>
      simp only [loop, execute, LoopSpec]
      refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
        by simpa only [mul_zero] using add_nonneg (sub_nonneg.mpr (hbelow x)) hp.2.2.2.le,
        by omega, ?_, fun _ => by trivial, by trivial⟩
      intro hf
      cases hf
  | succ n ih =>
      by_cases hstop : ‖a.grad‖ ≤ eps / 2
      · rw [loop, if_pos hstop]
        simp only [execute, LoopSpec]
        refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
          by simpa only [mul_zero] using add_nonneg (sub_nonneg.mpr (hbelow x)) hp.2.2.2.le,
          by omega, fun _ => accurate_stop f M eps heps x a ha hstop, ?_, by trivial⟩
        intro hf
        cases hf
      · let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
        let y := x + s
        let ay := getter (y, tolerance M eps)
        have hay : Accurate f M eps y ay := hvalid y
        have hstep := actual_step_radius_and_descent f hC2 M eps hM heps hH x a ha
        change (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ f x - f y) ∧
          (∀ ay : Answer E, Accurate f M eps y ay → ¬ ‖ay.grad‖ ≤ eps / 2 →
            stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ f x - f y) at hstep
        rw [loop, if_neg hstop]
        change LoopSpec f M eps lower (n + 1) x
          (execute getter (.ask (y, tolerance M eps) (fun ay =>
            if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))))
        simp only [execute]
        change LoopSpec f M eps lower (n + 1) x
          ((execute getter (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))).1,
           (execute getter (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))).2 + 1)
        by_cases hnextstop : ‖ay.grad‖ ≤ eps / 2
        · have hbudget : M / 4 * ‖s‖ ^ 3 ≤ f x - lower + stepCharge M eps := by
            by_cases hr : stepRadius M eps ≤ ‖s‖
            · have hd := hstep.1 hr
              linarith only [hd, hbelow y, hp.2.2.2]
            · have hrle : ‖s‖ ≤ stepRadius M eps := (lt_of_not_ge hr).le
              have hcube : ‖s‖ ^ 3 ≤ stepRadius M eps ^ 3 := by gcongr
              have hh := mul_le_mul_of_nonneg_left hcube (by positivity : 0 ≤ M / 4)
              change M / 4 * ‖s‖ ^ 3 ≤ f x - lower + M / 4 * stepRadius M eps ^ 3
              linarith only [hh, hbelow x]
          simp only [if_pos hnextstop, execute, LoopSpec]
          refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
            hbudget, by omega, fun _ => accurate_stop f M eps heps y ay hay hnextstop, ?_, by trivial⟩
          intro hf
          cases hf
        · have hd := hstep.2 ay hay hnextstop
          have hradius := hd.1
          have hcube : stepRadius M eps ^ 3 ≤ ‖s‖ ^ 3 := by gcongr
          have hcharge : stepCharge M eps ≤ M / 4 * ‖s‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hcube (by positivity)
          have hi := ih y ay hay
          simp only [LoopSpec] at hi
          simp only [if_neg hnextstop, FangqingGetterComposition.execute_map,
            LoopSpec, appendCharged, Nat.cast_add, Nat.cast_one]
          refine ⟨by nlinarith only [hi.1, hd.2, hcharge],
            by nlinarith only [hi.2.1, hd.2], ?_, hi.2.2.2.1, ?_, ?_⟩
          · have hh := hi.2.2.1
            omega
          · intro hf
            have hh := hi.2.2.2.2.1 hf
            omega
          · have hh := hi.2.2.2.2.2
            omega

noncomputable def fuel (Delta M eps : ℝ) : ℕ := Nat.ceil (Delta / stepCharge M eps) + 1

theorem actual_finite_cubic_termination
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower Delta : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (start : E) (hgap : f start - lower ≤ Delta) :
    let run := execute getter (program M eps (fuel Delta M eps) start)
    run.1.success = true ∧ ‖gradient f run.1.point‖ ≤ eps ∧
      (run.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
      run.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧
      (run.2 : ℝ) ≤ 2 + Delta / stepCharge M eps := by
  dsimp only
  let a := getter (start, tolerance M eps)
  let rest := execute getter (loop M eps (fuel Delta M eps) start a)
  have hp := radius_properties M eps hM heps
  have hs := actual_cubic_loop_spec f hC2 M eps lower hM heps hH hbelow getter hvalid
    (fuel Delta M eps) start a (hvalid start)
  change LoopSpec f M eps lower (fuel Delta M eps) start rest at hs
  dsimp only [LoopSpec] at hs
  have hc : (rest.1.charged : ℝ) ≤ Delta / stepCharge M eps :=
    (le_div_iff₀ hp.2.2.2).mpr (by nlinarith only [hs.1, hgap])
  have hsuccess : rest.1.success = true := by
    cases hb : rest.1.success with
    | true => rfl
    | false =>
        have hn := hs.2.2.2.2.1 hb
        rw [hn] at hc
        have hceil : Delta / stepCharge M eps ≤ (Nat.ceil (Delta / stepCharge M eps) : ℝ) := Nat.le_ceil _
        unfold fuel at hc
        push_cast at hc
        linarith only [hc, hceil]
  have hmoves : (rest.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps := by
    have hh : (rest.1.moves : ℝ) ≤ (rest.1.charged : ℝ) + 1 := by exact_mod_cast hs.2.2.1
    linarith only [hh, hc]
  have hcubic : rest.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < M / 4)).mp
    have hid : M / 4 * (4 * Delta / M + stepRadius M eps ^ 3) = Delta + stepCharge M eps := by
      unfold stepCharge
      field_simp <;> ring
    rw [hid]
    nlinarith only [hs.2.1, hgap]
  change rest.1.success = true ∧ ‖gradient f rest.1.point‖ ≤ eps ∧
    (rest.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
    rest.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧ ((rest.2 + 1 : ℕ) : ℝ) ≤ _
  refine ⟨hsuccess, hs.2.2.2.1 hsuccess, hmoves, hcubic, ?_⟩
  rw [hs.2.2.2.2.2]
  push_cast
  linarith only [hmoves]

end OriginalBorelOuterCubicSeparateErrors




namespace OriginalBorelOuterCubicSeparateErrors

theorem radius_and_charge_identities (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    stepRadius M eps ^ 3 = eps ^ (3 / 2 : ℝ) / (64 * M * Real.sqrt M) ∧
      stepCharge M eps = eps ^ (3 / 2 : ℝ) / (256 * Real.sqrt M) := by
  have hr : stepRadius M eps = Real.sqrt eps / (4 * Real.sqrt M) := by
    unfold stepRadius
    rw [Real.sqrt_div heps.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have he3 : Real.sqrt eps ^ 3 = eps * Real.sqrt eps := by rw [pow_succ, Real.sq_sqrt heps.le]
  have hM3 : Real.sqrt M ^ 3 = M * Real.sqrt M := by rw [pow_succ, Real.sq_sqrt hM.le]
  have hepow : eps ^ (3 / 2 : ℝ) = eps * Real.sqrt eps := by
    calc
      _ = eps ^ (1 + 1 / 2 : ℝ) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add heps, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hcube : stepRadius M eps ^ 3 = eps ^ (3 / 2 : ℝ) / (64 * M * Real.sqrt M) := by
    rw [hr, div_pow, mul_pow, he3, hM3, hepow]
    norm_num
    ring
  refine ⟨hcube, ?_⟩
  unfold stepCharge
  rw [hcube]
  field_simp [ne_of_gt hM, ne_of_gt (Real.sqrt_pos.mpr hM)]
  <;> ring

theorem reciprocal_charge_identity (Delta M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    Delta / stepCharge M eps = 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) := by
  rw [(radius_and_charge_identities M eps hM heps).2, div_div_eq_mul_div]
  ring

noncomputable def epsilonThreshold (Delta M : ℝ) : ℝ := (Delta * Real.sqrt M) ^ (2 / 3 : ℝ)

theorem epsilon_threshold_properties (Delta M eps : ℝ) (hDelta : 0 < Delta) (hM : 0 < M)
    (heps : 0 < eps) (hsmall : eps ≤ epsilonThreshold Delta M) :
    0 < epsilonThreshold Delta M ∧ eps ^ (3 / 2 : ℝ) ≤ Delta * Real.sqrt M := by
  have hx : 0 < Delta * Real.sqrt M := by positivity
  have hpos : 0 < epsilonThreshold Delta M := by unfold epsilonThreshold; positivity
  have hp := Real.rpow_le_rpow heps.le hsmall (by norm_num : (0 : ℝ) ≤ 3 / 2)
  change eps ^ (3 / 2 : ℝ) ≤ ((Delta * Real.sqrt M) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) at hp
  rw [← Real.rpow_mul hx.le] at hp
  norm_num only [show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one] at hp
  exact ⟨hpos, hp⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

open OriginalBetaATSTrial (Answer execute)

theorem cubic_asymptotic_rate_and_full_step_budget
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower Delta : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (start : E) (hgap : f start - lower ≤ Delta)
    (hsmall : eps ^ (3 / 2 : ℝ) ≤ Delta * Real.sqrt M) :
    let run := execute getter (program M eps (fuel Delta M eps) start)
    ‖gradient f run.1.point‖ ≤ eps ∧
      (run.1.moves : ℝ) ≤ 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) ∧
      run.1.cubicSteps ≤ 5 * Delta / M ∧
      (run.2 : ℝ) ≤ 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) := by
  dsimp only
  have hDelta : 0 ≤ Delta := by linarith only [hgap, hbelow start]
  have hpow : 0 < eps ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos heps _
  have hs := actual_finite_cubic_termination f hC2 M eps lower Delta hM heps hH hbelow getter hvalid start hgap
  have hrate : 1 ≤ Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) :=
    (le_div_iff₀ hpow).mpr (by simpa only [one_mul] using hsmall)
  let t := Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ)
  change 1 ≤ t at hrate
  rw [reciprocal_charge_identity Delta M eps hM heps] at hs
  have hcube : stepRadius M eps ^ 3 ≤ Delta / (64 * M) := by
    rw [(radius_and_charge_identities M eps hM heps).1]
    calc
      _ ≤ (Delta * Real.sqrt M) / (64 * M * Real.sqrt M) :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ = _ := by field_simp [ne_of_gt (Real.sqrt_pos.mpr hM)]
  refine ⟨hs.2.1, ?_, ?_, ?_⟩
  · have hh := hs.2.2.1
    rw [show 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 256 * t by dsimp [t]; ring] at hh
    rw [show 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 512 * t by dsimp [t]; ring]
    nlinarith only [hh, hrate]
  · have hh := hs.2.2.2.1
    have hn : 0 ≤ Delta / M := by positivity
    rw [show 4 * Delta / M = 4 * (Delta / M) by ring] at hh
    rw [show Delta / (64 * M) = (Delta / M) / 64 by ring] at hcube
    rw [show 5 * Delta / M = 5 * (Delta / M) by ring]
    nlinarith only [hh, hcube, hn]
  · have hh := hs.2.2.2.2
    rw [show 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 256 * t by dsimp [t]; ring] at hh
    rw [show 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 512 * t by dsimp [t]; ring]
    nlinarith only [hh, hrate]

end OriginalBorelOuterCubicSeparateErrors


namespace OriginalBorelStatefulEnvelopeCubic

open OriginalBorelOuterCubic OriginalBorelOuterCubicSeparateErrors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section
set_option maxHeartbeats 3000000

/-- Every actual cubic step increases the value by at most one explicit terminal
charge. Large steps decrease it. This controls the genuine terminal query's envelope
gap without invoking the refuted unconditional all-step cube budget. -/
theorem actual_step_value_upper
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (x : E) (a : OriginalBetaATSTrial.Answer E) (ha : Accurate f M eps x a) :
    let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
    f (x + s) ≤ f x + stepCharge M eps := by
  let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
  let R := stepRadius M eps
  have hp := radius_properties M eps hM heps
  have hcharge : 0 ≤ stepCharge M eps := hp.2.2.2.le
  by_cases hlarge : R ≤ ‖s‖
  · have hd := (actual_step_radius_and_descent f hC2 M eps hM heps hH x a ha).1 hlarge
    have hnon : 0 ≤ M / 4 * ‖s‖ ^ 3 := by positivity
    change f (x + s) ≤ f x + _
    linarith only [hd, hnon, hcharge]
  · have hr : ‖s‖ ≤ R := (lt_of_not_ge hlarge).le
    have hR : 0 < R := hp.2.1
    have hRsq : M * R ^ 2 = eps / 16 := hp.2.2.1
    have hq0 := Real.sqrt_nonneg (M * eps)
    have hqsq := Real.sq_sqrt (show 0 ≤ M * eps by positivity)
    have hQ : Real.sqrt (M * eps) = 4 * M * R := by
      have hh := congrArg (fun t : ℝ => 16 * M * t) hRsq
      have hh' : (4 * M * R) ^ 2 = M * eps := by nlinarith only [hh]
      have hMR : 0 < 4 * M * R := by positivity
      nlinarith only [hh', hqsq, hq0, hMR]
    have hEps : eps = 16 * M * R ^ 2 := by linarith only [hRsq]
    have herr : eps / 1024 * R + (Real.sqrt (M * eps) / 1024) / 2 * R ^ 2 ≤ stepCharge M eps := by
      have heq : eps / 1024 * R + (Real.sqrt (M * eps) / 1024) / 2 * R ^ 2 =
          (9 / 512 : ℝ) * M * R ^ 3 := by rw [hQ, hEps]; ring
      rw [heq]
      change (9 / 512 : ℝ) * M * R ^ 3 ≤ M / 4 * R ^ 3
      have hn : 0 ≤ M * R ^ 3 := by positivity
      nlinarith only [hn]
    have hs := (OriginalBorelOuterCubic.inexact_step_bounds f hC2 M hM hH x a.grad a.hess (eps / 1024)
      (Real.sqrt (M * eps) / 1024) ha.1 ha.2).1
    have hlin := mul_le_mul_of_nonneg_left hr (show 0 ≤ eps / 1024 by positivity)
    have hsq := pow_le_pow_left₀ (norm_nonneg s) hr 2
    have hquad := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ (Real.sqrt (M * eps) / 1024) / 2 by positivity)
    have hcube : 0 ≤ M * ‖s‖ ^ 3 := by positivity
    change f (x + s) ≤ f x + _
    change f (x + s) - f x ≤ -(M / 3) * ‖s‖ ^ 3 + eps / 1024 * ‖s‖ +
      (Real.sqrt (M * eps) / 1024) / 2 * ‖s‖ ^ 2 at hs
    nlinarith only [hs, hlin, hquad, herr, hcube]

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalEnvelopeOracleProgram
open OriginalBorelOuterCubic OriginalBorelOuterCubicSeparateErrors

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def estimateProgram (mu L rho D tau : ℝ) (x : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Estimate E F) :=
  OriginalEnvelopeOracleProgram.program L x (OriginalMinimumWarmSolver.program mu L rho D tau x x yin)

def asAnswer (a : Estimate E F) : Answer E := ⟨a.grad, a.hess⟩

theorem actual_estimate
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (estimateProgram mu L rho D tau x yin)
    ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
    ‖run.1.grad - gradient (saddleEnvelope (JointSliceRegularity.curry J) L) x‖ ≤ 2 * L * tau ∧
    ‖run.1.hess - fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x‖ ≤
      4 * rho * (1 + L / mu) ^ 2 * tau ∧
    (run.2 : ℝ) ≤ (1 + min (Real.sqrt (L / mu)) ((rho * D / mu) ^ (2 / 7 : ℝ))) *
      OriginalMinimumWarmSolver.logFactor J mu L rho D tau x x yin + 1 := by
  let p := OriginalMinimumWarmSolver.program mu L rho D tau x x yin
  let w := (execute (OriginalDualOracleProgram.actualOracle J) p).1
  have hw := OriginalMinimumWarmSolver.actual_minimum_warm_solver J mu L rho D tau
    hmu hLmu hrho htau hC2 hLip hHess hsc x x yin hwarm
  have he := OriginalEnvelopeOracle.envelope_oracle_from_joint_negative_slice J L mu rho
    (hmu.trans_le hLmu) hmu hrho hC2 hsc hLip hHess x w tau hw.1
  unfold estimateProgram
  rw [OriginalEnvelopeOracleProgram.actual_execution]
  refine ⟨hw.1, he.1, he.2, ?_⟩
  simp only [Nat.cast_add, Nat.cast_one]
  exact add_le_add hw.2 (le_refl (1 : ℝ))

structure Result (E F : Type*) where
  point : E
  saddle : Joint E F
  success : Bool
  charged : ℕ
  moves : List (OriginalStatefulEnvelopeGD.Move E F)

def cubedMovement (moves : List (OriginalStatefulEnvelopeGD.Move E F)) : ℝ :=
  (moves.map (fun m => ‖m.next - m.previous‖ ^ 3)).sum

def appendCharged (m : OriginalStatefulEnvelopeGD.Move E F) (out : Result E F) : Result E F :=
  { out with charged := out.charged + 1, moves := m :: out.moves }

/-- Actual cubic execution with a previous returned saddle kept as inner warm state. -/
def loop (mu L rho tau M eps : ℝ) : ℕ → E → Estimate E F →
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F)
  | 0, x, a => .pure ⟨x, a.saddle, false, 0, []⟩
  | n + 1, x, a =>
      if ‖a.grad‖ ≤ eps / 2 then .pure ⟨x, a.saddle, true, 0, []⟩
      else
        let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
        let y := x + s
        let D := tau + 2 * Real.sqrt (L / mu) * ‖s‖
        let m : OriginalStatefulEnvelopeGD.Move E F := ⟨x, y, a.saddle.snd, D⟩
        bind (estimateProgram mu L rho D tau y a.saddle.snd) (fun ay =>
          if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
          else map (appendCharged m) (loop mu L rho tau M eps n y ay))

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalEnvelopeOracleProgram
open OriginalBorelOuterCubic OriginalBorelOuterCubicSeparateErrors

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

structure LoopSpec (J : Joint E F → ℝ) (mu L rho tau M eps lower : ℝ)
    (n : ℕ) (x : E) (run : Result E F × ℕ) : Prop where
  close : ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L run.1.point‖ ≤ tau
  charged_budget : stepCharge M eps * (run.1.charged : ℝ) ≤ saddleEnvelope (JointSliceRegularity.curry J) L x - lower
  cube_budget : M / 4 * cubedMovement run.1.moves ≤ saddleEnvelope (JointSliceRegularity.curry J) L x - lower + stepCharge M eps
  length_bound : run.1.moves.length ≤ run.1.charged + 1
  terminal : run.1.success = true → ‖gradient (saddleEnvelope (JointSliceRegularity.curry J) L) run.1.point‖ ≤ eps
  exhausted : run.1.success = false → run.1.charged = n
  original_cost : (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ)
  value_upper : saddleEnvelope (JointSliceRegularity.curry J) L run.1.point ≤ saddleEnvelope (JointSliceRegularity.curry J) L x + stepCharge M eps
  legal_moves : ∀ m ∈ run.1.moves,
    ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
    m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
    saddleEnvelope (JointSliceRegularity.curry J) L m.previous ≤ saddleEnvelope (JointSliceRegularity.curry J) L x ∧
    saddleEnvelope (JointSliceRegularity.curry J) L m.next ≤ saddleEnvelope (JointSliceRegularity.curry J) L x + stepCharge M eps

theorem actual_loop_spec
    (J : Joint E F → ℝ) (mu L rho tau M eps lower : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau) (hM : 0 < M) (heps : 0 < eps)
    (htolG : 2 * L * tau ≤ eps / 1024)
    (htolH : 4 * rho * (1 + L / mu) ^ 2 * tau ≤ Real.sqrt (M * eps) / 1024)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hEHess : ∀ x y : E,
      ‖fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x -
        fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ saddleEnvelope (JointSliceRegularity.curry J) L x)
    (n : ℕ) (x : E) (a : Estimate E F)
    (hclose : ‖a.saddle - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau)
    (ha : Accurate (saddleEnvelope (JointSliceRegularity.curry J) L) M eps x (asAnswer a)) :
    LoopSpec J mu L rho tau M eps lower n x
      (execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps n x a)) := by
  let Ef := saddleEnvelope (JointSliceRegularity.curry J) L
  have hL : 0 < L := hmu.trans_le hLmu
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hEC2 : ContDiff ℝ 2 Ef := OriginalEnvelopeRegularity.actual_envelope_contDiff2 J L mu hL hmu hC2 hsc hLip
  have hp := radius_properties M eps hM heps
  have hcharge : 0 < stepCharge M eps := hp.2.2.2
  induction n generalizing x a with
  | zero =>
      rw [loop]
      simp only [execute]
      refine ⟨hclose, ?_, ?_, by norm_num, ?_, fun _ => rfl, ?_, ?_, ?_⟩
      · simp only [Nat.cast_zero, mul_zero]
        change 0 ≤ Ef x - lower
        linarith only [hbelow x]
      · change M / 4 * (0 : ℝ) ≤ Ef x - lower + stepCharge M eps
        linarith only [hbelow x, hcharge]
      · intro hh
        cases hh
      · simp [OriginalStatefulEnvelopeGD.costSum]
      · change Ef x ≤ Ef x + stepCharge M eps
        linarith only [hcharge]
      · intro m hm
        cases hm
  | succ n ih =>
      by_cases hstop : ‖a.grad‖ ≤ eps / 2
      · rw [loop, if_pos hstop]
        simp only [execute]
        refine ⟨hclose, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Nat.cast_zero, mul_zero]
          change 0 ≤ Ef x - lower
          linarith only [hbelow x]
        · change M / 4 * (0 : ℝ) ≤ Ef x - lower + stepCharge M eps
          linarith only [hbelow x, hcharge]
        · intro _
          exact accurate_stop Ef M eps heps x (asAnswer a) ha hstop
        · intro hh
          cases hh
        · simp [OriginalStatefulEnvelopeGD.costSum]
        · change Ef x ≤ Ef x + stepCharge M eps
          linarith only [hcharge]
        · intro m hm
          cases hm
      · let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
        let y := x + s
        let D := tau + 2 * Real.sqrt (L / mu) * ‖s‖
        let m : OriginalStatefulEnvelopeGD.Move E F := ⟨x, y, a.saddle.snd, D⟩
        let first := execute (OriginalDualOracleProgram.actualOracle J) (estimateProgram mu L rho D tau y a.saddle.snd)
        let ay := first.1
        have hs : y - x = s := by dsimp only [y]; abel
        have hprevious : ‖a.saddle.snd - vStar (JointSliceRegularity.curry J) L x‖ ≤ tau :=
          (WithLp.norm_snd_le E (a.saddle - zStar (JointSliceRegularity.curry J) L x)).trans hclose
        have hwarm : ‖a.saddle.snd - vStar (JointSliceRegularity.curry J) L y‖ ≤ D := by
          have hh := OriginalWarmAmortization.actual_warm_dual_distance J L mu hL hmu hJ hLip hsc x y a.saddle.snd tau hprevious
          simpa only [hs] using hh
        have hfirst := actual_estimate J mu L rho D tau hmu hLmu hrho htau hC2 hLip hHess hsc y a.saddle.snd hwarm
        have hayClose : ‖ay.saddle - zStar (JointSliceRegularity.curry J) L y‖ ≤ tau := hfirst.1
        have hay : Accurate Ef M eps y (asAnswer ay) :=
          ⟨hfirst.2.1.trans htolG, hfirst.2.2.1.trans htolH⟩
        have hfirstCost : (first.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.moveCost J mu L rho tau m + 1 := hfirst.2.2.2
        have hstep := actual_step_radius_and_descent Ef hEC2 M eps hM heps hEHess x (asAnswer a) ha
        change (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ Ef x - Ef y) ∧
          (∀ ay' : Answer E, Accurate Ef M eps y ay' → ¬ ‖ay'.grad‖ ≤ eps / 2 →
            stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ Ef x - Ef y) at hstep
        have hvalue : Ef y ≤ Ef x + stepCharge M eps := actual_step_value_upper Ef hEC2 M eps hM heps hEHess x (asAnswer a) ha
        by_cases hnext : ‖ay.grad‖ ≤ eps / 2
        · have hexec : execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps (n + 1) x a) =
              (⟨y, ay.saddle, true, 0, [m]⟩, first.2) := by
            simp only [loop, if_neg hstop, execute_bind]
            change ((execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).1,
              first.2 + (execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).2) = _
            rw [if_pos hnext]
            rfl

          have hbudget : M / 4 * ‖s‖ ^ 3 ≤ Ef x - lower + stepCharge M eps := by
            by_cases hlarge : stepRadius M eps ≤ ‖s‖
            · have hd := hstep.1 hlarge
              linarith only [hd, hbelow y, hcharge]
            · have hr : ‖s‖ ≤ stepRadius M eps := (lt_of_not_ge hlarge).le
              have hc : ‖s‖ ^ 3 ≤ stepRadius M eps ^ 3 := by gcongr
              have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ M / 4 by positivity)
              unfold stepCharge
              linarith only [hh, hbelow x]
          rw [hexec]
          refine ⟨hayClose, ?_, ?_, by norm_num, ?_, ?_, ?_, hvalue, ?_⟩
          · simp only [Nat.cast_zero, mul_zero]
            change 0 ≤ Ef x - lower
            linarith only [hbelow x]
          · change M / 4 * (‖y - x‖ ^ 3 + 0) ≤ Ef x - lower + stepCharge M eps
            simpa only [hs, add_zero] using hbudget
          · intro _
            exact accurate_stop Ef M eps heps y (asAnswer ay) hay hnext
          · intro hh
            cases hh
          · simpa only [OriginalStatefulEnvelopeGD.costSum, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, add_zero, List.length_singleton, Nat.cast_one] using hfirstCost
          · intro move hmem
            have he : move = m := List.mem_singleton.mp hmem
            subst move
            refine ⟨hwarm, ?_, le_refl _, hvalue⟩
            change D = tau + 2 * Real.sqrt (L / mu) * ‖y - x‖
            rw [hs]
        · let rest := execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps n y ay)
          have hrec := ih y ay hayClose hay
          change LoopSpec J mu L rho tau M eps lower n y rest at hrec
          have hd := hstep.2 (asAnswer ay) hay hnext
          have hc : stepRadius M eps ^ 3 ≤ ‖s‖ ^ 3 := by exact pow_le_pow_left₀ hp.2.1.le hd.1 3
          have hpaid : stepCharge M eps ≤ M / 4 * ‖s‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hc (show 0 ≤ M / 4 by positivity)
          have hdescent : Ef y ≤ Ef x := by
            have hn : 0 ≤ M / 4 * ‖s‖ ^ 3 := by positivity
            linarith only [hd.2, hn]
          have hexec : execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps (n + 1) x a) =
              (appendCharged m rest.1, first.2 + rest.2) := by
            simp only [loop, if_neg hstop, execute_bind]
            change ((execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).1,
              first.2 + (execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).2) = _
            rw [if_neg hnext, execute_map]
          rw [hexec]
          have hcube : cubedMovement (m :: rest.1.moves) = ‖s‖ ^ 3 + cubedMovement rest.1.moves := by
            simp only [cubedMovement, List.map_cons, List.sum_cons]
            change ‖y - x‖ ^ 3 + _ = _
            rw [hs]
          refine ⟨hrec.close, ?_, ?_, ?_, hrec.terminal, ?_, ?_, ?_, ?_⟩
          · change stepCharge M eps * ((rest.1.charged + 1 : ℕ) : ℝ) ≤ Ef x - lower
            push_cast
            have hh := hrec.charged_budget
            nlinarith only [hh, hd.2, hpaid]
          · change M / 4 * cubedMovement (m :: rest.1.moves) ≤ Ef x - lower + stepCharge M eps
            rw [hcube]
            have hh := hrec.cube_budget
            nlinarith only [hh, hd.2]
          · have hh := hrec.length_bound
            change (m :: rest.1.moves).length ≤ rest.1.charged + 1 + 1
            simp only [List.length_cons]
            omega
          · intro hh
            exact congrArg Nat.succ (hrec.exhausted hh)
          · change ((first.2 + rest.2 : ℕ) : ℝ) ≤ OriginalStatefulEnvelopeGD.costSum J mu L rho tau (m :: rest.1.moves) + ((m :: rest.1.moves).length : ℝ)
            simp only [Nat.cast_add, OriginalStatefulEnvelopeGD.costSum, List.map_cons, List.sum_cons,
              List.length_cons, Nat.cast_one]
            have hh := hrec.original_cost
            dsimp only [OriginalStatefulEnvelopeGD.costSum] at hh
            linarith only [hh, hfirstCost]
          · have hh := hrec.value_upper
            exact hh.trans (add_le_add hdescent le_rfl)
          · intro move hmem
            rcases List.mem_cons.mp hmem with he | he
            · subst move
              refine ⟨hwarm, ?_, le_refl _, ?_⟩
              · change D = tau + 2 * Real.sqrt (L / mu) * ‖y - x‖
                rw [hs]
              · exact hdescent.trans (le_add_of_nonneg_right hcharge.le)
            · obtain ⟨hlegal, hradius, hprev, hnext⟩ := hrec.legal_moves move he
              exact ⟨hlegal, hradius, hprev.trans hdescent, hnext.trans (add_le_add hdescent le_rfl)⟩

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalEnvelopeOracleProgram
open OriginalBorelOuterCubic OriginalBorelOuterCubicSeparateErrors

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def program (mu L rho D0 tau M eps Delta : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F) :=
  bind (estimateProgram mu L rho D0 tau start yin) (fun a =>
    loop mu L rho tau M eps (OriginalBorelOuterCubicSeparateErrors.fuel Delta M eps) start a)

/-- The complete stateful cubic execution halts. The extra terminal cube and its
slightly larger level set are retained explicitly, including when the gap is zero. -/
theorem actual_finite_termination_with_warm_trace
    (J : Joint E F → ℝ) (mu L rho D0 tau M eps Delta lower : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hM : 0 < M) (heps : 0 < eps)
    (htolG : 2 * L * tau ≤ eps / 1024)
    (htolH : 4 * rho * (1 + L / mu) ^ 2 * tau ≤ Real.sqrt (M * eps) / 1024)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hEHess : ∀ x y : E,
      ‖fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x -
        fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ saddleEnvelope (JointSliceRegularity.curry J) L x)
    (start : E) (yin : F)
    (hgap : saddleEnvelope (JointSliceRegularity.curry J) L start - lower ≤ Delta)
    (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L start‖ ≤ D0) :
    let run := execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D0 tau M eps Delta start yin)
    run.1.success = true ∧
    ‖gradient (saddleEnvelope (JointSliceRegularity.curry J) L) run.1.point‖ ≤ eps ∧
    ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L run.1.point‖ ≤ tau ∧
    (run.1.moves.length : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
    cubedMovement run.1.moves ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧
    (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin +
      1 + OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ) ∧
    (∀ m ∈ run.1.moves,
      ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
      m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
      saddleEnvelope (JointSliceRegularity.curry J) L m.previous - lower ≤ Delta ∧
      saddleEnvelope (JointSliceRegularity.curry J) L m.next - lower ≤ Delta + stepCharge M eps) := by
  let first := execute (OriginalDualOracleProgram.actualOracle J)
    (estimateProgram mu L rho D0 tau start yin)
  let n := OriginalBorelOuterCubicSeparateErrors.fuel Delta M eps
  let rest := execute (OriginalDualOracleProgram.actualOracle J)
    (loop mu L rho tau M eps n start first.1)
  have hp := radius_properties M eps hM heps
  have hcharge : 0 < stepCharge M eps := hp.2.2.2
  have hfirst := actual_estimate J mu L rho D0 tau hmu hLmu hrho htau hC2 hLip hHess hsc start yin hwarm
  have hclose : ‖first.1.saddle - zStar (JointSliceRegularity.curry J) L start‖ ≤ tau := hfirst.1
  have ha : Accurate (saddleEnvelope (JointSliceRegularity.curry J) L) M eps start (asAnswer first.1) :=
    ⟨hfirst.2.1.trans htolG, hfirst.2.2.1.trans htolH⟩
  have hcost0 : (first.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin + 1 := hfirst.2.2.2
  have hs := actual_loop_spec J mu L rho tau M eps lower hmu hLmu hrho htau hM heps htolG htolH
    hC2 hLip hHess hsc hEHess hbelow n start first.1 hclose ha
  change LoopSpec J mu L rho tau M eps lower n start rest at hs
  have hc : (rest.1.charged : ℝ) ≤ Delta / stepCharge M eps := by
    apply (le_div_iff₀ hcharge).mpr
    have hh := hs.charged_budget
    nlinarith only [hh, hgap]
  have hsuccess : rest.1.success = true := by
    cases hb : rest.1.success with
    | true => rfl
    | false =>
        have hcount := hs.exhausted hb
        rw [hcount] at hc
        dsimp [n, OriginalBorelOuterCubicSeparateErrors.fuel] at hc
        push_cast at hc
        have hceil := Nat.le_ceil (Delta / stepCharge M eps)
        linarith only [hc, hceil]
  have hlength : (rest.1.moves.length : ℝ) ≤ 1 + Delta / stepCharge M eps := by
    have hh : (rest.1.moves.length : ℝ) ≤ (rest.1.charged : ℝ) + 1 := by exact_mod_cast hs.length_bound
    linarith only [hc, hh]
  have hcubes : cubedMovement rest.1.moves ≤ 4 * Delta / M + stepRadius M eps ^ 3 := by
    have hh := hs.cube_budget
    have hm : M * (4 * Delta / M + stepRadius M eps ^ 3) = 4 * Delta + 4 * stepCharge M eps := by
      unfold stepCharge
      field_simp
      <;> ring
    have hmul : M * cubedMovement rest.1.moves ≤ M * (4 * Delta / M + stepRadius M eps ^ 3) := by
      nlinarith only [hh, hgap, hm]
    exact (mul_le_mul_iff_right₀ hM).mp hmul
  have hexec : execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D0 tau M eps Delta start yin) = (rest.1, first.2 + rest.2) := by
    simp only [program, execute_bind]
    rfl
  rw [hexec]
  refine ⟨hsuccess, hs.terminal hsuccess, hs.close, hlength, hcubes, ?_, ?_⟩
  · simp only [Nat.cast_add]
    have hh := hs.original_cost
    linarith only [hh, hcost0]
  · intro m hm
    obtain ⟨hw, hr, hp, hn⟩ := hs.legal_moves m hm
    exact ⟨hw, hr, by linarith only [hp, hgap], by linarith only [hn, hgap]⟩

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalBorelOuterCubicSeparateErrors

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

def curvature (mu L rho : ℝ) := 8 * rho * (1 + L / mu) ^ (3 / 2 : ℝ)

def callerTolerance (mu L rho eps : ℝ) :=
  min (eps / (4096 * L))
    (min (Real.sqrt (curvature mu L rho * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2))
      (min (mu / rho) (OriginalStatefulEnvelopeGD.callerTolerance mu L eps)))

def caller (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F) :=
  program mu L rho (Ry + (L / mu) * Real.sqrt (Delta / L)) (callerTolerance mu L rho eps)
    (curvature mu L rho) (eps / 2) Delta start yin

theorem actual_cubic_caller_from_original_inputs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let M := curvature mu L rho
    let tau := callerTolerance mu L rho eps
    let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.1.moves.length : ℝ) ≤ 1 + Delta / stepCharge M (eps / 2) ∧
    cubedMovement run.1.moves ≤ 4 * Delta / M + stepRadius M (eps / 2) ^ 3 ∧
    (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin + 1 +
      OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ) ∧
    (∀ m ∈ run.1.moves,
      ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
      m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
      OriginalDualResidualQueryBound.observedRadius J L m.next m.next m.warm ≤
        3 * (Real.sqrt ((Delta + stepCharge M (eps / 2)) / L) + m.radius)) := by
  let f := JointSliceRegularity.curry J
  let lower := sInf (Set.range (phi f))
  let tau := callerTolerance mu L rho eps
  let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  let M := curvature mu L rho
  have hM : 0 < M := by dsimp [M, curvature]; positivity
  have hratio : 0 < L / mu := by positivity
  have htau : 0 < tau := by
    have hsq : 0 < Real.sqrt (M * (eps / 2)) := Real.sqrt_pos.mpr (by positivity)
    have hgd : 0 < OriginalStatefulEnvelopeGD.callerTolerance mu L eps := by
      unfold OriginalStatefulEnvelopeGD.callerTolerance
      positivity
    change 0 < min (eps / (4096 * L))
      (min (Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2))
        (min (mu / rho) (OriginalStatefulEnvelopeGD.callerTolerance mu L eps)))
    positivity
  have htolG : 2 * L * tau ≤ (eps / 2) / 1024 := by
    have ht : tau ≤ eps / (4096 * L) := min_le_left _ _
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * L by positivity)
    have he : 2 * L * (eps / (4096 * L)) = (eps / 2) / 1024 := by field_simp; ring
    exact hh.trans_eq he
  have htolH : 4 * rho * (1 + L / mu) ^ 2 * tau ≤ Real.sqrt (M * (eps / 2)) / 1024 := by
    have ht : tau ≤ Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 4 * rho * (1 + L / mu) ^ 2 by positivity)
    have he : 4 * rho * (1 + L / mu) ^ 2 *
        (Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2)) = Real.sqrt (M * (eps / 2)) / 1024 := by
      field_simp
      <;> ring
    exact hh.trans_eq he
  have htoutput : tau ≤ OriginalStatefulEnvelopeGD.callerTolerance mu L eps :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdx := JointSliceRegularity.differentiable_x_slice J hJ
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y
  have hxy := fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v
  obtain ⟨hPhi, hweak⟩ := phi_regular_from_slices f L mu hL hmu hdx hdy hsc hxx hxy
  have hE := saddleEnvelope_eq_moreau f L mu hmu hsc hdy
  have hElower : ∀ x, lower ≤ saddleEnvelope f L x := by
    intro x
    rw [hE, MoreauTransfer.envelope_eq_prox_objective (phi f) L hL hPhi hweak]
    have hp := csInf_le hbelow (Set.mem_range_self (MoreauTransfer.prox (phi f) L x))
    unfold MoreauTransfer.objective
    have hn : 0 ≤ L * ‖MoreauTransfer.prox (phi f) L x - x‖ ^ 2 := by positivity
    change lower ≤ phi f (MoreauTransfer.prox (phi f) L x) + _
    linarith only [hp, hn]
  have hEgap : saddleEnvelope f L start - lower ≤ Delta := by
    have hh := MoreauTransfer.envelope_le_original (phi f) L hL hPhi hweak start
    rw [← hE] at hh
    linarith only [hh, hgap]
  have hinit := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry
    hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hEHess := (OriginalEnvelopeRegularity.envelope_regularity_from_joint_negative_slice
    J L mu rho hL hmu hrho.le hC2 hsc hLip hHess).2.2
  have hh := actual_finite_termination_with_warm_trace J mu L rho D0 tau M (eps / 2) Delta lower
    hmu hLmu hrho.le htau hM (by positivity) htolG htolH hC2 hLip hHess hsc hEHess hElower start yin hEgap hinit
  change run.1.success = true ∧ _ at hh
  rcases hh with ⟨htrue, hgradE, hclose, hcount, hcubes, hcost, htrace⟩
  change ‖gradient (saddleEnvelope f L) run.1.point‖ ≤ eps / 2 at hgradE
  have htransfer := exact_transfer_from_slices f L mu hL hmu hdx hdy hsc hxx hxy hbelow start Delta hgap
  have hPhiLip := OriginalStatefulEnvelopeGD.actual_phi_gradient_lipschitz J mu L hmu hL hC2 hLip hsc
  have hfirst : ‖run.1.saddle.fst - uStar f L run.1.point‖ ≤ tau := by
    exact (WithLp.norm_fst_le E (run.1.saddle - zStar f L run.1.point)).trans hclose
  have houtput : ‖gradient (phi f) run.1.saddle.fst‖ ≤ eps := by
    have hd := hPhiLip run.1.saddle.fst (uStar f L run.1.point)
    have hm := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ L * (1 + L / mu) by positivity)
    have hn := norm_le_norm_sub_add (gradient (phi f) run.1.saddle.fst)
      (gradient (phi f) (uStar f L run.1.point))
    change ‖gradient (phi f) run.1.saddle.fst - gradient (phi f) (uStar f L run.1.point)‖ ≤ _ at hd
    rw [← (htransfer.1 run.1.point).2] at hn hd
    have hmul := mul_le_mul_of_nonneg_left htoutput (show 0 ≤ L * (1 + L / mu) by positivity)
    have he : L * (1 + L / mu) * OriginalStatefulEnvelopeGD.callerTolerance mu L eps = eps / 128 := by
      unfold OriginalStatefulEnvelopeGD.callerTolerance
      field_simp
      <;> ring
    rw [he] at hmul
    linarith only [hd, hm, hn, hgradE, hmul, heps]
  refine ⟨htrue, houtput, hcount, hcubes, hcost, ?_⟩
  · intro m hm
    obtain ⟨hlegal, hradius, hprev, hnext⟩ := htrace m hm
    have hb := (OriginalOuterPrimalInitialization.standing_primal_residual_bound J L mu lower (Delta + stepCharge M (eps / 2)) m.radius
      hL hmu hC2 hLip hsc (fun u => csInf_le hbelow ⟨u, rfl⟩) m.next m.warm hnext hlegal).2.2
    exact ⟨hlegal, hradius, hb⟩


end
end OriginalBorelStatefulEnvelopeCubic


open scoped BigOperators
namespace OriginalBorelStatefulEnvelopeCubic
open OriginalStatefulEnvelopeGD
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
noncomputable section
set_option maxHeartbeats 4000000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def cubicPolynomialBound (mu L rho tau : ℝ) (moves : List (Move E F)) : ℝ :=
  (moves.length : ℝ) * (1 + (rho * tau / mu) ^ (2 / 7 : ℝ)) +
    (rho / mu * (2 * Real.sqrt (L / mu))) ^ (2 / 7 : ℝ) *
      (moves.length : ℝ) ^ (19 / 21 : ℝ) * cubedMovement moves ^ (2 / 21 : ℝ)

/-- Actual per-move costs are amortized over the actual physical step trace.
The finite maximum of log-factors is retained explicitly, rather than assumed to be
uniformly polylogarithmic. -/
theorem actual_cubic_cost_sum_holder_bound
    (J : Joint E F → ℝ) (mu L rho tau : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hrho : 0 ≤ rho) (htau : 0 ≤ tau) (moves : List (Move E F))
    (hradii : ∀ m ∈ moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖) :
    costSum J mu L rho tau moves ≤
      maximumLog J mu L rho tau moves * cubicPolynomialBound mu L rho tau moves := by
  let N := moves.length
  let step : Fin N → ℝ := fun i => ‖(moves.get i).next - (moves.get i).previous‖
  let radius : Fin N → ℝ := fun i => rho * (moves.get i).radius / mu
  have hradius : ∀ i : Fin N, 0 ≤ (moves.get i).radius := by
    intro i
    rw [hradii (moves.get i) (List.get_mem _ _)]
    positivity
  have hM : 0 ≤ maximumLog J mu L rho tau moves :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (maximum_log_positive J mu L rho tau moves)
  have hpoint : ∀ i : Fin N,
      moveCost J mu L rho tau (moves.get i) ≤
        maximumLog J mu L rho tau moves * (1 + radius i ^ (2 / 7 : ℝ)) := by
    intro i
    have hlog : moveLog J mu L rho tau (moves.get i) ≤ maximumLog J mu L rho tau moves := by
      exact List.le_max_of_le' 1 (List.mem_map.mpr ⟨moves.get i, List.get_mem _ _, rfl⟩) le_rfl
    have hscale : 0 ≤ 1 + min (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ)) := by
      have hp : 0 ≤ radius i := div_nonneg (mul_nonneg hrho (hradius i)) hmu.le
      exact add_nonneg zero_le_one (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg hp _))
    have ha := mul_le_mul_of_nonneg_left hlog hscale
    have hb := mul_le_mul_of_nonneg_left
      (add_le_add_left (min_le_right (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ))) 1) hM
    change (1 + min (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ))) *
      moveLog J mu L rho tau (moves.get i) ≤ _
    exact ha.trans (by nlinarith only [hb])
  have hholder := OriginalWarmAmortization.warm_cost_sum_from_cubed_steps
    (Finset.univ : Finset (Fin N)) step radius (rho * tau / mu)
    (rho / mu * (2 * Real.sqrt (L / mu))) (by positivity) (by positivity)
    (fun _ _ => norm_nonneg _) (fun i _ => div_nonneg (mul_nonneg hrho (hradius i)) hmu.le) (by
      intro i _
      have hi := hradii (moves.get i) (List.get_mem _ _)
      change rho * (moves.get i).radius / mu ≤ rho * tau / mu +
        rho / mu * (2 * Real.sqrt (L / mu)) * ‖(moves.get i).next - (moves.get i).previous‖
      rw [hi]
      ring_nf
      exact le_rfl)
  have hcubes : ∑ i : Fin N, step i ^ 3 = cubedMovement moves :=
    (list_sum_as_fin moves (fun m => ‖m.next - m.previous‖ ^ 3)).symm
  have hpoly : ∑ i : Fin N, (1 + radius i ^ (2 / 7 : ℝ)) ≤ cubicPolynomialBound mu L rho tau moves := by
    simpa only [Finset.card_univ, Fintype.card_fin, hcubes, N, cubicPolynomialBound] using hholder
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [← Finset.mul_sum] at hsum
  rw [costSum, list_sum_as_fin]
  exact hsum.trans (mul_le_mul_of_nonneg_left hpoly hM)


theorem cubed_movement_nonnegative (moves : List (Move E F)) : 0 ≤ cubedMovement moves := by
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
    positivity)

theorem one_step_cubed_le_total (moves : List (Move E F)) (m : Move E F) (hm : m ∈ moves) :
    ‖m.next - m.previous‖ ^ 3 ≤ cubedMovement moves := by
  induction moves with
  | nil => cases hm
  | cons head tail ih =>
      simp only [cubedMovement, List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hm with h | h
      · subst m
        exact le_add_of_nonneg_right (cubed_movement_nonnegative tail)
      · exact (ih h).trans (le_add_of_nonneg_left (by positivity))

theorem norm_le_one_add_cube (v : E) : ‖v‖ ≤ 1 + ‖v‖ ^ 3 := by
  by_cases h : ‖v‖ ≤ 1
  · have hc : 0 ≤ ‖v‖ ^ 3 := by positivity
    linarith only [h, hc]
  · have h1 : 1 ≤ ‖v‖ := (lt_of_not_ge h).le
    have hh := mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ ‖v‖ ^ 2 + ‖v‖ by positivity)
    nlinarith only [hh]

theorem cubic_warm_radii_uniform_bound (L mu tau B : ℝ)
    (moves : List (Move E F)) (hcubes : cubedMovement moves ≤ B)
    (hradii : ∀ m ∈ moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖) :
    ∀ m ∈ moves, m.radius ≤ tau + 2 * Real.sqrt (L / mu) * (1 + B) := by
  intro m hm
  have hstep := (one_step_cubed_le_total moves m hm).trans hcubes
  have hn := norm_le_one_add_cube (m.next - m.previous)
  have hh := mul_le_mul_of_nonneg_left (show ‖m.next - m.previous‖ ≤ 1 + B by linarith only [hn,hstep])
    (show 0 ≤ 2 * Real.sqrt (L / mu) by positivity)
  rw [hradii m hm]
  linarith only [hh]

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelCubicHolderNormalization

set_option maxHeartbeats 3000000

/-- The terminal cube is charged to the same `1 + gap / charge` factor as the
actual number of moves. No small-epsilon premise or unconditional cube-sum bound
is used. -/
theorem holder_with_terminal_budget
    (N C B R a b : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C) (hB : 0 < B) (hR : 0 < R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hNB : N ≤ B) (hCB : C ≤ B * R ^ 3)
    (ha1 : a ≤ 1) (hbR : b * R ≤ 1) :
    N * (1 + a ^ (2 / 7 : ℝ)) +
      b ^ (2 / 7 : ℝ) * N ^ (19 / 21 : ℝ) * C ^ (2 / 21 : ℝ) ≤ 3 * B := by
  have haPow : a ^ (2 / 7 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow ha ha1 (by norm_num : (0 : ℝ) ≤ 2 / 7)
  have hNPow := Real.rpow_le_rpow hN hNB (by norm_num : (0 : ℝ) ≤ 19 / 21)
  have hCPow := Real.rpow_le_rpow hC hCB (by norm_num : (0 : ℝ) ≤ 2 / 21)
  have hRPow : (R ^ 3) ^ (2 / 21 : ℝ) = R ^ (2 / 7 : ℝ) := by
    rw [← Real.rpow_natCast R 3, ← Real.rpow_mul hR.le]
    norm_num
  have hBPow : B ^ (19 / 21 : ℝ) * B ^ (2 / 21 : ℝ) = B := by
    rw [← Real.rpow_add hB]
    norm_num
  have hprod : b ^ (2 / 7 : ℝ) * N ^ (19 / 21 : ℝ) * C ^ (2 / 21 : ℝ) ≤ B := by
    have h1 := mul_le_mul_of_nonneg_left hNPow (Real.rpow_nonneg hb (2 / 7 : ℝ))
    have h2 := mul_le_mul h1 hCPow (Real.rpow_nonneg hC (2 / 21 : ℝ))
      (mul_nonneg (Real.rpow_nonneg hb _) (Real.rpow_nonneg hB.le _))
    have hid : b ^ (2 / 7 : ℝ) * B ^ (19 / 21 : ℝ) * (B * R ^ 3) ^ (2 / 21 : ℝ) =
        B * (b * R) ^ (2 / 7 : ℝ) := by
      rw [Real.mul_rpow hB.le (pow_nonneg hR.le 3), hRPow, Real.mul_rpow hb hR.le]
      calc
        _ = (B ^ (19 / 21 : ℝ) * B ^ (2 / 21 : ℝ)) *
            (b ^ (2 / 7 : ℝ) * R ^ (2 / 7 : ℝ)) := by ring
        _ = _ := by rw [hBPow]
    rw [hid] at h2
    have h3 : (b * R) ^ (2 / 7 : ℝ) ≤ 1 := by
      simpa using Real.rpow_le_rpow (mul_nonneg hb hR.le) hbR (by norm_num : (0 : ℝ) ≤ 2 / 7)
    exact h2.trans (by nlinarith only [mul_le_mul_of_nonneg_left h3 hB.le])
  have hfirst := mul_le_mul hNB (show 1 + a ^ (2 / 7 : ℝ) ≤ 2 by linarith only [haPow])
    (show 0 ≤ 1 + a ^ (2 / 7 : ℝ) by positivity) hB.le
  nlinarith only [hfirst, hprod]

end OriginalBorelCubicHolderNormalization


namespace OriginalBorelCubicSelectedRegime
noncomputable section
set_option maxHeartbeats 3000000

theorem warm_coefficient_times_step_radius_le_one
    (mu L rho eps : ℝ) (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1) :
    (rho / mu * (2 * Real.sqrt (L / mu))) *
      OriginalBorelOuterCubicSeparateErrors.stepRadius (OriginalBorelStatefulEnvelopeCubic.curvature mu L rho) (eps / 2) ≤ 1 := by
  let s := Real.sqrt (L / mu)
  let M := OriginalBorelStatefulEnvelopeCubic.curvature mu L rho
  let R := OriginalBorelOuterCubicSeparateErrors.stepRadius M (eps / 2)
  let b := rho / mu * (2 * s)
  have hL : 0 < L := hmu.trans_le hLmu
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = L / mu := Real.sq_sqrt (by positivity)
  have hLeq : L = mu * s ^ 2 := by rw [hs2]; field_simp
  have hM : 0 < M := by dsimp [M, OriginalBorelStatefulEnvelopeCubic.curvature]; positivity
  have hp := OriginalBorelOuterCubicSeparateErrors.radius_properties M (eps / 2) hM (by positivity)
  have hR : 0 < R := hp.2.1
  have hMR0 := hp.2.2.1
  have hMR : M * R ^ 2 = eps / 32 := by change M * R ^ 2 = eps / 2 / 16 at hMR0; linarith only [hMR0]
  have hpower : (L / mu) ^ (3 / 2 : ℝ) = s ^ 3 := by
    dsimp only [s]
    symm
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ L / mu by positivity)]
    norm_num
  have hMLower : 8 * rho * s ^ 3 ≤ M := by
    have hpow := Real.rpow_le_rpow (show 0 ≤ L / mu by positivity)
      (show L / mu ≤ 1 + L / mu by linarith) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [hpower] at hpow
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hRbound : R ^ 2 ≤ eps / (256 * rho * s ^ 3) := by
    apply (le_div_iff₀ (show 0 < 256 * rho * s ^ 3 by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hMLower (sq_nonneg R)
    nlinarith only [hh, hMR]
  have hb2 := mul_le_mul_of_nonneg_left hRbound (sq_nonneg b)
  have hid : b ^ 2 * (eps / (256 * rho * s ^ 3)) =
      OriginalGDRateNormalization.ratio mu L rho eps / 64 := by
    dsimp only [b, OriginalGDRateNormalization.ratio]
    change (rho / mu * (2 * s)) ^ 2 * (eps / (256 * rho * s ^ 3)) =
      (rho * s ^ 3 * eps / L ^ 2) / 64
    rw [hLeq]
    field_simp
    <;> ring
  rw [hid] at hb2
  have hb : 0 ≤ b * R := by dsimp [b]; positivity
  change b * R ≤ 1
  nlinarith only [hb2, hr, hb]

theorem terminal_cube_budget_factorization (Delta M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    4 * Delta / M + OriginalBorelOuterCubicSeparateErrors.stepRadius M eps ^ 3 =
      (1 + Delta / OriginalBorelOuterCubicSeparateErrors.stepCharge M eps) *
        OriginalBorelOuterCubicSeparateErrors.stepRadius M eps ^ 3 := by
  have hp := OriginalBorelOuterCubicSeparateErrors.radius_properties M eps hM heps
  have hR : OriginalBorelOuterCubicSeparateErrors.stepRadius M eps ≠ 0 := ne_of_gt hp.2.1
  unfold OriginalBorelOuterCubicSeparateErrors.stepCharge
  field_simp
  <;> ring

end
end OriginalBorelCubicSelectedRegime


namespace OriginalBorelStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial OriginalBorelOuterCubicSeparateErrors
open OriginalStatefulEnvelopeGD

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

def cubicBudget (mu L rho Delta eps : ℝ) :=
  1 + Delta / stepCharge (curvature mu L rho) (eps / 2)

def cubeBound (mu L rho Delta eps : ℝ) :=
  4 * Delta / curvature mu L rho + stepRadius (curvature mu L rho) (eps / 2) ^ 3

def queryGap (mu L rho Delta eps : ℝ) := Delta + stepCharge (curvature mu L rho) (eps / 2)

def globalWarmRadius (mu L rho Delta Ry eps : ℝ) :=
  max (OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry)
    (callerTolerance mu L rho eps + 2 * Real.sqrt (L / mu) * (1 + cubeBound mu L rho Delta eps))

def globalObservedRadius (mu L rho Delta Ry eps : ℝ) :=
  3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + globalWarmRadius mu L rho Delta Ry eps)

def globalLogFactor (mu L rho Delta Ry eps : ℝ) :=
  OriginalUniformMinimumWarmLog.uniformFactor mu L rho (globalWarmRadius mu L rho Delta Ry eps)
    (callerTolerance mu L rho eps) (globalObservedRadius mu L rho Delta Ry eps)

/-- The genuine cubic caller has a parameter-only logarithmic factor and a full
original-oracle budget in the selected `r ≤ 1` regime. Both the terminal move and
its extra envelope query are included. -/
theorem actual_uniform_cubic_selected_branch
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    let U := globalLogFactor mu L rho Delta Ry eps
    1 ≤ U ∧ run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.2 : ℝ) ≤ U * (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry +
      1 + 4 * cubicBudget mu L rho Delta eps) := by
  let tau := callerTolerance mu L rho eps
  let M := curvature mu L rho
  let D0 := OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry
  let B := cubicBudget mu L rho Delta eps
  let R := globalWarmRadius mu L rho Delta Ry eps
  let Obs := globalObservedRadius mu L rho Delta Ry eps
  let U := globalLogFactor mu L rho Delta Ry eps
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  have hM : 0 < M := by dsimp [M, curvature]; positivity
  have hp := radius_properties M (eps / 2) hM (by positivity)
  have hcharge : 0 < stepCharge M (eps / 2) := hp.2.2.2
  have hDelta : 0 ≤ Delta := by
    have hi := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap, hi]
  have hB : 0 < B := by dsimp [B,cubicBudget]; positivity
  have hCB : 0 ≤ cubeBound mu L rho Delta eps := by
    change 0 ≤ 4 * Delta / M + stepRadius M (eps / 2) ^ 3
    exact add_nonneg (by positivity) (pow_nonneg hp.2.1.le 3)
  have htau : 0 < tau := by
    have hsq : 0 < Real.sqrt (M * (eps / 2)) := Real.sqrt_pos.mpr (by positivity)
    have hgd : 0 < OriginalStatefulEnvelopeGD.callerTolerance mu L eps := by
      unfold OriginalStatefulEnvelopeGD.callerTolerance
      positivity
    change 0 < min (eps / (4096 * L))
      (min (Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2))
        (min (mu / rho) (OriginalStatefulEnvelopeGD.callerTolerance mu L eps)))
    positivity
  have hRtau : tau ≤ R := by
    apply le_trans ?_ (le_max_right _ _)
    exact le_add_of_nonneg_right (by positivity)
  have hR0 : D0 ≤ R := le_max_left _ _
  have hR : 0 < R := htau.trans_le hRtau
  have hObs : 0 ≤ Obs := by dsimp [Obs, globalObservedRadius]; positivity
  have hU : 1 ≤ U := OriginalStatefulEnvelopeGD.uniform_minimum_factor_ge_one
    mu L rho R tau Obs hmu hL hrho.le htau hR.le hObs
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hbase := actual_cubic_caller_from_original_inputs J mu L rho Delta Ry eps hmu hLmu hrho heps
    hC2 hLip hHess hsc hbelow start yin hgap hdual
  change run.1.success = true ∧ _ at hbase
  rcases hbase with ⟨htrue, hstationary, hcount, hcubes, hcost, htrace⟩
  have hrad : ∀ m ∈ run.1.moves, m.radius ≤ R := by
    intro m hm
    have hh := cubic_warm_radii_uniform_bound L mu tau (cubeBound mu L rho Delta eps) run.1.moves
      hcubes (fun m hm => (htrace m hm).2.1) m hm
    exact hh.trans (le_max_right _ _)
  have hlogs : ∀ m ∈ run.1.moves, OriginalStatefulEnvelopeGD.moveLog J mu L rho tau m ≤ U := by
    intro m hm
    obtain ⟨hlegal, _, hobs⟩ := htrace m hm
    have hD : 0 ≤ m.radius := (norm_nonneg _).trans hlegal
    have hobsR : OriginalDualResidualQueryBound.observedRadius J L m.next m.next m.warm ≤ Obs :=
      hobs.trans (by
        change 3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + m.radius) ≤
          3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + R)
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hrad m hm)) (by norm_num))
    exact (OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform J mu L rho m.radius tau R Obs
      hmu hL hrho htau hD (hrad m hm) hRtau hC2 hLip hHess hsc m.next m.next m.warm hobsR).2
  have hMax := OriginalStatefulEnvelopeGD.maximum_log_le_of_all J mu L rho tau U hU run.1.moves hlogs
  have hinit := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hD0 : 0 ≤ D0 := (norm_nonneg _).trans hinit
  have hinitObs := OriginalInitialSaddleRadius.actual_initial_primal_residual J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hSQ : Real.sqrt (Delta / L) ≤ Real.sqrt (queryGap mu L rho Delta eps / L) := by
    apply Real.sqrt_le_sqrt
    apply (div_le_div_iff_of_pos_right hL).mpr
    change Delta ≤ Delta + stepCharge M (eps / 2)
    linarith only [hcharge]
  have hinitObsR : OriginalDualResidualQueryBound.observedRadius J L start start yin ≤ Obs :=
    hinitObs.trans (by
      change 3 * (Real.sqrt (Delta / L) + D0) ≤
        3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + R)
      exact mul_le_mul_of_nonneg_left (add_le_add hSQ hR0) (by norm_num))
  have hinitLog := (OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform J mu L rho D0 tau R Obs
    hmu hL hrho htau hD0 hR0 hRtau hC2 hLip hHess hsc start start yin hinitObsR).2
  have hI0 : 0 ≤ OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry := by
    dsimp [OriginalStatefulEnvelopeGD.initializationPolynomial]
    have hp : 0 ≤ rho * OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry / mu := by
      change 0 ≤ rho * D0 / mu
      positivity
    positivity
  have hinitCost : OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin ≤
      OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry * U :=
    mul_le_mul_of_nonneg_left hinitLog hI0
  have htauSmall : rho * tau / mu ≤ 1 := by
    have ht : tau ≤ mu / rho :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ rho / mu by positivity)
    have he : (rho / mu) * (mu / rho) = 1 := by field_simp
    rw [he] at hh
    calc
      rho * tau / mu = (rho / mu) * tau := by ring
      _ ≤ 1 := hh
  have hfactor := OriginalBorelCubicSelectedRegime.terminal_cube_budget_factorization Delta M (eps / 2) hM (by positivity)
  have hcubesB : cubedMovement run.1.moves ≤ B * stepRadius M (eps / 2) ^ 3 := hcubes.trans_eq hfactor
  have hpoly := OriginalBorelCubicHolderNormalization.holder_with_terminal_budget
    (run.1.moves.length : ℝ) (cubedMovement run.1.moves) B (stepRadius M (eps / 2))
    (rho * tau / mu) (rho / mu * (2 * Real.sqrt (L / mu)))
    (by positivity) (cubed_movement_nonnegative _) hB hp.2.1 (by positivity) (by positivity)
    hcount hcubesB htauSmall
    (OriginalBorelCubicSelectedRegime.warm_coefficient_times_step_radius_le_one mu L rho eps hmu hLmu hrho heps hr)
  have hholder := actual_cubic_cost_sum_holder_bound J mu L rho tau hmu hL hrho.le htau.le run.1.moves
    (fun m hm => (htrace m hm).2.1)
  have hcostMoves : OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves ≤ U * (3 * B) := by
    have hP0 : 0 ≤ cubicPolynomialBound mu L rho tau run.1.moves := by
      have hC0 := cubed_movement_nonnegative run.1.moves
      unfold cubicPolynomialBound
      positivity
    have h1 := mul_le_mul_of_nonneg_right hMax hP0
    have h2 := mul_le_mul_of_nonneg_left hpoly hU0
    exact hholder.trans (h1.trans h2)
  change (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin +
    1 + OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ) at hcost
  refine ⟨hU,htrue,hstationary,?_⟩
  change (run.2 : ℝ) ≤ U * (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry + 1 + 4 * B)
  have hlen : (run.1.moves.length : ℝ) ≤ B := hcount
  have h1 := mul_nonneg (sub_nonneg.mpr hU) (show 0 ≤ 1 + B by positivity)
  nlinarith only [hcost,hinitCost,hcostMoves,hlen,h1]

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelCubicPaperRate
noncomputable section
set_option maxHeartbeats 3000000

def A2 (mu L rho Delta eps : ℝ) :=
  Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) / eps ^ (3 / 2 : ℝ)

theorem sqrt_curvature_upper (mu L rho : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) :
    Real.sqrt (OriginalBorelStatefulEnvelopeCubic.curvature mu L rho) ≤
      8 * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) := by
  have hL : 0 < L := hmu.trans_le hLmu
  have hk : 1 ≤ L / mu := (le_div_iff₀ hmu).mpr (by simpa using hLmu)
  have hk0 : 0 ≤ L / mu := by positivity
  have ht : Real.sqrt ((1 + L / mu) ^ (3 / 2 : ℝ)) = (1 + L / mu) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (show 0 ≤ 1 + L / mu by positivity)]
    norm_num
  have hroot : Real.sqrt (OriginalBorelStatefulEnvelopeCubic.curvature mu L rho) =
      Real.sqrt 8 * Real.sqrt rho * (1 + L / mu) ^ (3 / 4 : ℝ) := by
    unfold OriginalBorelStatefulEnvelopeCubic.curvature
    rw [Real.sqrt_mul (show 0 ≤ 8 * rho by positivity),Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8),ht]
  have hp := Real.rpow_le_rpow (show 0 ≤ 1 + L / mu by positivity)
    (show 1 + L / mu ≤ 2 * (L / mu) by linarith only [hk]) (by norm_num : (0 : ℝ) ≤ 3 / 4)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hk0] at hp
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have h8 : Real.sqrt (8 : ℝ) ≤ 4 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8),Real.sqrt_nonneg (8 : ℝ)]
  rw [hroot]
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hk0 (3 / 4 : ℝ))
  have h4 := mul_le_mul h8 (hp.trans h3) (Real.rpow_nonneg (show 0 ≤ 1 + L / mu by positivity) _)
    (by norm_num : (0 : ℝ) ≤ 4)
  have h5 := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg rho)
  nlinarith only [h5]

theorem cubic_budget_le_paper_rate (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (hDelta : 0 ≤ Delta) (heps : 0 < eps) :
    OriginalBorelStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps ≤ 1 + 8192 * A2 mu L rho Delta eps := by
  have hL : 0 < L := hmu.trans_le hLmu
  let M := OriginalBorelStatefulEnvelopeCubic.curvature mu L rho
  have hM : 0 < M := by dsimp [M,OriginalBorelStatefulEnvelopeCubic.curvature]; positivity
  have hcharge := OriginalBorelOuterCubicSeparateErrors.reciprocal_charge_identity Delta M (eps / 2) hM (by positivity)
  have hsqrt := sqrt_curvature_upper mu L rho hmu hLmu hrho
  have hscale : eps ^ (3 / 2 : ℝ) ≤ 4 * (eps / 2) ^ (3 / 2 : ℝ) := by
    have hid : eps = 2 * (eps / 2) := by ring
    have hh : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
      have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (3 / 2 : ℝ) ≤ 2)
      norm_num at ht
      exact ht
    calc
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (eps / 2) ^ (3 / 2 : ℝ) := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ eps / 2)]
        congr 1
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (by positivity)
  have hpow : 0 < eps ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos heps _
  have hhalf : 0 < (eps / 2) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hnum := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 256 * Delta by positivity)
  have h1 := div_le_div_of_nonneg_right hnum hhalf.le
  have h2 : (2048 * Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ)) / (eps / 2) ^ (3 / 2 : ℝ) ≤
      8192 * A2 mu L rho Delta eps := by
    unfold A2
    rw [show 8192 * (Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) / eps ^ (3 / 2 : ℝ)) =
      (8192 * Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ)) / eps ^ (3 / 2 : ℝ) by ring]
    apply (div_le_div_iff₀ hhalf hpow).mpr
    have hmul := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ 2048 * Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) by positivity)
    nlinarith only [hmul]
  change 1 + Delta / OriginalBorelOuterCubicSeparateErrors.stepCharge M (eps / 2) ≤ _
  rw [hcharge]
  have h3 : 256 * Delta * Real.sqrt M / (eps / 2) ^ (3 / 2 : ℝ) ≤
      8192 * A2 mu L rho Delta eps := h1.trans (by convert! h2 using 1 <;> ring)
  linarith only [h3]

end
end OriginalBorelCubicPaperRate


namespace OriginalBorelMainUpperRates
noncomputable section
set_option maxHeartbeats 3000000

def cubic (mu L rho Delta eps : ℝ) :=
  OriginalBorelCubicPaperRate.A2 mu L rho Delta eps *
    (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (1 / 7 : ℝ))

def middle (mu L rho Delta eps : ℝ) :=
  OriginalGDRateNormalization.A1 Delta L eps *
    (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ))

def first (mu L Delta eps : ℝ) :=
  Real.sqrt (L / mu) * OriginalGDRateNormalization.A1 Delta L eps

def frontier (mu L rho Delta eps : ℝ) :=
  min (cubic mu L rho Delta eps) (min (middle mu L rho Delta eps) (first mu L Delta eps))

theorem A2_eq_A1_sqrt_ratio (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (heps : 0 < eps) :
    OriginalBorelCubicPaperRate.A2 mu L rho Delta eps =
      OriginalGDRateNormalization.A1 Delta L eps * Real.sqrt (OriginalGDRateNormalization.ratio mu L rho eps) := by
  have hk : 0 ≤ L / mu := by positivity
  have hr : 0 ≤ OriginalGDRateNormalization.ratio mu L rho eps := by
    unfold OriginalGDRateNormalization.ratio
    positivity
  have hp : ((L / mu) ^ (3 / 4 : ℝ)) ^ 2 = (L / mu) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk]
    norm_num
  let c := Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) * Real.sqrt eps / L
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcsq : c ^ 2 = OriginalGDRateNormalization.ratio mu L rho eps := by
    dsimp only [c]
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hrho,Real.sq_sqrt heps.le,hp,
      OriginalGDRateNormalization.ratio_eq_paper mu L rho eps hmu hL]
  have hroot : Real.sqrt (OriginalGDRateNormalization.ratio mu L rho eps) = c := by
    nlinarith only [Real.sq_sqrt hr,Real.sqrt_nonneg (OriginalGDRateNormalization.ratio mu L rho eps),hcsq,hc]
  have hepow : eps ^ (3 / 2 : ℝ) = eps * Real.sqrt eps := by
    calc
      _ = eps ^ (1 + 1 / 2 : ℝ) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add heps,Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [hroot]
  unfold OriginalBorelCubicPaperRate.A2 OriginalGDRateNormalization.A1 c
  rw [hepow]
  field_simp
  <;> rw [Real.sq_sqrt heps.le]
  <;> ring

theorem A2_le_all_rates_in_small_regime (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (hDelta : 0 ≤ Delta) (heps : 0 < eps)
    (hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1) :
    OriginalBorelCubicPaperRate.A2 mu L rho Delta eps ≤ frontier mu L rho Delta eps := by
  have hL : 0 < L := hmu.trans_le hLmu
  have ha1 : 0 ≤ OriginalGDRateNormalization.A1 Delta L eps := by unfold OriginalGDRateNormalization.A1; positivity
  have ha2 : 0 ≤ OriginalBorelCubicPaperRate.A2 mu L rho Delta eps := by unfold OriginalBorelCubicPaperRate.A2; positivity
  have hr0 : 0 ≤ OriginalGDRateNormalization.ratio mu L rho eps := by unfold OriginalGDRateNormalization.ratio; positivity
  have hsqrt : Real.sqrt (OriginalGDRateNormalization.ratio mu L rho eps) ≤ 1 := by
    have hh := Real.sqrt_le_sqrt hr
    simpa using hh
  have hk : 1 ≤ Real.sqrt (L / mu) := by
    have hh := Real.sqrt_le_sqrt ((le_div_iff₀ hmu).mpr (by simpa using hLmu) : 1 ≤ L / mu)
    simpa using hh
  have hA2 : OriginalBorelCubicPaperRate.A2 mu L rho Delta eps ≤ OriginalGDRateNormalization.A1 Delta L eps := by
    rw [A2_eq_A1_sqrt_ratio mu L rho Delta eps hmu hL hrho heps]
    nlinarith only [mul_le_mul_of_nonneg_left hsqrt ha1]
  unfold frontier
  refine le_min ?_ (le_min ?_ ?_)
  · unfold cubic
    have hh := mul_nonneg ha2 (Real.rpow_nonneg hr0 (1 / 7 : ℝ))
    nlinarith only [hh]
  · unfold middle
    have hh := mul_nonneg ha1 (Real.rpow_nonneg hr0 (2 / 7 : ℝ))
    nlinarith only [hh,hA2]
  · unfold first
    have hh := mul_nonneg ha1 (sub_nonneg.mpr hk)
    nlinarith only [hh,hA2]

theorem middle_le_twice_cubic_in_large_regime (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (hDelta : 0 ≤ Delta) (heps : 0 < eps)
    (hr : 1 ≤ OriginalGDRateNormalization.ratio mu L rho eps) :
    middle mu L rho Delta eps ≤ 2 * cubic mu L rho Delta eps := by
  let r := OriginalGDRateNormalization.ratio mu L rho eps
  have ha1 : 0 ≤ OriginalGDRateNormalization.A1 Delta L eps := by unfold OriginalGDRateNormalization.A1; positivity
  have ha2 : 0 ≤ OriginalBorelCubicPaperRate.A2 mu L rho Delta eps := by unfold OriginalBorelCubicPaperRate.A2; positivity
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hpow : r ^ (2 / 7 : ℝ) ≤ Real.sqrt r := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hsqrt : 1 ≤ Real.sqrt r := by
    have hh := Real.sqrt_le_sqrt hr
    simpa using hh
  have hA2 := A2_eq_A1_sqrt_ratio mu L rho Delta eps hmu hL hrho heps
  change OriginalBorelCubicPaperRate.A2 mu L rho Delta eps = OriginalGDRateNormalization.A1 Delta L eps * Real.sqrt r at hA2
  have h1 := mul_le_mul_of_nonneg_left (show 1 + r ^ (2 / 7 : ℝ) ≤ 2 * Real.sqrt r by linarith only [hpow,hsqrt]) ha1
  have h2 := mul_nonneg ha2 (Real.rpow_nonneg hr0 (1 / 7 : ℝ))
  unfold middle cubic
  change OriginalGDRateNormalization.A1 Delta L eps * (1 + r ^ (2 / 7 : ℝ)) ≤
    2 * (OriginalBorelCubicPaperRate.A2 mu L rho Delta eps * (1 + r ^ (1 / 7 : ℝ)))
  nlinarith only [h1,h2,hA2]

end
end OriginalBorelMainUpperRates


namespace OriginalBorelActualMainUpper

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def positiveProgram (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) E :=
  if OriginalGDRateNormalization.ratio mu L rho eps ≤ 1 then
    map (fun out : OriginalBorelStatefulEnvelopeCubic.Result E F => out.saddle.fst)
      (OriginalBorelStatefulEnvelopeCubic.caller mu L rho Delta Ry eps start yin)
  else
    map (fun out : OriginalStatefulEnvelopeGD.Result E F => out.saddle.fst)
      (OriginalStatefulEnvelopeGD.caller mu L rho Delta Ry eps start yin)

def positiveLogFactor (mu L rho Delta Ry eps : ℝ) :=
  max (OriginalStatefulEnvelopeGD.globalLogFactor mu L rho Delta Ry eps)
    (OriginalBorelStatefulEnvelopeCubic.globalLogFactor mu L rho Delta Ry eps)

def program (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) E :=
  if rho = 0 then OriginalZeroHessianReconstruction.program mu L Delta Ry eps start yin
  else positiveProgram mu L rho Delta Ry eps start yin

def logarithmicFactor (mu L rho Delta Ry eps : ℝ) :=
  if rho = 0 then 1 else positiveLogFactor mu L rho Delta Ry eps

theorem scalar_cost_domination (T u U I R c : ℝ)
    (hT : T ≤ u * (I + c * R)) (hu : u ≤ U) (hU : 0 ≤ U)
    (hI : 0 ≤ I) (hR : 0 ≤ R) (hc : 0 ≤ c) (hcmax : c ≤ 32768) :
    T ≤ 32768 * U * (I + R) := by
  have h1 := mul_le_mul_of_nonneg_right hu (show 0 ≤ I + c * R by positivity)
  have h2 := mul_nonneg hU (show 0 ≤ (32768 - c) * R by positivity)
  have h3 := mul_nonneg hU hI
  nlinarith only [hT,h1,h2,h3]

theorem cost_le_frontier_of_three_bounds (T K I mu L rho Delta eps : ℝ)
    (hc : T ≤ K * (I + OriginalBorelMainUpperRates.cubic mu L rho Delta eps))
    (hm : T ≤ K * (I + OriginalBorelMainUpperRates.middle mu L rho Delta eps))
    (hf : T ≤ K * (I + OriginalBorelMainUpperRates.first mu L Delta eps)) :
    T ≤ K * (I + OriginalBorelMainUpperRates.frontier mu L rho Delta eps) := by
  unfold OriginalBorelMainUpperRates.frontier
  by_cases h : OriginalBorelMainUpperRates.cubic mu L rho Delta eps ≤
      min (OriginalBorelMainUpperRates.middle mu L rho Delta eps) (OriginalBorelMainUpperRates.first mu L Delta eps)
  · rw [min_eq_left h]
    exact hc
  · rw [min_eq_right (le_of_not_ge h)]
    by_cases hm' : OriginalBorelMainUpperRates.middle mu L rho Delta eps ≤ OriginalBorelMainUpperRates.first mu L Delta eps
    · rw [min_eq_left hm']
      exact hm
    · rw [min_eq_right (le_of_not_ge hm')]
      exact hf

theorem positive_main_upper
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (positiveProgram mu L rho Delta Ry eps start yin)
    let U := positiveLogFactor mu L rho Delta Ry eps
    1 ≤ U ∧ ‖gradient (phi (JointSliceRegularity.curry J)) run.1‖ ≤ eps ∧
    (run.2 : ℝ) ≤ 32768 * U *
      (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry +
        OriginalBorelMainUpperRates.frontier mu L rho Delta eps) := by
  let U := positiveLogFactor mu L rho Delta Ry eps
  let Ug := OriginalStatefulEnvelopeGD.globalLogFactor mu L rho Delta Ry eps
  let Uc := OriginalBorelStatefulEnvelopeCubic.globalLogFactor mu L rho Delta Ry eps
  let I := OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry
  have hL : 0 < L := hmu.trans_le hLmu
  have hDelta : 0 ≤ Delta := by
    have hi := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap,hi]
  have hD0 : 0 ≤ OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry := by
    have hh := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
    exact (norm_nonneg _).trans hh
  have hI : 1 ≤ I := by
    change 1 ≤ 1 + min (Real.sqrt (L / mu))
      ((rho * OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry / mu) ^ (2 / 7 : ℝ))
    exact le_add_of_nonneg_right (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _))
  have hUgU : Ug ≤ U := le_max_left _ _
  have hUcU : Uc ≤ U := le_max_right _ _
  have hgd := OriginalStatefulEnvelopeGD.actual_uniform_gradient_main_branches J mu L rho Delta Ry eps
    hmu hLmu hrho heps hC2 hLip hHess hsc hbelow start yin hgap hdual
  have hUg : 1 ≤ Ug := hgd.1
  have hU : 1 ≤ U := hUg.trans hUgU
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  by_cases hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1
  · have hc := OriginalBorelStatefulEnvelopeCubic.actual_uniform_cubic_selected_branch J mu L rho Delta Ry eps
      hmu hLmu hrho heps hr hC2 hLip hHess hsc hbelow start yin hgap hdual
    simp only [positiveProgram,if_pos hr,execute_map]
    refine ⟨hU,hc.2.2.1,?_⟩
    change ((execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalBorelStatefulEnvelopeCubic.caller mu L rho Delta Ry eps start yin)).2 : ℝ) ≤
      32768 * U * (I + OriginalBorelMainUpperRates.frontier mu L rho Delta eps)
    have hB := OriginalBorelCubicPaperRate.cubic_budget_le_paper_rate mu L rho Delta eps hmu hLmu hrho hDelta heps
    have hA2 := OriginalBorelMainUpperRates.A2_le_all_rates_in_small_regime mu L rho Delta eps hmu hLmu hrho.le hDelta heps hr
    have hraw : 0 ≤ I + 1 + 4 * OriginalBorelStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps := by
      have hM : 0 < OriginalBorelStatefulEnvelopeCubic.curvature mu L rho := by
        unfold OriginalBorelStatefulEnvelopeCubic.curvature
        positivity
      have hcharge := (OriginalBorelOuterCubicSeparateErrors.radius_properties
        (OriginalBorelStatefulEnvelopeCubic.curvature mu L rho) (eps / 2) hM (by positivity)).2.2.2
      unfold OriginalBorelStatefulEnvelopeCubic.cubicBudget
      positivity
    have h1 := mul_le_mul_of_nonneg_right hUcU hraw
    have h2 := mul_le_mul_of_nonneg_left
      (show I + 1 + 4 * OriginalBorelStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps ≤
        32768 * (I + OriginalBorelMainUpperRates.frontier mu L rho Delta eps) by nlinarith only [hB,hA2,hI]) hU0
    have hcCost := hc.2.2.2
    change ((execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalBorelStatefulEnvelopeCubic.caller mu L rho Delta Ry eps start yin)).2 : ℝ) ≤
      Uc * (I + 1 + 4 * OriginalBorelStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps) at hcCost
    nlinarith only [hcCost,h1,h2]
  · simp only [positiveProgram,if_neg hr,execute_map]
    refine ⟨hU,hgd.2.2.1,?_⟩
    let T := ((execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalStatefulEnvelopeGD.caller mu L rho Delta Ry eps start yin)).2 : ℝ)
    have hmiddle : T ≤ Ug * (I + 512 * OriginalBorelMainUpperRates.middle mu L rho Delta eps) := by
      convert! hgd.2.2.2.1 using 1 <;> unfold OriginalBorelMainUpperRates.middle <;> ring
    have hfirst : T ≤ Ug * (I + 256 * OriginalBorelMainUpperRates.first mu L Delta eps) := by
      convert! hgd.2.2.2.2 using 1 <;> unfold OriginalBorelMainUpperRates.first <;> ring
    have hmid0 : 0 ≤ OriginalBorelMainUpperRates.middle mu L rho Delta eps := by
      unfold OriginalBorelMainUpperRates.middle OriginalGDRateNormalization.A1 OriginalGDRateNormalization.ratio
      positivity
    have hfirst0 : 0 ≤ OriginalBorelMainUpperRates.first mu L Delta eps := by
      unfold OriginalBorelMainUpperRates.first OriginalGDRateNormalization.A1
      positivity
    have hcub0 : 0 ≤ OriginalBorelMainUpperRates.cubic mu L rho Delta eps := by
      unfold OriginalBorelMainUpperRates.cubic OriginalBorelCubicPaperRate.A2 OriginalGDRateNormalization.ratio
      positivity
    have hcomp := OriginalBorelMainUpperRates.middle_le_twice_cubic_in_large_regime mu L rho Delta eps hmu hL hrho.le hDelta heps (le_of_not_ge hr)
    have h1 : T ≤ Ug * (I + 1024 * OriginalBorelMainUpperRates.cubic mu L rho Delta eps) := by
      have hh := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ 512 * Ug by positivity)
      nlinarith only [hmiddle,hh]
    have hc := scalar_cost_domination T Ug U I (OriginalBorelMainUpperRates.cubic mu L rho Delta eps) 1024
      h1 hUgU hU0 (zero_le_one.trans hI) hcub0 (by norm_num) (by norm_num)
    have hm := scalar_cost_domination T Ug U I (OriginalBorelMainUpperRates.middle mu L rho Delta eps) 512
      hmiddle hUgU hU0 (zero_le_one.trans hI) hmid0 (by norm_num) (by norm_num)
    have hf := scalar_cost_domination T Ug U I (OriginalBorelMainUpperRates.first mu L Delta eps) 256
      hfirst hUgU hU0 (zero_le_one.trans hI) hfirst0 (by norm_num) (by norm_num)
    exact cost_le_frontier_of_three_bounds T (32768 * U) I mu L rho Delta eps hc hm hf

/-- Full actual original-oracle upper program: rho=0 reconstructs the whole
quadratic from one bundle; rho>0 selects cubic/GD using only known parameters.
The original theorem's randomized lower bound is a separate obligation. -/
theorem main_upper_from_original_standing_inputs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program mu L rho Delta Ry eps start yin)
    let U := logarithmicFactor mu L rho Delta Ry eps
    1 ≤ U ∧ ‖gradient (phi (JointSliceRegularity.curry J)) run.1‖ ≤ eps ∧
    (run.2 : ℝ) ≤ 32768 * U *
      (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry +
        OriginalBorelMainUpperRates.frontier mu L rho Delta eps) := by
  by_cases hzero : rho = 0
  · subst rho
    have hh := OriginalZeroHessianReconstruction.one_original_query_suffices_when_hessian_is_constant
      J mu L Delta Ry eps hmu hLmu heps hC2 hLip hHess hsc hbelow start yin hgap hdual
    simp only [program,logarithmicFactor,if_pos rfl,ite_true]
    refine ⟨le_refl _,hh.2,?_⟩
    rw [hh.1]
    have hDelta : 0 ≤ Delta := by
      have hi := csInf_le hbelow (Set.mem_range_self start)
      linarith only [hgap,hi]
    have hL : 0 < L := hmu.trans_le hLmu
    have hF : 0 ≤ OriginalBorelMainUpperRates.frontier mu L 0 Delta eps := by
      unfold OriginalBorelMainUpperRates.frontier OriginalBorelMainUpperRates.cubic OriginalBorelMainUpperRates.middle
        OriginalBorelMainUpperRates.first OriginalBorelCubicPaperRate.A2 OriginalGDRateNormalization.A1 OriginalGDRateNormalization.ratio
      positivity
    have hI : 1 ≤ OriginalStatefulEnvelopeGD.initializationPolynomial mu L 0 Delta Ry := by
      unfold OriginalStatefulEnvelopeGD.initializationPolynomial
      simp only [zero_mul,zero_div,Real.zero_rpow (by norm_num : (2 / 7 : ℝ) ≠ 0)]
      exact le_add_of_nonneg_right (le_min (Real.sqrt_nonneg _) le_rfl)
    norm_num only [Nat.cast_one,mul_one]
    nlinarith only [hF,hI]
  · have hpos : 0 < rho := lt_of_le_of_ne hrho (Ne.symm hzero)
    simp only [program,logarithmicFactor,if_neg hzero]
    exact positive_main_upper J mu L rho Delta Ry eps hmu hLmu hpos heps hC2 hLip hHess hsc hbelow start yin hgap hdual

end
end OriginalBorelActualMainUpper
end
