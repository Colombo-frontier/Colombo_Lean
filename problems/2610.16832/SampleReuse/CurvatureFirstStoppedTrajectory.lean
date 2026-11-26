import SampleReuse.CurvatureFirstFinite
import SampleReuse.FiniteSignCharging

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

abbrev StoppedOptimizerCache (d : ℕ) := Bool × OptimizerCache d

/-- Analysis-only stop at the first success or invalid inspection. It retains
the point where that inspection was made, so its last checkpoint may still
be charged even though it takes no further optimization step. -/
def curvatureStoppedStep {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (f : Point d → ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (t : ℕ)
    (s : StoppedOptimizerCache d) (b : Bool) : StoppedOptimizerCache d :=
  if s.1 then
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2
    if ValidInspection f ε γ s.2.1 r.action then
      match curvatureFirstAdvance P ε γ b r with
      | none => (false,s.2)
      | some s' => (true,s')
    else (false,s.2)
  else s

def curvatureStoppedRun {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (f : Point d → ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d) :
    ℕ → StoppedOptimizerCache d
  | 0 => (true,optimizerInitial x₀)
  | t+1 => curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t) (signs t)

theorem curvatureStoppedRun_depends_sign_past {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs signs' : ℕ → Bool) (x₀ : Point d) (t : ℕ) (heq : ∀ j < t, signs j = signs' j) :
    curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t =
      curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs' x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [curvatureStoppedRun,ih (fun j hj => heq j (Nat.lt_succ_of_lt hj)),heq t (Nat.lt_succ_self t)]

def extendFiniteSigns {M : ℕ} (w : Fin M → Bool) (t : ℕ) : Bool :=
  if ht : t < M then w ⟨t,ht⟩ else false

theorem extendFiniteSigns_past {M : ℕ} (i : Fin M) (w w' : Fin M → Bool)
    (he : SignPastEq i w w') : ∀ t < i.val, extendFiniteSigns w t = extendFiniteSigns w' t := by
  intro t ht
  have htM := ht.trans i.isLt
  simp only [extendFiniteSigns,dif_pos htM]
  exact he ⟨t,htM⟩ ht

theorem curvatureStoppedRun_signPredictable {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (x₀ : Point d) :
    SignPredictable (fun i : Fin M => fun w =>
      curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ i.val) := by
  intro i w w' he
  exact curvatureStoppedRun_depends_sign_past hBg hBH P ε γ scaleG scaleH f F tape _ _ x₀ i.val
    (extendFiniteSigns_past i w w' he)

def stoppedInspectionAction {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : StoppedOptimizerCache d) : CurvatureFirstAction d :=
  if s.1 then
    let a := (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2).action
    if ValidInspection f ε γ s.2.1 a then a else .success
  else .success

def actionDrift {d : ℕ} (P : Parameters) (ε : ℝ) : CurvatureFirstAction d → Point d
  | .gradient g => (-(ε/(4*P.gradientLip))) • ((‖g‖⁻¹:ℝ) • g)
  | _ => 0

def actionInnovationVector {d : ℕ} (P : Parameters) (γ : ℝ) : CurvatureFirstAction d → Point d
  | .curvature v => (γ/P.hessianLip) • v
  | _ => 0

theorem curvatureStoppedStep_increment {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : StoppedOptimizerCache d) (b : Bool) :
    (curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s b).2.1 - s.2.1 =
      actionDrift P ε (stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape t s) +
      signValue b • actionInnovationVector P γ
        (stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape t s) := by
  have hp := curvatureFirstInspect_point hBg hBH P ε γ scaleG scaleH F tape t s.2
  simp only [curvatureStoppedStep,stoppedInspectionAction]
  split_ifs
  · simp only [curvatureFirstAdvance]
    cases (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2).action with
    | success => simp only [actionDrift,actionInnovationVector,smul_zero,add_zero,sub_self]
    | gradient g => simp only [hp,gradientMove,actionDrift,actionInnovationVector,smul_zero,add_zero,add_sub_cancel_left]
    | curvature v => simp only [hp,curvatureNext,actionDrift,actionInnovationVector,zero_add,smul_smul,add_sub_cancel_left]
  · simp only [actionDrift,actionInnovationVector,smul_zero,add_zero,sub_self]
  · simp only [actionDrift,actionInnovationVector,smul_zero,add_zero,sub_self]

end
end SampleReuse
