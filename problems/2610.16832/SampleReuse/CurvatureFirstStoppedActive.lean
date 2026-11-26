import SampleReuse.CurvatureFirstStoppedCounts
import SampleReuse.CurvatureFirstTrajectory

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

variable {Ω : Type*} {d T Bg BH : ℕ}
  (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
  (f : Point d → ℝ) (F : Ω → Point d → ℝ)
  (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)

theorem curvatureStoppedStep_active (t : ℕ) (s : StoppedOptimizerCache d) (b : Bool)
    (ha : (curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s b).1 = true) :
    s.1 = true := by
  by_contra hn
  have hf : s.1 = false := Bool.eq_false_iff.mpr hn
  simp only [curvatureStoppedStep,hf,Bool.false_eq_true,if_false] at ha

theorem curvatureStoppedRun_frozen (signs : ℕ → Bool) (x₀ : Point d) {j t : ℕ}
    (hjt : j ≤ t)
    (hj : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ j).1 = false) :
    curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t =
      curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ j := by
  induction t, hjt using Nat.le_induction with
  | base => rfl
  | succ t _ ih =>
    rw [curvatureStoppedRun,ih]
    simp only [curvatureStoppedStep,hj,Bool.false_eq_true,if_false]

theorem curvatureStoppedRun_active_before (signs : ℕ → Bool) (x₀ : Point d) {j t : ℕ}
    (hjt : j ≤ t)
    (ht : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t).1 = true) :
    (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ j).1 = true := by
  by_contra hn
  have hj : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ j).1 = false :=
    Bool.eq_false_iff.mpr hn
  rw [curvatureStoppedRun_frozen hBg hBH P ε γ scaleG scaleH f F tape signs x₀ hjt hj,hj] at ht
  cases ht

theorem curvatureStoppedStep_actionStepCount (t : ℕ) (s : StoppedOptimizerCache d) (b : Bool) :
    actionStepCount (stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape t s) =
      if (curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s b).1 then 1 else 0 := by
  by_cases hs : s.1 = true
  · by_cases hv : ValidInspection f ε γ s.2.1
        (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2).action
    · simp only [stoppedInspectionAction,curvatureStoppedStep,if_pos hs,if_pos hv]
      cases he : (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2).action <;>
        simp only [curvatureFirstAdvance,he,actionStepCount,Bool.false_eq_true,if_false,if_true]
    · simp only [stoppedInspectionAction,curvatureStoppedStep,if_pos hs,if_neg hv,
        actionStepCount,Bool.false_eq_true,if_false]
  · simp only [stoppedInspectionAction,curvatureStoppedStep,if_neg hs,actionStepCount]

theorem curvatureStoppedStep_cache_of_active (t : ℕ) (s : StoppedOptimizerCache d) (b : Bool)
    (ha : (curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s b).1 = true) :
    (curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s b).2 =
      curvatureMacroAdvance P ε γ b (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2) := by
  have hs := curvatureStoppedStep_active hBg hBH P ε γ scaleG scaleH f F tape t s b ha
  simp only [curvatureStoppedStep,hs,if_true] at ha ⊢
  by_cases hv : ValidInspection f ε γ s.2.1
      (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2).action
  · simp only [if_pos hv] at ha ⊢
    cases he : (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2).action <;>
      simp only [curvatureFirstAdvance,he,curvatureMacroAdvance,inspectionNextPoint] at ha ⊢
    cases ha
  · simp only [if_neg hv] at ha
    cases ha

theorem curvatureStoppedRun_eq_macro_of_active (signs : ℕ → Bool) (x₀ : Point d) (t : ℕ)
    (ht : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t).1 = true) :
    (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t).2 =
      curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := curvatureStoppedRun_active_before hBg hBH P ε γ scaleG scaleH f F tape signs x₀
      (Nat.le_succ t) ht
    rw [curvatureStoppedRun,curvatureStoppedStep_cache_of_active hBg hBH P ε γ scaleG scaleH f F tape
      t _ (signs t) ht,ih hp]
    rfl

end
end SampleReuse
