import SampleReuse.CurvatureFirstValidity

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

/-- Total extension of the outer-iteration trajectory. A success inspection
uses a zero move; the executable controller returns at its first success.
This extension permits deterministic horizons in the concentration proof. -/
def curvatureMacroAdvance {d : ℕ} (P : Parameters) (ε γ : ℝ) (b : Bool)
    (r : CurvatureFirstInspection d) : OptimizerCache d :=
  (inspectionNextPoint P ε γ r.cache.1 r.action b,r.cache.2)

def curvatureMacroRun {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d) :
    ℕ → OptimizerCache d
  | 0 => optimizerInitial x₀
  | t+1 => curvatureMacroAdvance P ε γ (signs t)
      (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t
        (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t))

theorem curvatureFirstInspect_hessianCache {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (t : ℕ) (s : OptimizerCache d) :
    (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).cache.2.2.2 =
      Function.update s.2.2.2 t (s.1,inspectionHessian hBH P scaleH F tape t s) := by
  simp only [curvatureFirstInspect,inspectionHessian,installCheckpoint,checkpointValue]
  split_ifs <;> rfl

theorem curvatureMacroRun_gradientIndex {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d) (t : ℕ) :
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t).2.1 ≤ t := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    have hi := curvatureFirstInspect_gradientIndex hBg hBH P ε γ scaleG scaleH F tape t
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t)
    exact hi.2.trans (Nat.add_le_add_right ih 1)

theorem curvatureMacroRun_gradientIndex_mono {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d) :
    Monotone (fun t => (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t).2.1) := by
  apply monotone_nat_of_le_succ
  intro t
  exact (curvatureFirstInspect_gradientIndex hBg hBH P ε γ scaleG scaleH F tape t
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t)).1

theorem curvatureMacroRun_hessianCache_succ {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d) (t : ℕ) :
    let s := curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ (t+1)).2.2.2 =
      Function.update s.2.2.2 t (s.1,inspectionHessian hBH P scaleH F tape t s) := by
  exact curvatureFirstInspect_hessianCache hBg hBH P ε γ scaleG scaleH F tape t _

theorem curvatureMacroRun_hessianCache_entry {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d) {j t : ℕ} (hj : j < t) :
    let sj := curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ j
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t).2.2.2 j =
      (sj.1,inspectionHessian hBH P scaleH F tape j sj) := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [curvatureMacroRun_hessianCache_succ]
    by_cases he : j = t
    · subst j; exact Function.update_self _ _ _
    · rw [Function.update_of_ne he]
      exact ih (by omega)

end
end SampleReuse
