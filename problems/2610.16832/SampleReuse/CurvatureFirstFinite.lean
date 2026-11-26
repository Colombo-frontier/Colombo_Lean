import SampleReuse.CurvatureFirstShadow
import SampleReuse.CurvatureFirstRun

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

def curvatureFirstFiniteExecute {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) :
    (m : ℕ) → ℕ → OptimizerCache d → (Fin m → Bool) → Option (Point d)
  | 0, _, _, _ => none
  | m+1, t, s, signs =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    match r.action with
    | .success => some s.1
    | .gradient g => curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F tape m (t+1)
        (gradientMove P ε s.1 g,r.cache.2) (Fin.tail signs)
    | .curvature v => curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F tape m (t+1)
        (curvatureNext (γ/P.hessianLip) s.1 v (signs 0),r.cache.2) (Fin.tail signs)

def curvatureFirstFiniteValid {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (f : Point d → ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) :
    (m : ℕ) → ℕ → OptimizerCache d → (Fin m → Bool) → Prop
  | 0, _, _, _ => True
  | m+1, t, s, signs =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    ValidInspection f ε γ s.1 r.action ∧
    match r.action with
    | .success => True
    | .gradient g => curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F tape m (t+1)
        (gradientMove P ε s.1 g,r.cache.2) (Fin.tail signs)
    | .curvature v => curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F tape m (t+1)
        (curvatureNext (γ/P.hessianLip) s.1 v (signs 0),r.cache.2) (Fin.tail signs)

theorem curvatureFirstFiniteExecute_eq {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) (bits : Fin m → Bool)
    (heq : ∀ i : Fin m, signs (t+i.val) = bits i) :
    curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F tape m t s bits =
      curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F tape signs m t s := by
  induction m generalizing t s with
  | zero => rfl
  | succ m ih =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    have hp : r.cache.1 = s.1 := curvatureFirstInspect_point hBg hBH P ε γ scaleG scaleH F tape t s
    have hh : signs t = bits 0 := by simpa only [Fin.val_zero,Nat.add_zero] using heq 0
    have ht : ∀ i : Fin m, signs (t+1+i.val) = Fin.tail bits i := by
      intro i
      simpa only [Fin.val_succ,Fin.tail,Nat.add_assoc,Nat.add_comm 1] using heq i.succ
    simp only [curvatureFirstFiniteExecute,curvatureFirstExecute,
      show curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s = r from rfl,
      curvatureFirstAdvance,hp,hh]
    cases r.action with
    | success => rfl
    | gradient g => exact ih (t+1) _ (Fin.tail bits) ht
    | curvature v => exact ih (t+1) _ (Fin.tail bits) ht

theorem curvatureFirstFiniteExecute_sosp {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (f : Point d → ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (m t : ℕ) (s : OptimizerCache d) (bits : Fin m → Bool)
    (hv : curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F tape m t s bits)
    {x : Point d} (ho : curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F tape m t s bits = some x) :
    IsSOSP f ε γ x := by
  induction m generalizing t s with
  | zero => cases ho
  | succ m ih =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    simp only [curvatureFirstFiniteValid,curvatureFirstFiniteExecute,
      show curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s = r from rfl] at hv ho
    cases ha : r.action with
    | success =>
      simp only [ha] at hv ho
      cases Option.some.inj ho
      exact hv.1
    | gradient g =>
      simp only [ha] at hv ho
      exact ih (t+1) _ (Fin.tail bits) hv.2 ho
    | curvature v =>
      simp only [ha] at hv ho
      exact ih (t+1) _ (Fin.tail bits) hv.2 ho

theorem curvatureFirstShadow_counts_of_exhausted {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (m t : ℕ) (s : OptimizerCache d) (bits : Fin m → Bool)
    (hv : curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F tape m t s bits)
    (ho : curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F tape m t s bits = none) :
    let r := curvatureFirstShadow hBg hBH P ε γ scaleG scaleH f F tape m t s bits
    r.gradientSteps+r.curvatureSteps = m := by
  induction m generalizing t s with
  | zero => rfl
  | succ m ih =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    simp only [curvatureFirstFiniteValid,curvatureFirstFiniteExecute,
      show curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s = r from rfl] at hv ho
    simp only [curvatureFirstShadow,
      show curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s = r from rfl,if_pos hv.1]
    cases ha : r.action with
    | success => simp only [ha] at ho; cases ho
    | gradient g =>
      simp only [ha] at hv ho ⊢
      have hi := ih (t+1) _ (Fin.tail bits) hv.2 ho
      simp only [CurvatureShadowResult.addAction]
      omega
    | curvature v =>
      simp only [ha] at hv ho ⊢
      have hi := ih (t+1) _ (Fin.tail bits) hv.2 ho
      simp only [CurvatureShadowResult.addAction]
      omega

end
end SampleReuse
