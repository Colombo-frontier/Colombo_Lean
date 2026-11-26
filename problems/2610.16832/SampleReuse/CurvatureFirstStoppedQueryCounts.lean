import SampleReuse.CurvatureFirstStoppedCounts
import SampleReuse.CurvatureFirstQueryCounts

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def stoppedInspectionQueryCounts {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : StoppedOptimizerCache d) : ℕ × ℕ :=
  if s.1 then let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2
    (r.gradientCalls,r.hessianCalls) else (0,0)

def curvatureStoppedQueryCounts {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) : ℕ → ℕ → StoppedOptimizerCache d → ℕ × ℕ
  | 0, _, _ => (0,0)
  | m+1, t, s => stoppedInspectionQueryCounts hBg hBH P ε γ scaleG scaleH F tape t s +
      curvatureStoppedQueryCounts hBg hBH P ε γ scaleG scaleH f F tape signs m (t+1)
        (curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s (signs t))

theorem curvatureStoppedQueryCounts_inactive {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (m t : ℕ) (s : OptimizerCache d) :
    curvatureStoppedQueryCounts hBg hBH P ε γ scaleG scaleH f F tape signs m t (false,s) = (0,0) := by
  induction m generalizing t with
  | zero => rfl
  | succ m ih => simp only [curvatureStoppedQueryCounts,stoppedInspectionQueryCounts,
      curvatureStoppedStep,Bool.false_eq_true,if_false,ih,zero_add]; rfl

theorem curvatureStoppedQueryCounts_eq_sum {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) (m t : ℕ) :
    curvatureStoppedQueryCounts hBg hBH P ε γ scaleG scaleH f F tape signs m t
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t) =
      ∑ i ∈ Finset.range m, stoppedInspectionQueryCounts hBg hBH P ε γ scaleG scaleH F tape (t+i)
        (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ (t+i)) := by
  induction m generalizing t with
  | zero => simp only [curvatureStoppedQueryCounts,Finset.range_zero,Finset.sum_empty]; rfl
  | succ m ih =>
    change stoppedInspectionQueryCounts hBg hBH P ε γ scaleG scaleH F tape t
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t) +
      curvatureStoppedQueryCounts hBg hBH P ε γ scaleG scaleH f F tape signs m (t+1)
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ (t+1)) = _
    rw [ih,Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show t+1+i=t+(i+1) by omega]

theorem curvatureStoppedQueryCounts_eq_actual_of_valid {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (m t : ℕ) (s : OptimizerCache d) (bits : Fin m → Bool)
    (heq : ∀ i : Fin m, signs (t+i.val) = bits i)
    (hv : curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F tape m t s bits) :
    curvatureStoppedQueryCounts hBg hBH P ε γ scaleG scaleH f F tape signs m t (true,s) =
      curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m t s := by
  induction m generalizing t s with
  | zero => rfl
  | succ m ih =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    have hp : r.cache.1 = s.1 := curvatureFirstInspect_point hBg hBH P ε γ scaleG scaleH F tape t s
    have hh : signs t = bits 0 := by simpa only [Fin.val_zero,Nat.add_zero] using heq 0
    have ht : ∀ i : Fin m, signs (t+1+i.val) = Fin.tail bits i := by
      intro i
      simpa only [Fin.val_succ,Fin.tail,Nat.add_assoc,Nat.add_comm 1] using heq i.succ
    change ValidInspection f ε γ s.1 r.action ∧ _ at hv
    simp only [curvatureStoppedQueryCounts,stoppedInspectionQueryCounts,curvatureStoppedStep,
      curvatureFirstDerivativeCounts,show curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s=r from rfl,
      if_pos rfl,if_pos hv.1,curvatureFirstAdvance,hp,hh,if_true]
    cases ha : r.action with
    | success => simp only [ha,curvatureStoppedQueryCounts_inactive]
    | gradient g =>
      simp only [ha]
      congr 1
      exact ih (t+1) _ (Fin.tail bits) ht (by simpa only [r,curvatureFirstFiniteValid,ha] using hv.2)
    | curvature v =>
      simp only [ha]
      congr 1
      exact ih (t+1) _ (Fin.tail bits) ht (by simpa only [r,curvatureFirstFiniteValid,ha] using hv.2)

end
end SampleReuse
