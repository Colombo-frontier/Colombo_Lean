import SampleReuse.CurvatureFirstAccuracyEvents
import SampleReuse.CurvatureFirstPolicy

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem curvatureFirstInspect_success_iff {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : OptimizerCache d) :
    (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).action = .success ↔
      curvatureTag (sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F tape t s)) = false ∧
        ‖inspectionGradient hBg P scaleG F tape s‖ ≤ 3*ε/4 := by
  simp only [curvatureFirstInspect,inspectionHessian,inspectionGradient]
  split_ifs <;> simp_all

theorem curvatureFirstExecute_succ_as_ite {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (m t : ℕ) (s : OptimizerCache d) :
    curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F tape signs (m+1) t s =
      if (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).action = .success
      then some s.1 else curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F tape signs m (t+1)
        (curvatureMacroAdvance P ε γ (signs t) (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s)) := by
  rw [curvatureFirstExecute]
  cases ha : (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).action <;>
    simp only [curvatureFirstAdvance,ha,curvatureMacroAdvance,inspectionNextPoint,
      reduceCtorEq,if_true,if_false]

theorem curvatureFirstInspect_success_measurableSet {Ω A : Type}
    [MeasurableSpace Ω] [MeasurableSpace A] {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (t : ℕ) (s : A → OptimizerCache d) (hs : Measurable s)
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (ht : Measurable tape) :
    MeasurableSet {a | (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F (tape a) t (s a)).action = .success} := by
  simp only [curvatureFirstInspect_success_iff]
  exact (((curvatureTag_measurable.comp (sourceCurvatureSelector_measurable (3*γ/4))).comp
      (inspectionHessian_measurable hBH P scaleH F hFH t s hs tape ht)) (measurableSet_singleton false)).inter
    (measurableSet_le (inspectionGradient_measurable hBg P scaleG F hFg s hs tape ht).norm measurable_const)

theorem curvatureFirstExecute_measurable {Ω A : Type}
    [MeasurableSpace Ω] [MeasurableSpace A] {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (htape : Measurable tape)
    (signs : A → ℕ → Bool) (hsigns : Measurable signs) (m t : ℕ)
    (s : A → OptimizerCache d) (hs : Measurable s) :
    Measurable (fun a => curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F (tape a) (signs a) m t (s a)) := by
  induction m generalizing t s with
  | zero => exact measurable_const
  | succ m ih =>
    simp_rw [curvatureFirstExecute_succ_as_ite]
    apply Measurable.ite (curvatureFirstInspect_success_measurableSet hBg hBH P ε γ scaleG scaleH F
      hFg hFH t s hs tape htape) ((optimizerOutput_some_measurable d).comp hs.fst)
    apply ih (t+1) _
    exact curvatureMacroAdvance_inspection_measurable hBg hBH P ε γ scaleG scaleH F hFg hFH
      t s hs _ ((measurable_pi_apply t).comp hsigns) tape htape

theorem optimizerOutput_none_measurableSet (d : ℕ) :
    MeasurableSet ({none} : Set (Option (Point d))) := by
  change ∃ s, MeasurableSet s ∧ (Equiv.optionEquivSumPUnit.{0,0} (Point d)) ⁻¹' s = {none}
  refine ⟨Set.range Sum.inr,measurableSet_range_inr,?_⟩
  ext x
  cases x <;> simp

end
end SampleReuse
