import SampleReuse.CurvatureFirstOutputMeasurable
import SampleReuse.CurvatureFirstQueryCounts

open MeasureTheory SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section

theorem checkpointCalls_measurable {A E : Type} [MeasurableSpace A]
    [MeasurableSpace E] {d B : ℕ} (scale σ L : ℝ)
    (k : A → ℕ) (hk : Measurable k) (cache : A → TreeCache d E) (hc : Measurable cache)
    (x : A → Point d) (hx : Measurable x) :
    Measurable (fun a => checkpointCalls (B := B) scale σ L (k a) (cache a) (x a)) := by
  apply measurable_natChoice (fun j a => checkpointCalls (B := B) scale σ L j (cache a) (x a)) _ k hk
  intro j
  by_cases hj : j=0
  · simp only [checkpointCalls,if_pos hj]
    exact measurable_const
  · simp only [checkpointCalls,checkpointBatchSize,if_neg hj]
    exact measurable_const.mul (chordBatchSize_measurable scale σ L x _ hx
      (((measurable_pi_apply (ancestorParent j)).comp hc).fst))

theorem curvatureFirstInspect_counts_as_ite {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : OptimizerCache d) :
    ((curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).gradientCalls,
      (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).hessianCalls) =
      (if curvatureTag (sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F tape t s))
        then 0 else checkpointCalls (B := Bg) scaleG P.gradientNoise P.gradientLip s.2.1 s.2.2.1 s.1,
        checkpointCalls (B := BH) scaleH P.hessianNoise P.hessianLip t s.2.2.2 s.1) := by
  simp only [curvatureFirstInspect,inspectionHessian]
  split_ifs <;> rfl

theorem curvatureFirstInspect_counts_measurable {Ω A : Type}
    [MeasurableSpace Ω] [MeasurableSpace A] {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ)
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (t : ℕ) (s : A → OptimizerCache d) (hs : Measurable s)
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (ht : Measurable tape) :
    Measurable (fun a =>
      ((curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F (tape a) t (s a)).gradientCalls,
       (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F (tape a) t (s a)).hessianCalls)) := by
  simp_rw [curvatureFirstInspect_counts_as_ite]
  have hflag : MeasurableSet {a | curvatureTag (sourceCurvatureSelector (3*γ/4)
      (inspectionHessian hBH P scaleH F (tape a) t (s a))) = true} :=
    ((curvatureTag_measurable.comp (sourceCurvatureSelector_measurable (3*γ/4))).comp
      (inspectionHessian_measurable hBH P scaleH F hFH t s hs tape ht)) (measurableSet_singleton true)
  exact (Measurable.ite hflag measurable_const
    (checkpointCalls_measurable scaleG P.gradientNoise P.gradientLip _ hs.snd.fst
      _ hs.snd.snd.fst _ hs.fst)).prodMk
    (checkpointCalls_measurable scaleH P.hessianNoise P.hessianLip _ measurable_const
      _ hs.snd.snd.snd _ hs.fst)

theorem curvatureFirstDerivativeCounts_succ_as_ite {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (m t : ℕ) (s : OptimizerCache d) :
    curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs (m+1) t s =
      ((curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).gradientCalls,
       (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).hessianCalls) +
      if (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).action = .success
      then (0,0) else curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m (t+1)
        (curvatureMacroAdvance P ε γ (signs t) (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s)) := by
  rw [curvatureFirstDerivativeCounts]
  cases ha : (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).action <;>
    simp only [curvatureFirstAdvance,ha,curvatureMacroAdvance,inspectionNextPoint,
      reduceCtorEq,if_true,if_false]

theorem curvatureFirstDerivativeCounts_measurable {Ω A : Type}
    [MeasurableSpace Ω] [MeasurableSpace A] {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (htape : Measurable tape)
    (signs : A → ℕ → Bool) (hsigns : Measurable signs) (m t : ℕ)
    (s : A → OptimizerCache d) (hs : Measurable s) :
    Measurable (fun a => curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F (tape a) (signs a) m t (s a)) := by
  induction m generalizing t s with
  | zero => exact measurable_const
  | succ m ih =>
    simp_rw [curvatureFirstDerivativeCounts_succ_as_ite]
    apply Measurable.add (curvatureFirstInspect_counts_measurable hBg hBH P ε γ scaleG scaleH F hFH t s hs tape htape)
    apply Measurable.ite (curvatureFirstInspect_success_measurableSet hBg hBH P ε γ scaleG scaleH F
      hFg hFH t s hs tape htape) measurable_const
    apply ih (t+1) _
    exact curvatureMacroAdvance_inspection_measurable hBg hBH P ε γ scaleG scaleH F hFg hFH
      t s hs _ ((measurable_pi_apply t).comp hsigns) tape htape

end
end SampleReuse
