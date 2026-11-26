import SampleReuse.BoundedCheckpointTime
import SampleReuse.CurvatureFirstTapes
import SampleReuse.CurvatureFirstTrajectoryMeasurable

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

def macroGradientTime {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    (k : ℕ) (g : SampleTape ((T+1)*Bg) Ω) : ℕ :=
  boundedClockTime (fun t =>
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).2.1) k T

def macroGradientLocation {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    (k : ℕ) (g : SampleTape ((T+1)*Bg) Ω) : Point d :=
  let t := macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g
  if t ≤ T then (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).1 else 0

theorem macroGradientTime_depends {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    {k : ℕ} (hk : k ≤ T) (g g' : SampleTape ((T+1)*Bg) Ω)
    (heq : ∀ r ∈ treePastHandles T Bg k, g r = g' r) :
    macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g =
      macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g' := by
  apply boundedClockTime_congr
  intro t
  apply curvatureMacroRun_gradient_clock_event
  · intro j i; simp only [derivativeTapes_hessian]
  · intro j hj i
    simp only [derivativeTapes_gradient]
    exact heq _ (treeBlockHandle_in_past (hj.le.trans hk) hj i)

theorem macroGradientLocation_depends {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    {k : ℕ} (hk : k ≤ T) (g g' : SampleTape ((T+1)*Bg) Ω)
    (heq : ∀ r ∈ treePastHandles T Bg k, g r = g' r) :
    macroGradientLocation hBg hBH P ε γ scaleG scaleH F h signs x₀ k g =
      macroGradientLocation hBg hBH P ε γ scaleG scaleH F h signs x₀ k g' := by
  have ht := macroGradientTime_depends hBg hBH P ε γ scaleG scaleH F h signs x₀ hk g g' heq
  unfold macroGradientLocation
  rw [← ht]
  dsimp only
  split_ifs
  · apply congrArg Prod.fst
    apply curvatureMacroRun_depends_gradient_past (k := k)
    · intro j i; simp only [derivativeTapes_hessian]
    · intro j hj i
      simp only [derivativeTapes_gradient]
      exact heq _ (treeBlockHandle_in_past (hj.le.trans hk) hj i)
    · exact boundedClockTime_clock_le (fun t =>
        (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).2.1) k T rfl
  · rfl

theorem macroGradientLocation_predictable {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d) :
    PredictableLocations (macroGradientLocation hBg hBH P ε γ scaleG scaleH F h signs x₀) := by
  constructor
  · intro k _
    have hm (t : ℕ) : Measurable (fun g : SampleTape ((T+1)*Bg) Ω =>
        curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t) :=
      (curvatureMacroRun_measurable hBg hBH P ε γ scaleG scaleH F hFg hFH x₀ t).comp
      (((derivativeTapes_measurable _ _).comp (measurable_id.prodMk measurable_const)).prodMk measurable_const)
    have ht : Measurable (macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k) :=
      boundedClockTime_measurable _ (fun t => (hm t).snd.fst) k T
    have hx := measurable_natChoice _ (fun t => (hm t).fst) _ ht
    exact Measurable.ite (measurableSet_le ht measurable_const) hx measurable_const
  · intro k hk g g' heq
    exact macroGradientLocation_depends hBg hBH P ε γ scaleG scaleH F h signs x₀ hk g g' heq

end
end SampleReuse
