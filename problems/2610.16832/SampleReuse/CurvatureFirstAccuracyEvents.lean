import SampleReuse.CurvatureFirstGradientAccuracy
import SampleReuse.CurvatureFirstHessianAccuracy

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem boundedClockTime_at_crossing (clock : ℕ → ℕ) (hm : Monotone clock)
    (T t : ℕ) (ht : t ≤ T) (hcross : clock (t+1) = clock t+1) :
    boundedClockTime clock (clock t) T = t := by
  have hle : boundedClockTime clock (clock t) T ≤ t :=
    Nat.find_min' _ (Or.inr (by omega))
  apply le_antisymm hle
  by_contra hn
  have hlt : boundedClockTime clock (clock t) T+1 ≤ t := by omega
  have hc := boundedClockTime_crosses clock (clock t) T (hle.trans ht)
  have hm' := hm hlt
  omega

theorem macroGradientTime_at_certificate {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (g : SampleTape ((T+1)*Bg) Ω) (h : SampleTape ((T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) (t : ℕ) (ht : t ≤ T)
    (hcert : sourceCurvatureSelector (3*γ/4)
      (inspectionHessian hBH P scaleH F (derivativeTapes g h) t
        (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t)) = .certificate) :
    macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).2.1 g = t := by
  apply boundedClockTime_at_crossing _
    (curvatureMacroRun_gradientIndex_mono hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀) T t ht
  change (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) t
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t)).cache.2.1 = _
  rw [curvatureFirstInspect_gradientClock,hcert]
  rfl

def MacroHessianAccurate {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH η : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (x₀ : Point d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) : Prop :=
  ∀ t ≤ T, let s := curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t
    ‖inspectionHessian hBH P scaleH F tape t s-hessian f s.1‖ ≤ η

def MacroGradientAccurate {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH η : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (x₀ : Point d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) : Prop :=
  ∀ t ≤ T, let s := curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t
    sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F tape t s) = .certificate →
    ‖inspectionGradient hBg P scaleG F tape s-gradient f s.1‖ ≤ η

theorem Admissible.curvatureFirst_gradient_macro_accuracy {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    (ε γ scaleG scaleH : ℝ) (z₀ : Ω) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hscale : scaleG = confidenceBatchScale d (η/(binaryDepth T+1)) (δ/(T+1)))
    (hcap : Bg = batchSize scaleG (P.gradientNoise^2))
    (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) :
    1-δ ≤ (sampleTapeLaw ((T+1)*Bg) μ).real {g |
      MacroGradientAccurate hBg hBH P ε γ scaleG scaleH η f F x₀ (derivativeTapes g h) signs} := by
  apply (had.curvatureFirst_gradient_accuracy hBg hBH ε γ scaleG scaleH z₀ hη hδ hscale hcap h signs).trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro g hg
  unfold MacroGradientAccurate
  intro t ht
  dsimp only
  intro hcert
  let k := (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).2.1
  have hk : k ≤ T :=
    (curvatureMacroRun_gradientIndex hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).trans ht
  have he := macroGradientTime_at_certificate hBg hBH P ε γ scaleG scaleH F g h signs x₀ t ht hcert
  have he' : macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g = t := he
  have hh := hg k hk (by rw [he']; exact ht)
  simpa only [he'] using hh

theorem inspectionHessian_measurable {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    {d T Bg BH : ℕ} (hBH : 0 < BH) (P : Parameters) (scaleH : ℝ)
    (F : Ω → Point d → ℝ) (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (t : ℕ) (s : A → OptimizerCache d) (hs : Measurable s)
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (ht : Measurable tape) :
    Measurable (fun a => inspectionHessian hBH P scaleH F (tape a) t (s a)) := by
  exact checkpointValue_measurable _ measurable_const _ hs.snd.snd.snd _
    (checkpointPacket_measurable hBH scaleH P.hessianNoise P.hessianLip _ hFH
      (hessianReserve T Bg BH) _ measurable_const _ hs.snd.snd.snd _ hs.fst tape ht)

theorem inspectionGradient_measurable {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    {d T Bg BH : ℕ} (hBg : 0 < Bg) (P : Parameters) (scaleG : ℝ)
    (F : Ω → Point d → ℝ) (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (s : A → OptimizerCache d) (hs : Measurable s)
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (ht : Measurable tape) :
    Measurable (fun a => inspectionGradient hBg P scaleG F (tape a) (s a)) := by
  exact checkpointValue_measurable _ hs.snd.fst _ hs.snd.snd.fst _
    (checkpointPacket_measurable hBg scaleG P.gradientNoise P.gradientLip _ hFg
      (gradientReserve T Bg BH) _ hs.snd.fst _ hs.snd.snd.fst _ hs.fst tape ht)

theorem Admissible.macroHessianAccurate_measurableSet {Ω A : Type}
    [MeasurableSpace Ω] [MeasurableSpace A] {d T Bg BH : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    (ε γ scaleG scaleH η : ℝ)
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (htape : Measurable tape)
    (signs : A → ℕ → Bool) (hsigns : Measurable signs) :
    MeasurableSet {a | MacroHessianAccurate hBg hBH P ε γ scaleG scaleH η f F x₀ (tape a) (signs a)} := by
  simp only [MacroHessianAccurate,Set.setOf_forall]
  apply MeasurableSet.iInter
  intro t
  apply MeasurableSet.iInter
  intro _
  have hs := (curvatureMacroRun_measurable hBg hBH P ε γ scaleG scaleH F
    had.gradient_measurable had.hessian_measurable x₀ t).comp (htape.prodMk hsigns)
  exact measurableSet_le ((inspectionHessian_measurable hBH P scaleH F had.hessian_measurable
    t _ hs tape htape).sub ((continuous_hessian had.population_smooth).measurable.comp hs.fst)).norm measurable_const

theorem Admissible.macroGradientAccurate_measurableSet {Ω A : Type}
    [MeasurableSpace Ω] [MeasurableSpace A] {d T Bg BH : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    (ε γ scaleG scaleH η : ℝ)
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (htape : Measurable tape)
    (signs : A → ℕ → Bool) (hsigns : Measurable signs) :
    MeasurableSet {a | MacroGradientAccurate hBg hBH P ε γ scaleG scaleH η f F x₀ (tape a) (signs a)} := by
  simp only [MacroGradientAccurate,Set.setOf_forall]
  apply MeasurableSet.iInter
  intro t
  apply MeasurableSet.iInter
  intro _
  have hs := (curvatureMacroRun_measurable hBg hBH P ε γ scaleG scaleH F
    had.gradient_measurable had.hessian_measurable x₀ t).comp (htape.prodMk hsigns)
  have hH := inspectionHessian_measurable hBH P scaleH F had.hessian_measurable t _ hs tape htape
  have hG := inspectionGradient_measurable hBg P scaleG F had.gradient_measurable _ hs tape htape
  have hc := (curvatureTag_measurable.comp
    ((sourceCurvatureSelector_measurable (3*γ/4)).comp hH)) (measurableSet_singleton false)
  have hg := measurableSet_le (hG.sub
    ((contDiff_gradient_one had.population_smooth).continuous.measurable.comp hs.fst)).norm
    (measurable_const : Measurable (fun _ : A => η))
  convert hc.compl.union hg using 1
  ext a
  simp only [Set.mem_setOf_eq,Set.mem_union,Set.mem_compl_iff,Set.mem_preimage,
    Set.mem_singleton_iff,imp_iff_not_or,Function.comp_def]
  cases sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F (tape a) t
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (tape a) (signs a) x₀ t)) <;>
    simp only [curvatureTag,Bool.false_eq_true,Bool.true_eq_false,not_true_eq_false,
      not_false_eq_true,false_or,true_or,reduceCtorEq]

end
end SampleReuse
