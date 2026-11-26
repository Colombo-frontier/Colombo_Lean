import SampleReuse.CurvatureFirstCapSuccess
import SampleReuse.DerivativeTapeLaw
import SampleReuse.OptimizerOutputFallback

open MeasureTheory SecondOrder
open scoped Classical InnerProductSpace
namespace SampleReuse
noncomputable section

theorem cappedCurvatureFirstOutput_measurable {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH M : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d) (x₀ : Point d) (Cg CH : ℕ) :
    Measurable (fun w : SampleTape ((T+1)*Bg+(T+1)*BH) Ω × (Fin M → Bool) =>
      cappedCurvatureFirstOutput hBg hBH P ε γ scaleG scaleH F q₀ x₀ Cg CH w.1 w.2) := by
  let alg (bits : Fin M → Bool) := cappedCurvatureFirstAlgorithm hBg hBH P ε γ scaleG scaleH q₀
    (extendFiniteSigns bits) M 0 (optimizerInitial x₀) Cg CH
  have hp : MeasurableOracleAlgorithmFamily alg :=
    cappedCurvatureFirstAlgorithm_finite_measurable hBg hBH P ε γ scaleG scaleH q₀ x₀ Cg CH
  have hr := persistentRun_measurable (fun bits => (alg bits).toQueryPolicy)
    hp.toMeasurableQueryPolicyFamily F hFg hFH (Cg+CH)
  exact (hp.output (Cg+CH)).comp (measurable_snd.prodMk (hr.comp measurable_swap))

theorem actual_sosp_measurableSet {d : ℕ} {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) (ε γ : ℝ) : MeasurableSet {x | IsSOSP f ε γ x} := by
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  have hH := hg.continuous_fderiv (by norm_num)
  have hs : IsClosed {x | IsSOSP f ε γ x} := by
    change IsClosed ({x | ‖gradient f x‖ ≤ ε} ∩
      {x | ∀ v : Point d, -γ*‖v‖^2 ≤ ⟪fderiv ℝ (gradient f) x v,v⟫_ℝ})
    apply (isClosed_le hg.continuous.norm continuous_const).inter
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const ((hH.clm_apply continuous_const).inner continuous_const)
  exact hs.measurableSet

theorem cappedCurvatureFirstOutput_fallback_measurable {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH M : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d) (x₀ : Point d) (Cg CH : ℕ) :
    Measurable (fun w : SampleTape ((T+1)*Bg+(T+1)*BH) Ω × (Fin M → Bool) =>
      (cappedCurvatureFirstOutput hBg hBH P ε γ scaleG scaleH F q₀ x₀ Cg CH w.1 w.2).getD x₀) :=
  (optimizerOutput_getD_measurable x₀).comp
    (cappedCurvatureFirstOutput_measurable hBg hBH P ε γ scaleG scaleH F hFg hFH q₀ x₀ Cg CH)

/-- Successful optional outputs on the split tape law remain successful
actual point outputs under the one iid tape law of the source oracle. -/
theorem cappedCurvatureFirstOutput_fallback_probability {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH M : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (f : Point d → ℝ) (F : Ω → Point d → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d) (x₀ : Point d) (Cg CH : ℕ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (((sampleTapeLaw ((T+1)*Bg) μ).prod (sampleTapeLaw ((T+1)*BH) μ)).prod
      (PMF.uniformOfFintype (Fin M → Bool)).toMeasure).real {w | ∃ x,
        cappedCurvatureFirstOutput hBg hBH P ε γ scaleG scaleH F q₀ x₀ Cg CH
          (derivativeTapes w.1.1 w.1.2) w.2 = some x ∧ IsSOSP f ε γ x} ≤
    ((sampleTapeLaw ((T+1)*Bg+(T+1)*BH) μ).prod
      (PMF.uniformOfFintype (Fin M → Bool)).toMeasure).real {w | IsSOSP f ε γ
        ((cappedCurvatureFirstOutput hBg hBH P ε γ scaleG scaleH F q₀ x₀ Cg CH w.1 w.2).getD x₀)} := by
  let good := {w : SampleTape ((T+1)*Bg+(T+1)*BH) Ω × (Fin M → Bool) | IsSOSP f ε γ
    ((cappedCurvatureFirstOutput hBg hBH P ε γ scaleG scaleH F q₀ x₀ Cg CH w.1 w.2).getD x₀)}
  have hg : MeasurableSet good :=
    (cappedCurvatureFirstOutput_fallback_measurable hBg hBH P ε γ scaleG scaleH F hFg hFH q₀ x₀ Cg CH)
      (actual_sosp_measurableSet hf ε γ)
  have hp := derivativeTapes_signs_measurePreserving ((T+1)*Bg) ((T+1)*BH) μ
    (PMF.uniformOfFintype (Fin M → Bool)).toMeasure
  rw [← hp.measureReal_preimage hg.nullMeasurableSet]
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro w ⟨x,hx,hS⟩
  change IsSOSP f ε γ ((cappedCurvatureFirstOutput hBg hBH P ε γ scaleG scaleH F q₀ x₀ Cg CH
    (derivativeTapes w.1.1 w.1.2) w.2).getD x₀)
  simpa only [hx,Option.getD_some] using hS

end
end SampleReuse
