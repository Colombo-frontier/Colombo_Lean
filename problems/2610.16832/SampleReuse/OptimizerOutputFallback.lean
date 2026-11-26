import SampleReuse.CurvatureFirstOutputMeasurable

open MeasureTheory SecondOrder
namespace SampleReuse
noncomputable section

/-- A capped run returns its actual point on success and the fixed initial
point on exhaustion; the resulting point-valued algorithm is measurable. -/
theorem optimizerOutput_getD_measurable {d : ℕ} (x₀ : Point d) :
    Measurable (fun o : Option (Point d) => o.getD x₀) := by
  have he : Measurable (Equiv.optionEquivSumPUnit.{0,0} (Point d)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hs : Measurable (Sum.elim id (fun _ : PUnit => x₀)) :=
    measurable_id.sumElim measurable_const
  convert hs.comp he using 1
  funext o
  cases o <;> rfl

theorem curvatureFirstExecute_fallback_measurable {Ω A : Type}
    [MeasurableSpace Ω] [MeasurableSpace A] {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (htape : Measurable tape)
    (signs : A → ℕ → Bool) (hsigns : Measurable signs) (m t : ℕ)
    (s : A → OptimizerCache d) (hs : Measurable s) (x₀ : Point d) :
    Measurable (fun a =>
      (curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F (tape a) (signs a) m t (s a)).getD x₀) :=
  (optimizerOutput_getD_measurable x₀).comp
    (curvatureFirstExecute_measurable hBg hBH P ε γ scaleG scaleH F hFg hFH tape htape signs hsigns m t s hs)

end
end SampleReuse
