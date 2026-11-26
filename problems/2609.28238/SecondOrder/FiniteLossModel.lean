import SecondOrder.FiniteMeanCalculus

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {d : ℕ}

theorem finiteLoss_reply_measurable (f : Ω → Point d → ℝ) (hf : ∀ z, ContDiff ℝ 2 (f z)) :
    Measurable (fun w : Ω × Point d => richReply f w.1 w.2) := by
  have hh : Measurable (fun w : Point d × Ω => richReply f w.2 w.1) := by
    apply measurable_from_prod_countable
    intro z
    have hg : ContDiff ℝ 1 (gradient (f z)) :=
      (InnerProductSpace.toDual ℝ (Point d)).symm.toContinuousLinearEquiv.contDiff.comp
        ((hf z).fderiv_right (by norm_num))
    exact ((hf z).continuous.prodMk
      (hg.continuous.prodMk (hg.continuous_fderiv (by norm_num)))).measurable
  exact hh.comp measurable_swap

/-- Finite, smooth, unbiased scalar losses with uniform field bounds satisfy
all the measurability, integrability, variance, and common-null-set clauses. -/
theorem finiteCommonLoss_of_uniformBounds (p : PMF Ω) (P : Parameters) {ν : ℝ}
    (hν : 0<ν) (hν1 : ν≤1) (F : Point d → ℝ) (f : Ω → Point d → ℝ)
    (hf : ∀ z, ContDiff ℝ 2 (f z))
    (hreg : ∀ z, ∃ C : ℝ, 0≤C ∧ ∀ x y, ‖hessian (f z) x-hessian (f z) y‖≤C*‖x-y‖)
    (hmean : ∀ x, (∫ z, f z x ∂p.toMeasure)=F x)
    (hgap : ∀ x, F 0-F x≤P.gap)
    (hLip : ∀ x y, ‖gradient F x-gradient F y‖≤P.gradientLip*‖x-y‖)
    (hHolder : ∀ x y, ‖hessian F x-hessian F y‖≤P.hessianHolder*‖x-y‖^ν)
    (hgerr : ∀ z x, ‖gradient (f z) x-gradient F x‖≤P.gradientNoise)
    (hHerr : ∀ z x, ‖hessian (f z) x-hessian F x‖≤min P.hessianNoise P.hessianBound) :
    CommonLoss p.toMeasure P ν F f := by
  have hfun : (fun x => ∫ z, f z x ∂p.toMeasure)=F := funext hmean
  have hF : ContDiff ℝ 2 F := by
    rw [← hfun]
    exact contDiff_finiteMean p f 2 hf
  have hm := finiteLoss_reply_measurable f hf
  refine ⟨hν,hν1,hF,hgap,hLip,hHolder,hm.fst,hm.snd.fst,hm.snd.snd,
    Filter.Eventually.of_forall (fun z => ⟨hf z,hreg z⟩),
    (fun _ => Integrable.of_finite), (fun _ => Integrable.of_finite), (fun _ => Integrable.of_finite),
    hmean, ?_, ?_, (fun _ => Integrable.of_finite), ?_,
    (fun _ _ => Integrable.of_finite), ?_, ?_⟩
  · intro x
    have hh := gradient_finiteMean p f x (fun z => (hf z).differentiable (by norm_num) x)
    rw [hfun] at hh
    exact hh.symm
  · intro x
    have hh := fderiv_gradient_finiteMean p f x hf
    rw [hfun] at hh
    exact hh.symm
  · intro x
    calc
      _ ≤ ∫ _z : Ω, P.gradientNoise^2 ∂p.toMeasure := by
        apply integral_mono Integrable.of_finite (integrable_const _)
        intro z
        exact pow_le_pow_left₀ (norm_nonneg _) (hgerr z x) 2
      _ = _ := by simp
  · intro x v
    calc
      _ ≤ ∫ _z : Ω, P.hessianNoise^2*‖v‖^2 ∂p.toMeasure := by
        apply integral_mono Integrable.of_finite (integrable_const _)
        intro z
        have hn := ((hessian (f z) x-hessian F x).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right ((hHerr z x).trans (min_le_left _ _)) (norm_nonneg v))
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := by simp
  · exact Filter.Eventually.of_forall (fun z x => (hHerr z x).trans (min_le_right _ _))

theorem finiteRichCommonLoss_of_valueBound (p : PMF Ω) (P : Parameters) {σ₀ : ℝ}
    (hσ₀ : 0<σ₀) (F : Point d → ℝ) (f : Ω → Point d → ℝ)
    (h : CommonLoss p.toMeasure P 1 F f) (hv : ∀ z x, |f z x-F x|≤σ₀) :
    RichCommonLoss p.toMeasure P σ₀ F f := by
  refine ⟨h,hσ₀,(fun _ => Integrable.of_finite),?_⟩
  intro x
  calc
    _ ≤ ∫ _z : Ω, σ₀^2 ∂p.toMeasure := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro z
      exact pow_le_pow_left₀ (abs_nonneg _) (hv z x) 2
    _ = _ := by simp

end
end SecondOrder
