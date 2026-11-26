import SampleReuse.Model
import SecondOrder.FiniteLossModel

/-! Finite common scalar losses satisfying the manuscript's stronger sample bounds. -/

open MeasureTheory SecondOrder
namespace SampleReuse
noncomputable section
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {d : ℕ}

/-- The derivative fields are obtained from the same scalar loss. Uniform
sample bounds yield a single probability-one set valid for all queries. -/
theorem finite_admissible_of_uniform_bounds (p : PMF Ω) (P : Parameters)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (x₀ : Point d)
    (hF : ∀ z, ContDiff ℝ 2 (F z))
    (hmean : ∀ x, (∫ z, F z x ∂p.toMeasure) = f x)
    (hgap : ∀ x, f x₀ - f x ≤ P.gap)
    (hLip : ∀ z x y, ‖gradient (F z) x - gradient (F z) y‖ ≤ P.gradientLip * ‖x - y‖)
    (hHess : ∀ z x y, ‖hessian (F z) x - hessian (F z) y‖ ≤ P.hessianLip * ‖x - y‖)
    (hgerr : ∀ z x, ‖gradient (F z) x - gradient f x‖ ≤ P.gradientNoise)
    (hHerr : ∀ z x, ‖hessian (F z) x - hessian f x‖ ≤ P.hessianNoise)
    (hgrad : ∀ x, ‖gradient f x‖ ≤ P.gradientBound) :
    Admissible p.toMeasure P f F x₀ := by
  have he : (fun x => ∫ z, F z x ∂p.toMeasure) = f := funext hmean
  have hf : ContDiff ℝ 2 f := by
    rw [← he]
    exact contDiff_finiteMean p F 2 hF
  have hm := finiteLoss_reply_measurable F hF
  refine ⟨hf, hgap, hm.fst, hm.snd.fst, hm.snd.snd,
    Filter.Eventually.of_forall (fun z => ⟨hF z, hLip z, hHess z⟩),
    (fun _ => Integrable.of_finite), (fun _ => Integrable.of_finite),
    (fun _ => Integrable.of_finite), hmean, ?_, ?_,
    Filter.Eventually.of_forall (fun z x => ⟨hgerr z x, hHerr z x⟩), hgrad⟩
  · intro x
    have hh := gradient_finiteMean p F x (fun z => (hF z).differentiable (by norm_num) x)
    rw [he] at hh
    exact hh.symm
  · intro x
    have hh := fderiv_gradient_finiteMean p F x hF
    rw [he] at hh
    exact hh.symm

end
end SampleReuse
