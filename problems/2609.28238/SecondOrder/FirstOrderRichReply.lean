import SecondOrder.FirstOrderSampleRegularity

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

instance firstOrderSpace_measurableSpace (d T : ℕ) : MeasurableSpace (FirstOrderSpace d T) :=
  borel (FirstOrderSpace d T)

instance firstOrderSpace_borelSpace (d T : ℕ) : BorelSpace (FirstOrderSpace d T) := ⟨rfl⟩

abbrev FirstOrderRichResponse (d T : ℕ) :=
  ℝ × FirstOrderSpace d T × (FirstOrderSpace d T →L[ℝ] FirstOrderSpace d T)

/-- The full reply is evaluated from one conservative sampled scalar loss. -/
def firstOrderRichReply (Θ : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (x : FirstOrderSpace d T) : FirstOrderRichResponse d T :=
  (firstOrderRandomLoss Θ z x, gradient (firstOrderRandomLoss Θ z) x,
    fderiv ℝ (gradient (firstOrderRandomLoss Θ z)) x)

theorem firstOrderRichReply_continuous (Θ : Fin (T+1) → (Fin d → Bool)) {R : ℝ}
    (z : FirstOrderCoefficients d T R) : Continuous (firstOrderRichReply Θ z) := by
  have hf := firstOrderRandomLoss_contDiff Θ z
  have hg : ContDiff ℝ 1 (gradient (firstOrderRandomLoss Θ z)) :=
    (InnerProductSpace.toDual ℝ (FirstOrderSpace d T)).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 3 by decide))
  exact hf.continuous.prodMk (hg.continuous.prodMk (hg.continuous_fderiv (by norm_num)))

private theorem measurable_finite_family {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [Countable A] [MeasurableSingletonClass A]
    (f : A → B → C) (hf : ∀ a, Measurable (f a)) :
    Measurable (fun w : A × B => f w.1 w.2) := by
  have hh : Measurable (fun w : B × A => f w.2 w.1) := measurable_from_prod_countable hf
  exact hh.comp measurable_swap

theorem firstOrderRichReply_measurable (Θ : Fin (T+1) → (Fin d → Bool)) (R : ℝ) :
    Measurable (fun w : FirstOrderCoefficients d T R × FirstOrderSpace d T => firstOrderRichReply Θ w.1 w.2) := by
  apply measurable_finite_family (firstOrderRichReply Θ)
  intro z
  exact (firstOrderRichReply_continuous Θ z).measurable

end
end SecondOrder

