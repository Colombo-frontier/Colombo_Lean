import SecondOrder.CurvatureSampleRegularity

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

instance curvatureSpace_measurableSpace (m T : ℕ) : MeasurableSpace (CurvatureSpace m T) :=
  borel (CurvatureSpace m T)

instance curvatureSpace_borelSpace (m T : ℕ) : BorelSpace (CurvatureSpace m T) := ⟨rfl⟩

abbrev CurvatureRichResponse (m T : ℕ) :=
  ℝ × CurvatureSpace m T × (CurvatureSpace m T →L[ℝ] CurvatureSpace m T)

/-- The full reply is evaluated from one conservative sampled scalar loss. -/
def curvatureRichReply (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (x : CurvatureSpace m T) : CurvatureRichResponse m T :=
  (curvatureRandomLoss Θ z x, gradient (curvatureRandomLoss Θ z) x,
    fderiv ℝ (gradient (curvatureRandomLoss Θ z)) x)

theorem curvatureRichReply_continuous (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) : Continuous (curvatureRichReply Θ z) := by
  have hf := curvatureRandomLoss_contDiff Θ z
  have hg : ContDiff ℝ 1 (gradient (curvatureRandomLoss Θ z)) :=
    (InnerProductSpace.toDual ℝ (CurvatureSpace m T)).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 3 by decide))
  exact hf.continuous.prodMk (hg.continuous.prodMk (hg.continuous_fderiv (by norm_num)))

private theorem measurable_finite_family {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [Countable A] [MeasurableSingletonClass A]
    (f : A → B → C) (hf : ∀ a, Measurable (f a)) :
    Measurable (fun w : A × B => f w.1 w.2) := by
  have hh : Measurable (fun w : B × A => f w.2 w.1) := measurable_from_prod_countable hf
  exact hh.comp measurable_swap

theorem curvatureRichReply_measurable (Θ : Fin (T+1) → BalancedVector m) (R : ℝ) :
    Measurable (fun w : CurvatureCoefficients m T R × CurvatureSpace m T => curvatureRichReply Θ w.1 w.2) := by
  apply measurable_finite_family (curvatureRichReply Θ)
  intro z
  exact (curvatureRichReply_continuous Θ z).measurable

end
end SecondOrder
