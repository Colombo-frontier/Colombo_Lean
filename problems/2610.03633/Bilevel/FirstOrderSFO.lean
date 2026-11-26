import Bilevel.FreshOracle

/-! Original full-gradient SFO laws, with the Euclidean sum-of-squares variance
of both blocks. Reading either block of one original call gives the component
oracle used by the fully first-order algorithms. -/

noncomputable section
open MeasureTheory

namespace Bilevel.FirstOrderSFO

variable {Query Seed X Y : Type*} [MeasurableSpace Query] [MeasurableSpace Seed]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

structure Oracle (ν : Measure Seed) (σ : ℝ) where
  truth_x : Query → X
  truth_y : Query → Y
  sample_x : Query → Seed → X
  sample_y : Query → Seed → Y
  truth_x_measurable : Measurable truth_x
  truth_y_measurable : Measurable truth_y
  sample_x_measurable : Measurable (fun qs : Query × Seed => sample_x qs.1 qs.2)
  sample_y_measurable : Measurable (fun qs : Query × Seed => sample_y qs.1 qs.2)
  square_integrable : ∀ q, Integrable (fun s =>
    ‖sample_x q s - truth_x q‖ ^ 2 + ‖sample_y q s - truth_y q‖ ^ 2) ν
  mean_x : ∀ q, (∫ s, sample_x q s - truth_x q ∂ν) = 0
  mean_y : ∀ q, (∫ s, sample_y q s - truth_y q ∂ν) = 0
  variance : ∀ q, (∫ s,
    ‖sample_x q s - truth_x q‖ ^ 2 + ‖sample_y q s - truth_y q‖ ^ 2 ∂ν) ≤ σ ^ 2

namespace Oracle

variable {ν : Measure Seed} {σ : ℝ} (O : Oracle (Query := Query) (X := X) (Y := Y) ν σ)

omit [BorelSpace Y] [SecondCountableTopology Y] in
theorem x_square_integrable (q : Query) : Integrable (fun s => ‖O.sample_x q s - O.truth_x q‖ ^ 2) ν := by
  apply (O.square_integrable q).mono'
    ((((O.sample_x_measurable.comp (measurable_const.prodMk measurable_id)).sub measurable_const).norm.pow_const 2).aestronglyMeasurable)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact le_add_of_nonneg_right (sq_nonneg _)

omit [BorelSpace X] [SecondCountableTopology X] in
theorem y_square_integrable (q : Query) : Integrable (fun s => ‖O.sample_y q s - O.truth_y q‖ ^ 2) ν := by
  apply (O.square_integrable q).mono'
    ((((O.sample_y_measurable.comp (measurable_const.prodMk measurable_id)).sub measurable_const).norm.pow_const 2).aestronglyMeasurable)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- One original full-gradient call, retaining its x block. -/
def xOracle : FreshOracle.Oracle (Query := Query) (E := X) ν σ where
  truth := O.truth_x
  sample := O.sample_x
  truth_measurable := O.truth_x_measurable
  sample_measurable := O.sample_x_measurable
  square_integrable := O.x_square_integrable
  mean := O.mean_x
  variance q := (integral_mono (O.x_square_integrable q) (O.square_integrable q)
    (fun _ => le_add_of_nonneg_right (sq_nonneg _))).trans (O.variance q)

/-- One original full-gradient call, retaining its y block. -/
def yOracle : FreshOracle.Oracle (Query := Query) (E := Y) ν σ where
  truth := O.truth_y
  sample := O.sample_y
  truth_measurable := O.truth_y_measurable
  sample_measurable := O.sample_y_measurable
  square_integrable := O.y_square_integrable
  mean := O.mean_y
  variance q := (integral_mono (O.y_square_integrable q) (O.square_integrable q)
    (fun _ => le_add_of_nonneg_left (sq_nonneg _))).trans (O.variance q)

end Oracle
end Bilevel.FirstOrderSFO

