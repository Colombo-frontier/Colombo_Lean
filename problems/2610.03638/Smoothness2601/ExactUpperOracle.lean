import Smoothness2601.CoordinateMinimax
import Smoothness2601.SineOracle

/-! The exact-upper-gradient restriction is an actual almost-sure property
of the original full-gradient law, valid at every query and hidden history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.PrimitiveGeometry
namespace Smoothness2601.ExactUpper

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {H : Type} [MeasurableSpace H]

def IsExact (O : Adaptive.Oracle P H) : Prop :=
  ∀ (x : X) (y : Y) (h : H), ∀ᵐ z ∂O.law ((false,(x,y)),h), z.1 = P.grad_f (pack x y)

omit [BorelSpace X] [SecondCountableTopology Y] in
theorem coordinate_transport (e : Z ≃ₗᵢ[ℝ] Y) (O : Adaptive.Oracle P H) (hO : IsExact P O) :
    IsExact (CoordinatePopulation.transport P e) (CoordinateOracle.transport P e O) := by
  intro x y h
  change ∀ᵐ z ∂CoordinateOracle.law P e O ((false,(x,y)),h), _
  rw [CoordinateOracle.law_apply]
  apply (ae_map_iff (CoordinateOracle.reply_measurable e).aemeasurable
    (measurable_fst (measurableSet_singleton _))).mpr
  filter_upwards [hO x (e y) h] with z hz
  change (CoordinateGeometry.joint (X := X) e).symm z.1 =
    (CoordinateGeometry.joint (X := X) e).symm (P.grad_f (pack x (e y)))
  rw [hz]

theorem freshBernoulli (signal : Adaptive.Query X Y → Joint X Y) (hs : Measurable signal)
    {B : ℝ} (hB : 0 < B) (hsmall : B ≤ b.σ) (henv : ∀ q, ‖signal q‖ ≤ B) :
    IsExact P (FreshBernoulli.oracle P signal hs hB hsmall henv) := by
  intro x y h
  change ∀ᵐ z ∂FreshBernoulli.law P signal _ _ ((false,(x,y)),h), _
  rw [FreshBernoulli.law_apply P signal hs]
  apply (ae_map_iff (measurable_of_finite _).aemeasurable
    (measurable_fst (measurableSet_singleton _))).mpr
  filter_upwards with coin
  exact FreshBernoulli.sample_upper P signal _ (x,y) coin

end Smoothness2601.ExactUpper
