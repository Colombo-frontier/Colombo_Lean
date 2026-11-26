import Bilevel.ParametricPartialFixedPoint
import Bilevel.PartialLegendreJointInverse

/-! A globally Borel full partial-conjugate gradient evaluator. Equality
with the true partial conjugate is required only at the actual contractive
parameter. Invalid array data need no validity test or global derivative
budget in the evaluated function. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ParametricPartialConjugate
open PrimitiveGeometry PartialLegendre
variable {A X Y : Type*} [MeasurableSpace A]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

def inverse (G : A → Joint X Y → Joint X Y) : A × Joint X Y → Joint X Y :=
  ParametricPartialFixedPoint.inverse (fun p z => lowerLift (G p.1) z)
    Prod.snd (fun _ => 0)

def gradientReply (G : A → Joint X Y → Joint X Y) (p : A × Joint X Y) : Joint X Y :=
  lowerProjection p.2-G p.1 (inverse G p)

theorem inverse_measurable (G : A → Joint X Y → Joint X Y)
    (hm : Measurable (fun p : A × Joint X Y => G p.1 p.2)) : Measurable (inverse G) := by
  have ha : Measurable (fun p : (A × Joint X Y) × Joint X Y => (p.1.1,p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hg := (lowerProjection (X:=X) (Y:=Y)).continuous.measurable.comp (hm.comp ha)
  exact ParametricPartialFixedPoint.inverse_measurable _ Prod.snd (fun _ => 0)
    hg measurable_snd measurable_const

theorem gradientReply_measurable (G : A → Joint X Y → Joint X Y)
    (hm : Measurable (fun p : A × Joint X Y => G p.1 p.2)) : Measurable (gradientReply G) := by
  exact ((lowerProjection (X:=X) (Y:=Y)).continuous.measurable.comp measurable_snd).sub
    (hm.comp (measurable_fst.prodMk (inverse_measurable G hm)))

omit [MeasurableSpace A] [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)]
  [SecondCountableTopology (Joint X Y)] in
theorem inverse_eq_jointInverse (G : A → Joint X Y → Joint X Y)
    (a : A) {K : NNReal} (hK : K<1) (hG : LipschitzWith K (G a)) (w : Joint X Y) :
    inverse G (a,w)=jointInverse hG hK w := by
  exact (ParametricPartialFixedPoint.inverse_unique
    (fun p : A × Joint X Y => lowerLift (G p.1)) Prod.snd (fun _ => 0)
    (a,w) hK (lowerLift_lipschitz hG) _ (jointInverse_equation hG hK w)).symm

omit [MeasurableSpace A] [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)]
  [SecondCountableTopology (Joint X Y)] in
theorem gradientReply_eq_jointGradient (G : A → Joint X Y → Joint X Y)
    (a : A) {K : NNReal} (hK : K<1) (hG : LipschitzWith K (G a)) (w : Joint X Y) :
    gradientReply G (a,w)=jointGradient hG hK w := by
  rw [gradientReply,inverse_eq_jointInverse G a hK hG,jointGradient_representation]

omit [MeasurableSpace A] [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)]
  [SecondCountableTopology (Joint X Y)] in
theorem gradientReply_eq_gradient (G : A → Joint X Y → Joint X Y)
    (a : A) {K : NNReal} (hK : K<1) (hG : LipschitzWith K (G a))
    (P : Joint X Y → ℝ) (hP : ∀ w,HasGradientAt P (G a w) w) (w : Joint X Y) :
    gradientReply G (a,w)=gradient (jointConjugate hG hK P) w := by
  rw [gradientReply_eq_jointGradient G a hK hG,jointConjugate_gradient hG hK P hP]

end Bilevel.ParametricPartialConjugate
