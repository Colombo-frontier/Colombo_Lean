import Bilevel.ChiJointConservativeOracle

/-! Exact gradients are conservative full original SFOs with any declared
nonnegative variance budget. Both complete derivative blocks are retained. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiPrimitive
open PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

def exactGradientOracle (f : Joint X Y → ℝ) (hf : ContDiff ℝ 3 f) (σ : ℝ) :
    FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y) (Measure.dirac ()) σ where
  truth := gradient f
  sample := fun q (_ : Unit) => gradient f q
  truth_measurable := (GradientJetBounds.gradient_contDiff hf).continuous.measurable
  sample_measurable := (GradientJetBounds.gradient_contDiff hf).continuous.measurable.comp measurable_fst
  square_integrable := by intro q;simp
  mean := by intro q;simp
  variance := by intro q;simp only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0),integral_zero];positivity

omit [SecondCountableTopology (Joint X Y)] in
theorem full_joint_oracles_exact {μ Lf Lg Cf ρ : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (f g : Joint X Y → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (hPf : ∀ x y,P.f x y=f (pack x y)) (hPg : ∀ x y,P.g x y=g (pack x y))
    (σf σg : ℝ) :
    ∃ Of : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y) (Measure.dirac ()) σf,
    ∃ Og : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y) (Measure.dirac ()) σg,
      (∀ q,Of.truth q=pack (P.fx q.fst q.snd) (P.fy q.fst q.snd)) ∧
      (∀ q,Og.truth q=pack (P.gx q.fst q.snd) (P.gy q.fst q.snd)) ∧
      ∀ q coin,(Of.sample q coin,Og.sample q coin)=(gradient f q,gradient g q) := by
  refine ⟨exactGradientOracle f hf σf,exactGradientOracle g hg σg,?_,?_,fun _ _ => rfl⟩
  · exact ChiUpperNoise.upper_full_gradient P f (hf.differentiable (by norm_num)) hPf
  · exact lower_full_gradient P g (hg.differentiable (by norm_num)) hPg

end Bilevel.ChiPrimitive
