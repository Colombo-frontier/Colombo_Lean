import Bilevel.ChiExactJointOracle

/-! Exact conservative full oracles need no third derivative of the lower
scalar.  Gradient continuity follows from the same Primitive's smoothness. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiPrimitive
open PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)]

def exactContinuousGradientOracle (f : Joint X Y → ℝ) (hf : Continuous (gradient f)) (σ : ℝ) :
    FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y) (Measure.dirac ()) σ where
  truth := gradient f
  sample := fun q (_ : Unit) => gradient f q
  truth_measurable := hf.measurable
  sample_measurable := hf.measurable.comp measurable_fst
  square_integrable := by intro q;simp
  mean := by intro q;simp
  variance := by intro q;simp only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0),integral_zero];positivity

theorem full_joint_oracles_exact_differentiable {μ Lf Lg Cf ρ : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (f g : Joint X Y → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hPf : ∀ x y,P.f x y=f (pack x y)) (hPg : ∀ x y,P.g x y=g (pack x y))
    (σf σg : ℝ) :
    ∃ Of : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y) (Measure.dirac ()) σf,
    ∃ Og : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y) (Measure.dirac ()) σg,
      (∀ q,Of.truth q=pack (P.fx q.fst q.snd) (P.fy q.fst q.snd)) ∧
      (∀ q,Og.truth q=pack (P.gx q.fst q.snd) (P.gy q.fst q.snd)) ∧
      ∀ q coin,(Of.sample q coin,Og.sample q coin)=(gradient f q,gradient g q) := by
  have hfl : LipschitzWith ⟨Lf,P.Lf_nonneg⟩ (gradient f) := by
    apply LipschitzWith.of_dist_le_mul
    intro q q'
    simp only [dist_eq_norm,NNReal.coe_mk]
    rw [ChiUpperNoise.upper_full_gradient P f hf hPf,ChiUpperNoise.upper_full_gradient P f hf hPf]
    exact (full_gradient_lipschitz_iff P.fx P.fy P.Lf_nonneg).mpr P.smooth_f q.fst q'.fst q.snd q'.snd
  have hgl : LipschitzWith ⟨Lg,P.Lg_nonneg⟩ (gradient g) := by
    apply LipschitzWith.of_dist_le_mul
    intro q q'
    simp only [dist_eq_norm,NNReal.coe_mk]
    rw [lower_full_gradient P g hg hPg,lower_full_gradient P g hg hPg]
    exact (full_gradient_lipschitz_iff P.gx P.gy P.Lg_nonneg).mpr P.smooth_g q.fst q'.fst q.snd q'.snd
  refine ⟨exactContinuousGradientOracle f hfl.continuous σf,
    exactContinuousGradientOracle g hgl.continuous σg,?_,?_,fun _ _ => rfl⟩
  · exact ChiUpperNoise.upper_full_gradient P f hf hPf
  · exact lower_full_gradient P g hg hPg

end Bilevel.ChiPrimitive
