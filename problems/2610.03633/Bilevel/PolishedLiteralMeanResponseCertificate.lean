import Bilevel.PolishedLiteralSmallness
import Bilevel.PolishedLiteralMicroMean

/-! Unconditional quantitative exact-response certificate for the literal
hierarchical mean: all perturbation and normal-core conditions are derived
from the actual source hierarchy and one numerical smallness threshold. -/
noncomputable section
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ZeroChainSchedule

/-- The scale and schedule assumptions are exactly source construction
choices. No lower-Hessian, overlap, normal-core or solution conclusion is
assumed. This closes the explicit-response portion of `hier:thm:mean`. -/
theorem literal_exact_mean_response_certificate : ∃ τ Rho : ℝ,0<τ ∧ 1≤Rho ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (θ : ℝ),
      1≤θ → 0<P.μ → P.μ≤P.L → 0<P.β → P.β≤P.radius →
      P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.J=levels θ → P.δ=resolution (1/64) P.β θ → P.w=width (1/64) P.β θ →
      P.β*θ≤τ →
      (∀ y : PolishedLiteralCompensated.LowerSpace (Joint X U),
        ‖iteratedFDeriv ℝ 2 P.data.perturbation y‖≤P.μ/2) ∧
      (∀ y : PolishedLiteralCompensated.LowerSpace (Joint X U),
        ‖iteratedFDeriv ℝ 3 P.data.perturbation y‖≤Rho*P.μ*θ) ∧
      (∀ x v,
        (∀ y,PolishedLiteralJointMean.lower P.data x v (PolishedLiteralJointMean.response P.data x v)≤
          PolishedLiteralJointMean.lower P.data x v y) ∧
        (∀ y,PolishedLiteralJointMean.lower P.data x v y≤
          PolishedLiteralJointMean.lower P.data x v (PolishedLiteralJointMean.response P.data x v) →
          y=PolishedLiteralJointMean.response P.data x v)) ∧
      (∀ x v,PolishedLiteralJointMean.response P.data x v=
        pack ((P.L/P.μ) • v) (P.selectedResidual (pack x ((P.L/P.μ) • v))/P.L)) ∧
      (∀ x v,PolishedLiteralJointMean.upper P.data x v (PolishedLiteralJointMean.response P.data x v)=
        P.outerMean (P.L/P.μ) (pack x v)) ∧
      PolishedLiteralJointMean.response P.data (0:X) (0:U)=0 := by
  obtain ⟨τ,Rho,hτ,hRho,hcert⟩ := literal_numerical_smallness_certificate
  refine ⟨τ,Rho,hτ,hRho,?_⟩
  intro X U _ _ _ _ _ _ P θ hθ hμ hμL hβ hR hβb hbR hJ hδ hw hscale
  have hL : 0<P.L := hμ.trans_le hμL
  obtain ⟨hsecond,hthird,hcore⟩ := hcert X U P θ hθ hμ hL hβ hR hβb hbR hJ hδ hw hscale
  refine ⟨hsecond,hthird,fun x v => P.exact_unique_response hμ hμL hsecond hcore x v,
    fun x v => rfl,fun x v => ?_,P.exact_initialization⟩
  exact (P.outerMean_eq_actual_hyperobjective hL.ne' x v).symm

end Bilevel.PolishedLiteral
