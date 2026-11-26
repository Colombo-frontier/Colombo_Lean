import Bilevel.PolishedLiteralLowerStrongConvex
import Bilevel.PolishedLiteralMeanResponseCertificate
import Bilevel.PolishedLiteralHyperSmoothness
import Bilevel.PolishedLiteralUpperPrimitive
import Bilevel.PolishedLiteralGapCertificate

/-! Complete analytic certificate for the manuscript's literal hierarchical
mean pair, with the same numerical macro/micro choices as thm:global.
Every field refers to the displayed source f,g,F and their actual gradients.
No budget, optimizer, coercivity or margin conclusion is a premise. -/
noncomputable section
set_option maxHeartbeats 1600000
open Filter
open scoped Topology RealInnerProductSpace
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain ZeroChainSchedule

structure MeanCertificate {X U : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    (P : Parameters (X:=X) (U:=U)) (κ θ C Rho Cgap cstar : ℝ) : Prop where
  upper_lower_gradient : ∀ x v y,‖gradient (PolishedLiteralJointMean.upper P.data x v) y‖≤C*P.L
  upper_smooth : ∀ q q',‖gradient P.upperJoint q-gradient P.upperJoint q'‖≤C*P.L*‖q-q'‖
  lower_smooth : ∀ q q',‖gradient P.sourceLower q-gradient P.sourceLower q'‖≤3*P.L*‖q-q'‖
  lowerYY : ∀ x v y d,(P.μ/2)*‖d‖^2≤
    ⟪(fderiv ℝ (gradient (PolishedLiteralJointMean.lower P.data x v)) y) d,d⟫
  lower_hessian_smooth : ∀ q q',
    ‖fderiv ℝ (gradient P.sourceLower) q-fderiv ℝ (gradient P.sourceLower) q'‖≤Rho*P.μ*θ*‖q-q'‖
  response_minimizes : ∀ x v y,
    PolishedLiteralJointMean.lower P.data x v (PolishedLiteralJointMean.response P.data x v)≤
      PolishedLiteralJointMean.lower P.data x v y
  response_unique : ∀ x v y,
    PolishedLiteralJointMean.lower P.data x v y≤
      PolishedLiteralJointMean.lower P.data x v (PolishedLiteralJointMean.response P.data x v) →
    y=PolishedLiteralJointMean.response P.data x v
  response_formula : ∀ x v,PolishedLiteralJointMean.response P.data x v=
    pack (κ • v) (P.selectedResidual (pack x (κ • v))/P.L)
  hyperobjective_formula : ∀ x v,
    PolishedLiteralJointMean.upper P.data x v (PolishedLiteralJointMean.response P.data x v)=P.outerMean κ (pack x v)
  hyperobjective_smooth : ∀ z z',‖gradient (P.outerMean κ) z-gradient (P.outerMean κ) z'‖≤C*P.L*κ^2*‖z-z'‖
  initialization : PolishedLiteralJointMean.response P.data (0:X) (0:U)=0
  coercive : Tendsto (P.outerMean κ) (cocompact (Joint X U)) atTop
  gap : P.outerMean κ 0-sInf (Set.range (P.outerMean κ))≤Cgap*((P.macroNode.n:ℝ)+1)*P.L*P.macroNode.width^2
  global_margin : ∀ x v,P.macroNode.coordinates x (Fin.last P.macroNode.n)<P.macroNode.width →
    cstar*(P.L*P.macroNode.width)≤‖gradient (P.outerMean κ) (pack x v)‖

/-- Source `hier:thm:mean`, using the same exact exponential profiles and
numerical constants that establish `thm:global`. The only smallness inputs
are the source's beta*theta and b conditions. -/
theorem literal_hierarchical_mean_certificate :
    ∃ Km A Cu ζ κ₀ cstar τ C Rho Cgap : ℝ,
      1≤Km ∧ 0<A ∧ 1≤Cu ∧ 0<ζ ∧ ζ≤1 ∧ 4≤κ₀ ∧ 2/ζ^3≤κ₀ ∧
      0<cstar ∧ 0<τ ∧ 0<C ∧ 1≤Rho ∧ 0≤Cgap ∧
    ∀ κ θ : ℝ,κ₀≤κ → 1≤θ →
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [FiniteDimensional ℝ X] [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      [FiniteDimensional ℝ U] (P : Parameters (X:=X) (U:=U)),
      P.SourceCalibration Km A Cu ζ κ → P.μ=P.L/κ →
      0<P.L → 0<P.macroNode.width → P.macroNode.width≤τ →
      P.J=levels θ → P.δ=resolution (1/64) P.β θ → P.w=width (1/64) P.β θ →
      P.β*θ≤τ → MeanCertificate P κ θ C Rho Cgap cstar := by
  obtain ⟨Km,A,Cu,ζ,κ₀,cstar,hKm,hA,hCu,hζ,hζ1,hκ₀,hcstar,hKm1,hCu1,hκscale,hglobal⟩ :=
    literal_global_certificate
  obtain ⟨τs,Rhos,hτs,hRhos,hsmall⟩ := literal_numerical_smallness_certificate
  obtain ⟨τl,Rho,hτl,hRho,hlower⟩ := literal_lower_full_budgets
  obtain ⟨Cf,hCf,hupper⟩ := source_upper_primitive_budgets Km A Cu ζ hKm1 hA.le hCu1 hζ hζ1
  obtain ⟨Cm,hCm,hbase⟩ := source_base_budgets Km A Cu ζ hKm1 hA.le hCu1 hζ hζ1
  let τ := min 1 (min τs τl)
  have hτ : 0<τ := lt_min zero_lt_one (lt_min hτs hτl)
  let C := Cf+Cm+1
  have hC : 0<C := by dsimp [C];positivity
  have hCfC : Cf≤C := by dsimp [C];linarith
  have hCmC : Cm≤C := by dsimp [C];linarith
  let Cgap := Parameters.sourceGapConstant A ζ
  have hCgap : 0≤Cgap := Parameters.sourceGapConstant_nonneg A ζ hA.le hζ.le
  refine ⟨Km,A,Cu,ζ,κ₀,cstar,τ,C,Rho,Cgap,hKm1,hA,hCu1,hζ,hζ1,hκ₀,hκscale,
    hcstar,hτ,hC,hRho,hCgap,?_⟩
  intro κ θ hκ hθ X U _ _ _ _ _ _ _ _ P hcal hμeq hL hb hbsmall hJ hδ hw hscale
  have hk4 : 4≤κ := hκ₀.trans hκ
  have hk0 : 0<κ := by linarith
  have hk1 : 1≤κ := by linarith
  have hkscale : 2/ζ^3≤κ := hκscale.trans hκ
  have hμ : 0<P.μ := by rw [hμeq];positivity
  have hμL : P.μ≤P.L := by rw [hμeq];exact div_le_self hL.le hk1
  have hratio : P.L/P.μ=κ := by rw [hμeq];field_simp
  have hβ : 0<P.β := by rw [hcal.microWidth];positivity
  have hβb : P.β≤P.macroNode.width := by rw [hcal.microWidth];exact div_le_self hb.le hk1
  have hbR : P.macroNode.width≤P.radius := by
    rw [hcal.microRadius]
    apply (le_div_iff₀ hζ).mpr
    convert mul_le_mul_of_nonneg_right (hζ1.trans hCu1) hb.le using 1
    ring
  have hRm : P.macroNode.width≤P.macroNode.radius := by
    rw [hcal.macroRadius]
    have hs : 1≤Real.sqrt ((P.macroNode.n:ℝ)+1) := Real.one_le_sqrt.mpr (by have hn : (0:ℝ)≤P.macroNode.n := Nat.cast_nonneg _;linarith)
    have ht := one_le_mul_of_one_le_of_one_le hKm1 hs
    nlinarith only [mul_le_mul_of_nonneg_right ht hb.le]
  have hsmallS : P.β*θ≤τs := hscale.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallL : P.β*θ≤τl := hscale.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb1 : P.macroNode.width≤1 := hbsmall.trans (min_le_left _ _)
  obtain ⟨hsecond,_,hcore⟩ := hsmall X U P θ hθ hμ hL hβ (hβb.trans hbR) hβb hRm hJ hδ hw hsmallS
  obtain ⟨_,_,hglip,hhlip⟩ := hlower X U P θ hθ hμ hμL hβ (hβb.trans hbR) hβb hRm hJ hδ hw hsmallL
  obtain ⟨hfy,_,hflip⟩ := hupper κ hk4 hkscale X U P hcal hL hb hb1
  obtain ⟨hFhess,_,_⟩ := hbase κ hk4 hkscale X U P hcal hL hb
  have hCscale : Cf*P.L≤C*P.L := mul_le_mul_of_nonneg_right hCfC hL.le
  have hFm (z : Joint X U) : ‖iteratedFDeriv ℝ 2 P.meanBase z‖≤C*P.L :=
    (hFhess z).trans (mul_le_mul_of_nonneg_right hCmC hL.le)
  refine {
    upper_lower_gradient := fun x v y => (hfy x v y).trans hCscale
    upper_smooth := fun q q' => (hflip q q').trans (mul_le_mul_of_nonneg_right hCscale (norm_nonneg _))
    lower_smooth := hglip
    lowerYY := P.lowerYY_coercive hμ hsecond
    lower_hessian_smooth := hhlip
    response_minimizes := fun x v => (P.exact_unique_response hμ hμL hsecond hcore x v).1
    response_unique := fun x v => (P.exact_unique_response hμ hμL hsecond hcore x v).2
    response_formula := fun x v => by
      change pack ((P.L/P.μ) • v) (P.selectedResidual (pack x ((P.L/P.μ) • v))/P.L)=
        pack (κ • v) (P.selectedResidual (pack x (κ • v))/P.L)
      rw [hratio]
    hyperobjective_formula := fun x v => by rw [P.exact_hyperobjective hL.ne',← hratio];rfl
    hyperobjective_smooth := P.outerMean_gradient_lipschitz κ (C*P.L) hk1 (by positivity) hFm
    initialization := P.exact_initialization
    coercive := P.source_calibrated_coercive hcal hKm hA.le hCu hζ hk0 hL hb
    gap := P.source_calibrated_gap hcal hA.le hζ.le hζ1 hk4 hL hb
    global_margin := hglobal κ hκ X U P hcal hL hb
  }

end Bilevel.PolishedLiteral
