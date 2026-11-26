import Bilevel.CompensatedMeanPrimitive
import Bilevel.CompensatedMeanJointHessian
import Bilevel.MultiscaleSmallness
import Bilevel.MultiscaleUpperSmoothness
import Bilevel.MultiscaleUpperBudget
import Bilevel.WrappedChainGap

/-! The actual mean-family certificate. Numerical constants and a numerical
βθ threshold imply every Primitive field, exact response, exact hypergradient,
coercivity, and the source finite initial-gap bound. The raw Cf budget remains
O(L + sqrt(L Δ)). -/

noncomputable section
set_option synthInstance.maxSize 1024
namespace Bilevel.MultiscaleMean
open Filter ZeroChain CompensatedMean
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local instance : NormedAddCommGroup (CompensatedMean.JointSpace E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (CompensatedMean.JointSpace E →L[ℝ] ℝ) := inferInstance

namespace Parameters
variable {n : ℕ} (P : Parameters (E := E) n)

def realized (x : E) : ℝ := P.outer ((P.L/P.μ) • x)

theorem realized_hasGradientAt (x : E) :
    HasGradientAt P.realized ((P.L/P.μ) • gradient P.outer ((P.L/P.μ) • x)) x := by
  have h := ((P.outer_contDiff.differentiable (by norm_num) _).hasGradientAt.hasFDerivAt).comp x
    ((hasFDerivAt_id x).const_smul (P.L/P.μ))
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  ext v
  simp only [InnerProductSpace.toDual_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_left,real_inner_smul_right,id_eq]

theorem realized_coercive [FiniteDimensional ℝ E] (hν : 0 < P.ν) :
    Tendsto P.realized (cocompact E) atTop := by
  have houter := WrappedChain.coercive n P.amplitude P.β P.ν P.R P.amplitude_nonneg hν
    (P.β_pos.trans_le P.β_le_R) P.U
  have hk : P.L/P.μ ≠ 0 := (div_pos P.L_pos P.μ_pos).ne'
  exact houter.comp (Homeomorph.smulOfNeZero (P.L/P.μ) hk).isClosedEmbedding.tendsto_cocompact

theorem response_zero : P.data.response 0 = 0 := by
  have hr : P.residual 0 = 0 := by
    simp only [residual,ZeroChainWrappedResidual.residual,WrappedChain.coordinates,
      RadialWrapper.compress,smul_zero,map_zero,ZeroChainResidualScaled.R_zero]
  change pack E ((P.L/P.μ) • (0:E)) (P.residual ((P.L/P.μ) • (0:E))/P.L) 0 = 0
  rw [smul_zero,hr,zero_div,pack_zero]

end Parameters

structure Realization {n : ℕ} (P : Parameters (E := E) n) (Lf Cf ρ : ℝ) where
  primitive : Model.Primitive (X := E) (Y := LowerSpace E) (P.μ/2) Lf (3*P.L) Cf ρ
  response : primitive.Response
  f_eq : primitive.f = P.data.upper
  g_eq : primitive.g = P.data.lower
  response_eq : response.y = P.data.response
  upper_joint_C3 : ContDiff ℝ 3 (fun v : CompensatedMean.JointSpace E => P.data.upper v.1 v.2)
  lower_joint_C3 : ContDiff ℝ 3 (fun v : CompensatedMean.JointSpace E => P.data.lower v.1 v.2)
  objective_eq : primitive.hyperobjective response = P.realized
  exact_gradient : ∀ x, HasGradientAt (primitive.hyperobjective response)
    ((P.L/P.μ) • gradient P.outer ((P.L/P.μ) • x)) x
  full_hessian_variation : ∀ z z' : CompensatedMean.JointSpace E,
    ‖fderiv ℝ (fderiv ℝ (fun v : CompensatedMean.JointSpace E => P.data.lower v.1 v.2)) z-
      fderiv ℝ (fderiv ℝ (fun v : CompensatedMean.JointSpace E => P.data.lower v.1 v.2)) z'‖ ≤
      ρ*Model.jointDistance z.1 z'.1 z.2 z'.2
  full_upper_derivative : ∀ z : CompensatedMean.JointSpace E,
    ‖fderiv ℝ (fun v : CompensatedMean.JointSpace E => P.data.upper v.1 v.2) z‖ ≤ Cf
  full_upper_gradient : ∀ x y,
    Real.sqrt (‖P.data.upperX x y‖^2+‖P.data.upperY x y‖^2) ≤ Cf
  coercive : Tendsto (primitive.hyperobjective response) (cocompact E) atTop
  initial_response : response.y 0 = 0
  gap : primitive.GapCertificate response 0
    (P.amplitude*((1+2*Real.exp 1)*ZeroChain.phiBound*(n+1:ℕ)))

namespace Realization
variable {n : ℕ} {P : Parameters (E := E) n} {Lf Cf ρ : ℝ} (Q : Realization P Lf Cf ρ)

theorem actual_gradient (x : E) :
    gradient (Q.primitive.hyperobjective Q.response) x =
      (P.L/P.μ) • gradient P.outer ((P.L/P.μ) • x) := (Q.exact_gradient x).gradient

theorem unique_lower_response (x : E) (y : LowerSpace E)
    (hy : Q.primitive.IsLowerSolution x y) : y = P.data.response x := by
  rw [← Q.response_eq]
  exact Q.primitive.lower_solution_unique x y (Q.response.y x) hy (Q.response.minimizes x)

theorem gap_to_infimum : Q.primitive.hyperobjective Q.response 0-
    sInf (Set.range (Q.primitive.hyperobjective Q.response)) ≤
      P.amplitude*((1+2*Real.exp 1)*ZeroChain.phiBound*(n+1:ℕ)) := by
  have hf : Q.gap.floor ≤ sInf (Set.range (Q.primitive.hyperobjective Q.response)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro z ⟨x,rfl⟩
    exact Q.gap.lower_bound x
  linarith [Q.gap.gap]

theorem minimum_attained : ∃ x,∀ y,Q.primitive.hyperobjective Q.response x ≤
    Q.primitive.hyperobjective Q.response y := by
  have hc : Continuous (Q.primitive.hyperobjective Q.response) := by
    rw [Q.objective_eq]
    exact P.outer_contDiff.continuous.comp (continuous_const.smul continuous_id)
  exact hc.exists_forall_le Q.coercive

end Realization

/-- All analytic hypotheses have been discharged for the displayed family.
The fixed frame-radius constant is numerical and can be chosen larger than
the source's end-game threshold. -/
theorem mean_family_certificate : ∃ K τ LfC CfC RhoC : ℝ,
    1 ≤ K ∧ 0 < τ ∧ 1 ≤ LfC ∧ 0 < CfC ∧ 1 ≤ RhoC ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] (n : ℕ) (P : Parameters (E := E) n) (Δ : ℝ),
      P.μ ≤ P.L → 0 < P.η → P.c = 1/64 →
      P.R = K*P.β*Real.sqrt (n+1:ℕ) → P.ν = P.η*P.L/24 →
      P.β*P.θ ≤ τ → 0 ≤ Δ → (n+1:ℕ)*P.η*P.L*P.β^2 ≤ Δ →
      Nonempty (Realization P (LfC*P.L) (CfC*(P.L+Real.sqrt (P.L*Δ))) (RhoC*P.μ*P.θ)) := by
  obtain ⟨B,hB,_hcoord⟩ := ZeroChain.coordinate_gradient_uniform_bound
  let K := 48*(B+1)
  have hK : 1 ≤ K := by dsimp [K]; linarith
  obtain ⟨τ,Rho,hτ,hRho,hsmall⟩ := numerical_smallness_certificate
  obtain ⟨A,hA,hsmooth⟩ := actual_upper_smoothness
  obtain ⟨D,hD,hupper⟩ := source_raw_upper_budget
  let CfC := D*(1+(1/24)*K)
  have hCfC : 0 < CfC := by dsimp [CfC]; positivity
  refine ⟨K,τ,A,CfC,Rho,hK,hτ,hA,hCfC,hRho,fun E _ _ _ _ n P Δ hμL hη hceq hR hν hscale hΔ hgap => ?_⟩
  have hL := P.L_pos
  have hμ := P.μ_pos
  have hβ := P.β_pos
  have hθ : 0 < P.θ := by linarith [P.θ_ge_one]
  have hνp : 0 < P.ν := by rw [hν]; positivity
  have hνL : P.ν ≤ P.L := by
    rw [hν]
    have hh := mul_le_mul_of_nonneg_right P.η_le_one P.L_pos.le
    nlinarith
  have hRad : P.β*Real.sqrt (n+1:ℕ) ≤ P.R := by
    rw [hR]
    have hh := mul_le_mul_of_nonneg_right hK (show 0 ≤ P.β*Real.sqrt (n+1:ℕ) by positivity)
    nlinarith only [hh]
  obtain ⟨hsecond,hthird,hcore⟩ := hsmall E n P hceq hscale
  have hAgrad := hsmooth E n P hRad hνL
  have hU : ∀ x y,‖P.data.upperY x y‖ ≤ CfC*(P.L+Real.sqrt (P.L*Δ)) := by
    intro x y
    apply hupper E n P K (1/24) Δ (by linarith) (by norm_num) hΔ hR _ hgap x y
    rw [hν]
    ring
  let Q := P.data.primitive P.μ_pos hμL (A*P.L) (CfC*(P.L+Real.sqrt (P.L*Δ))) (Rho*P.μ*P.θ)
    (by positivity) (by positivity) (by positivity) hAgrad hU hsecond hthird
  let r : Q.Response := {
    y := P.data.response
    minimizes := fun x y => P.data.response_minimizes P.μ_pos hμL P.L_pos.ne' hsecond hcore x y }
  have hobj : Q.hyperobjective r = P.realized := funext P.exact_hyperobjective
  obtain ⟨umin,hmin⟩ := WrappedChain.minimum_attained n P.amplitude P.β P.ν P.R P.amplitude_nonneg hνp
    (P.β_pos.trans_le P.β_le_R) P.U
  have hgap0 := WrappedChain.pointwise_gap n P.amplitude P.β P.ν P.R P.amplitude_nonneg P.ν_nonneg P.U umin
  refine ⟨{
    primitive := Q
    response := r
    f_eq := rfl
    g_eq := rfl
    response_eq := rfl
    upper_joint_C3 := P.data.upper_joint_contDiff
    lower_joint_C3 := P.data.lower_joint_contDiff
    objective_eq := hobj
    exact_gradient := fun x => hobj.symm ▸ P.realized_hasGradientAt x
    full_hessian_variation := P.data.full_joint_hessian_variation (Rho*P.μ*P.θ) (by positivity) hthird
    full_upper_derivative := P.data.full_upper_derivative_bound _ (by positivity) hU
    full_upper_gradient := P.data.full_upper_gradient_bound _ hU
    coercive := hobj.symm ▸ P.realized_coercive hνp
    initial_response := P.response_zero
    gap := {
      floor := P.outer umin
      lower_bound := fun x => by rw [hobj]; exact hmin ((P.L/P.μ) • x)
      gap := by
        rw [hobj]
        change P.outer ((P.L/P.μ) • (0:E))-P.outer umin ≤ _
        simpa only [smul_zero] using hgap0
    }
  }⟩

end Bilevel.MultiscaleMean
