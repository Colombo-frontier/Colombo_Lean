import Bilevel.MultiscaleMeanCertificate
import Bilevel.MultiscaleAmplitudeSmallness
import Bilevel.MultiscaleGradientRisk

/-! Actual mean-family realization with the exact target variation budget.
The chain amplitude is fixed before all problem budgets and dimensions. -/
noncomputable section
namespace Bilevel.MultiscaleMean
open Filter ZeroChain CompensatedMean
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 1024

theorem amplitude_mean_family_certificate : ∃ K ηmax τ LfC CfC : ℝ,
    1 ≤ K ∧ 0 < ηmax ∧ ηmax ≤ 1 ∧ 0 < τ ∧ 1 ≤ LfC ∧ 0 < CfC ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] (n : ℕ) (P : Parameters (E := E) n) (Δ : ℝ),
      P.μ ≤ P.L → 0 < P.η → P.η ≤ ηmax → P.c = 1/64 →
      P.R = K*P.β*Real.sqrt (n+1:ℕ) → P.ν = P.η*P.L/24 →
      P.β*P.θ ≤ τ → 0 ≤ Δ → (n+1:ℕ)*P.η*P.L*P.β^2 ≤ Δ →
      Nonempty (Realization P (LfC*P.L) (CfC*(P.L+Real.sqrt (P.L*Δ))) ((P.μ/2)*P.θ)) ∧
      (∀ x,|WrappedChain.coordinates n P.R P.U ((P.L/P.μ) • x) (Fin.last n)|<P.β →
        (P.L/P.μ)*P.η*P.L*P.β/2≤‖gradient P.realized x‖) := by
  obtain ⟨B,hB,hcoord⟩ := ZeroChain.coordinate_gradient_uniform_bound
  let K := 48*(B+1)
  have hK : 1 ≤ K := by dsimp [K]; linarith
  obtain ⟨ηmax,τ,hηmax,hηmax1,hτ,_hτ1,hsmall⟩ := amplitude_smallness_certificate
  obtain ⟨A,hA,hsmooth⟩ := actual_upper_smoothness
  obtain ⟨D,hD,hupper⟩ := source_raw_upper_budget
  let CfC := D*(1+(1/24)*K)
  have hCfC : 0 < CfC := by dsimp [CfC]; positivity
  refine ⟨K,ηmax,τ,A,CfC,hK,hηmax,hηmax1,hτ,hA,hCfC,fun E _ _ _ _ n P Δ hμL hη hηbound hceq hR hν hscale hΔ hgap => ?_⟩
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
  obtain ⟨hsecond,hthird,hcore⟩ := hsmall E n P hceq hηbound hscale
  have hAgrad := hsmooth E n P hRad hνL
  have hU : ∀ x y,‖P.data.upperY x y‖ ≤ CfC*(P.L+Real.sqrt (P.L*Δ)) := by
    intro x y
    apply hupper E n P K (1/24) Δ (by linarith) (by norm_num) hΔ hR _ hgap x y
    rw [hν]
    ring
  let Q := P.data.primitive P.μ_pos hμL (A*P.L) (CfC*(P.L+Real.sqrt (P.L*Δ))) ((P.μ/2)*P.θ)
    (by positivity) (by positivity) (by positivity) hAgrad hU hsecond hthird
  let r : Q.Response := {
    y := P.data.response
    minimizes := fun x y => P.data.response_minimizes P.μ_pos hμL P.L_pos.ne' hsecond hcore x y }
  have hobj : Q.hyperobjective r = P.realized := funext P.exact_hyperobjective
  obtain ⟨umin,hmin⟩ := WrappedChain.minimum_attained n P.amplitude P.β P.ν P.R P.amplitude_nonneg hνp
    (P.β_pos.trans_le P.β_le_R) P.U
  have hgap0 := WrappedChain.pointwise_gap n P.amplitude P.β P.ν P.R P.amplitude_nonneg P.ν_nonneg P.U umin
  refine ⟨?_,fun x hx => P.source_endgame B hB (hcoord n) hη hR hν x hx⟩
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
    full_hessian_variation := P.data.full_joint_hessian_variation ((P.μ/2)*P.θ) (by positivity) hthird
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
