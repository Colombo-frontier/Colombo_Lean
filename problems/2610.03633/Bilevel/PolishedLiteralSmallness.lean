import Bilevel.PolishedLiteralPerturbationBudgets
import Bilevel.PolishedLiteralResponse

/-! One numerical beta*theta threshold discharges the actual global
lower-Hessian budget and normal-core linearity for the literal hierarchy. -/
noncomputable section
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ZeroChainSchedule
theorem literal_numerical_smallness_certificate : ∃ τ Rho : ℝ,0<τ ∧ 1≤Rho ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (θ : ℝ),
      1≤θ → 0<P.μ → 0<P.L → 0<P.β → P.β≤P.radius →
      P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.J=levels θ → P.δ=resolution (1/64) P.β θ → P.w=width (1/64) P.β θ →
      P.β*θ≤τ →
      (∀ y : PolishedLiteralCompensated.LowerSpace (Joint X U),
        ‖iteratedFDeriv ℝ 2 P.data.perturbation y‖≤P.μ/2) ∧
      (∀ y : PolishedLiteralCompensated.LowerSpace (Joint X U),
        ‖iteratedFDeriv ℝ 3 P.data.perturbation y‖≤Rho*P.μ*θ) ∧
      (∀ z j,j≤P.J → |P.selectedResidual z/P.L|≤P.w j/4) := by
  obtain ⟨M,hM,hm⟩ := actual_literal_perturbation_bounds
  obtain ⟨C,hC,hc⟩ := selected_residual_value_bound
  let τ := min 1 (min (1/(130*M)) (1/(256*C)))
  have hMp : 0 < M := by linarith
  have hCp : 0 < C := by linarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  refine ⟨τ,4097*M,hτ,by nlinarith,fun X U _ _ _ _ _ _ P θ hθ hμ hL hβ hR hβb hbR hJ hδ hw hs => ?_⟩
  have hθ0 : 0 ≤ θ := by linarith
  have hs1 : P.β*θ ≤ 1 := hs.trans (min_le_left _ _)
  have hβ1 : P.β ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hθ hβ.le]
  have hβθ : P.β ≤ θ := by linarith
  have hsM : P.β*θ ≤ 1/(130*M) := hs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsC : P.β*θ ≤ 1/(256*C) := hs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hMsmall : 130*M*P.β*θ ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 130*M)).mp hsM
    nlinarith only [hh]
  have hCsmall : 4*C*P.β*θ ≤ (1/64:ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0 < 256*C)).mp hsC
    nlinarith only [hh]
  have hroot : Real.sqrt θ ≤ θ := by
    have hh := Real.sq_sqrt hθ0
    have hp : θ ≤ θ^2 := by nlinarith
    nlinarith [Real.sqrt_nonneg θ]
  have hbr : P.β*Real.sqrt θ ≤ P.β*θ := mul_le_mul_of_nonneg_left hroot hβ.le
  have hb2 : P.β^2 ≤ P.β*θ := by nlinarith
  refine ⟨fun y => ?_,fun y => ?_,?_⟩
  · have hh := (hm X U P (1/64) θ (by norm_num) (by norm_num) hθ hμ hL hβ hR hβb hbR hJ hδ hw y).1
    calc
      _ ≤ M*P.μ*(P.β^2+P.β*Real.sqrt θ/(1/64:ℝ)) := hh
      _ ≤ M*P.μ*(65*P.β*θ) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hMp.le hμ.le)
        norm_num
        nlinarith only [hbr,hb2]
      _ = (P.μ/2)*(130*M*P.β*θ) := by ring
      _ ≤ P.μ/2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hMsmall (by positivity : 0 ≤ P.μ/2)
  · have hh := (hm X U P (1/64) θ (by norm_num) (by norm_num) hθ hμ hL hβ hR hβb hbR hJ hδ hw y).2
    calc
      _ ≤ M*P.μ*(P.β+θ/(1/64:ℝ)^2) := hh
      _ ≤ M*P.μ*(4097*θ) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hMp.le hμ.le)
        norm_num
        linarith
      _ = _ := by ring
  · exact P.normal_core C (1/64) θ hCp.le (by norm_num) hθ hL hβ hJ
      (fun j => congrFun hw j) (hc X U P hL.le) hCsmall


end Bilevel.PolishedLiteral
