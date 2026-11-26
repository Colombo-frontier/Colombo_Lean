import Bilevel.MultiscalePerturbation

/-! A single numerical βθ threshold gives both global lower-Hessian
coercivity and exact response-core linearity for the actual family. -/

noncomputable section
namespace Bilevel.MultiscaleMean
open ZeroChainSchedule CompensatedMean

theorem numerical_smallness_certificate : ∃ τ Rho : ℝ, 0 < τ ∧ 1 ≤ Rho ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n), P.c = 1/64 → P.β*P.θ ≤ τ →
      (∀ y : LowerSpace E,‖iteratedFDeriv ℝ 2 P.data.perturbation y‖ ≤ P.μ/2) ∧
      (∀ y : LowerSpace E,‖iteratedFDeriv ℝ 3 P.data.perturbation y‖ ≤ Rho*P.μ*P.θ) ∧
      (∀ u j,j ≤ P.data.J → |P.data.r u/P.L| ≤ P.data.w j/4) := by
  obtain ⟨M,hM,hm⟩ := actual_perturbation_bounds
  obtain ⟨C,hC,hc⟩ := ZeroChainWrappedResidual.residual_uniform_bounds
  let τ := min 1 (min (1/(130*M)) (1/(256*C)))
  have hMp : 0 < M := by linarith
  have hCp : 0 < C := by linarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  refine ⟨τ,4097*M,hτ,by nlinarith,fun E _ _ _ n P hceq hs => ?_⟩
  have hμ := P.μ_pos
  have hβ := P.β_pos
  have hθ := P.θ_ge_one
  have hθ0 : 0 ≤ P.θ := by linarith
  have hs1 : P.β*P.θ ≤ 1 := hs.trans (min_le_left _ _)
  have hβ1 : P.β ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hθ hβ.le]
  have hβθ : P.β ≤ P.θ := by linarith
  have hsM : P.β*P.θ ≤ 1/(130*M) := hs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsC : P.β*P.θ ≤ 1/(256*C) := hs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hMsmall : 130*M*P.β*P.θ ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 130*M)).mp hsM
    nlinarith only [hh]
  have hCsmall : 4*C*P.β*P.θ ≤ P.c := by
    have hh := (le_div_iff₀ (by positivity : 0 < 256*C)).mp hsC
    rw [hceq]
    nlinarith only [hh]
  have hroot : Real.sqrt P.θ ≤ P.θ := by
    have hh := Real.sq_sqrt hθ0
    have hp : P.θ ≤ P.θ^2 := by nlinarith
    nlinarith [Real.sqrt_nonneg P.θ]
  have hbr : P.β*Real.sqrt P.θ ≤ P.β*P.θ := mul_le_mul_of_nonneg_left hroot hβ.le
  have hb2 : P.β^2 ≤ P.β*P.θ := by nlinarith
  refine ⟨fun y => ?_,fun y => ?_,?_⟩
  · have hh := (hm E n P y).1
    calc
      _ ≤ M*P.μ*(P.β^2+P.β*Real.sqrt P.θ/P.c) := hh
      _ ≤ M*P.μ*(65*P.β*P.θ) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hMp.le hμ.le)
        rw [hceq]
        norm_num
        nlinarith only [hbr,hb2]
      _ = (P.μ/2)*(130*M*P.β*P.θ) := by ring
      _ ≤ P.μ/2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hMsmall (by positivity : 0 ≤ P.μ/2)
  · have hh := (hm E n P y).2
    calc
      _ ≤ M*P.μ*(P.β+P.θ/P.c^2) := hh
      _ ≤ M*P.μ*(4097*P.θ) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hMp.le hμ.le)
        rw [hceq]
        norm_num
        linarith
      _ = _ := by ring
  · apply P.core_width_condition hCp.le _ hCsmall
    intro u
    exact (hc E n P.amplitude P.β P.R P.amplitude_nonneg P.β_pos P.β_le_R P.U u).1

end Bilevel.MultiscaleMean
