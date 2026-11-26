import Bilevel.MultiscaleMeanCore

/-! The source's raw Cf budget. It is obtained from the actual upper gradient
and the chain-gap budget; no Δ/L restriction is imposed. -/

noncomputable section
namespace Bilevel.MultiscaleMean

theorem gap_controls_gradient_scale (η L β Δ T : ℝ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hL : 0 < L) (hβ : 0 ≤ β) (hΔ : 0 ≤ Δ)
    (hT : 0 ≤ T) (hgap : T*η*L*β^2 ≤ Δ) :
    η*L*β*Real.sqrt T ≤ Real.sqrt (L*Δ) := by
  have hq : 0 ≤ η*L*β*Real.sqrt T := by positivity
  have hηL : η*L ≤ L := by nlinarith
  have hbase : 0 ≤ T*η*L*β^2 := by positivity
  have hmul := mul_le_mul hηL hgap hbase hL.le
  have hTs := Real.sq_sqrt hT
  have hDs := Real.sq_sqrt (mul_nonneg hL.le hΔ)
  have he : (η*L*β*Real.sqrt T)^2 = (η*L)*(T*η*L*β^2) := by
    rw [mul_pow,mul_pow,mul_pow,hTs]
    ring
  have hsq : (η*L*β*Real.sqrt T)^2 ≤ (Real.sqrt (L*Δ))^2 := by
    rw [he,hDs]
    exact hmul
  exact (sq_le_sq₀ hq (Real.sqrt_nonneg _)).mp hsq

/-- Uniform in ambient dimension. K records only the fixed radial-wrapper
constant, not a restriction on the gap. -/
theorem raw_upper_budget : ∃ D : ℝ, 1 ≤ D ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n) (K Δ : ℝ), 0 ≤ K → 0 ≤ Δ →
      P.ν*P.R ≤ K*(P.η*P.L*P.β*Real.sqrt (n+1:ℕ)) →
      (n+1:ℕ)*P.η*P.L*P.β^2 ≤ Δ →
      ∀ (x : E) (y : CompensatedMean.LowerSpace E),
        ‖P.data.upperY x y‖ ≤ D*(1+K)*(P.L+Real.sqrt (P.L*Δ)) := by
  obtain ⟨B,hB,hchain⟩ := ZeroChain.coordinate_gradient_uniform_bound
  obtain ⟨C,hC,hr⟩ := ZeroChainWrappedResidual.residual_uniform_bounds
  let D := 1+B+C
  have hD : 1 ≤ D := by dsimp [D]; linarith
  refine ⟨D,hD,fun E _ _ _ n P K Δ hK hΔ hrad hgap x y => ?_⟩
  have hC0 : 0 ≤ C := by linarith
  have hL := P.L_pos
  have hβ := P.β_pos
  have hη := P.η_nonneg
  have hT : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hroot : 1 ≤ Real.sqrt (n+1:ℕ) := Real.one_le_sqrt.mpr hT
  have hjet (u : E) : ‖iteratedFDeriv ℝ 1 P.residual u‖ ≤ C*P.amplitude/P.β := by
    have h := (hr E n P.amplitude P.β P.R P.amplitude_nonneg hβ P.β_le_R P.U u).2 0
    simpa only [Fin.val_zero,zero_add,pow_one] using h
  have hraw := P.upper_gradient_raw_bound B C hB (hchain n) hjet x y
  have hscale := gap_controls_gradient_scale P.η P.L P.β Δ (n+1:ℕ) hη P.η_le_one hL hβ.le hΔ
    (by positivity) hgap
  have hq : 0 ≤ P.η*P.L*P.β*Real.sqrt (n+1:ℕ) := by positivity
  have he : P.amplitude/P.β = P.η*P.L*P.β := by
    dsimp [Parameters.amplitude]
    field_simp
    ring
  have he' : C*P.amplitude/P.β = C*(P.η*P.L*P.β) := by rw [mul_div_assoc,he]
  rw [he,he'] at hraw
  have hrsmall : C*(P.η*P.L*P.β) ≤ C*(P.η*P.L*P.β*Real.sqrt (n+1:ℕ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hroot (show 0 ≤ C*(P.η*P.L*P.β) by positivity)]
  have hcoefficient : B+C+K ≤ D*(1+K) := by
    dsimp [D]
    nlinarith [mul_nonneg hB hK,mul_nonneg hC0 hK]
  have hcoefficient0 : 0 ≤ B+C+K := by positivity
  have hdL : P.L ≤ D*(1+K)*P.L := by
    have hh : 1 ≤ D*(1+K) := by nlinarith [mul_nonneg (show 0 ≤ D by linarith) hK]
    nlinarith [mul_le_mul_of_nonneg_right hh hL.le]
  have hcscale := mul_le_mul_of_nonneg_left hscale hcoefficient0
  have hctop := mul_le_mul_of_nonneg_right hcoefficient (Real.sqrt_nonneg (P.L*Δ))
  nlinarith only [hraw,hrad,hrsmall,hcscale,hctop,hdL]

/-- Substituting the manuscript's exact R and ν makes the coefficient purely
numerical once its fixed wrapper constants are chosen. -/
theorem source_raw_upper_budget : ∃ D : ℝ, 1 ≤ D ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n) (K η₀ Δ : ℝ), 0 ≤ K → 0 ≤ η₀ → 0 ≤ Δ →
      P.R = K*P.β*Real.sqrt (n+1:ℕ) → P.ν = η₀*P.η*P.L →
      (n+1:ℕ)*P.η*P.L*P.β^2 ≤ Δ →
      ∀ (x : E) (y : CompensatedMean.LowerSpace E),
        ‖P.data.upperY x y‖ ≤ D*(1+η₀*K)*(P.L+Real.sqrt (P.L*Δ)) := by
  obtain ⟨D,hD,hb⟩ := raw_upper_budget
  refine ⟨D,hD,fun E _ _ _ n P K η₀ Δ hK hη₀ hΔ hR hν hgap x y => ?_⟩
  apply hb E n P (η₀*K) Δ (mul_nonneg hη₀ hK) hΔ _ hgap x y
  rw [hR,hν]
  ring_nf
  exact le_rfl

end Bilevel.MultiscaleMean
