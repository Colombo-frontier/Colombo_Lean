import NCBall.Construction
import Mathlib.MeasureTheory.Function.L2Space

/-! # Taking the expectation over sample handles

The Gaussian assumption is stronger than necessary for this step: integrability
and zero mean of each noise vector suffice. These are explicit hypotheses.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace NCBall

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integral_localBump_noise {n : ℕ} (u y : Space n) (σ : ℝ)
    (Z : Ω → Space n) (hZ : Integrable Z μ) (hmean : ∫ ω, Z ω ∂μ = 0) :
    ∫ ω, localBump (u + σ • Z ω) y ∂μ = localBump u y := by
  have hi : Integrable (fun ω => u + σ • Z ω) μ :=
    integrable_const u |>.add (hZ.smul σ)
  have hm : ∫ ω, u + σ • Z ω ∂μ = u := by
    have hadd := integral_add (integrable_const u) (hZ.smul σ)
    simp only [Pi.smul_apply] at hadd
    rw [hadd, integral_const, integral_smul, hmean]
    simp
  simp only [localBump]
  rw [integral_const_mul]
  have hinner : (fun ω => ⟪u + σ • Z ω, y⟫_ℝ) =
      (fun ω => ⟪y, u + σ • Z ω⟫_ℝ) := by ext ω; exact real_inner_comm _ _
  rw [hinner, integral_inner hi y, hm, real_inner_comm y u]

/-- Equation (6.15) for any integrable centered noise distribution. -/
theorem sample_mean_eq_population {n M : ℕ} (ρ γ lam σ : ℝ)
    (c U : ℕ → Space n) (Z : ℕ → Ω → Space n)
    (hZ : ∀ j < M, Integrable (Z j) μ)
    (hmean : ∀ j < M, ∫ ω, Z j ω ∂μ = 0) (x : Space n) :
    ∫ ω, chainValue M ρ γ lam c (fun j => U j + σ • Z j ω) x ∂μ =
      chainValue M ρ γ lam c U x := by
  have hloc : ∀ j ∈ Finset.range M,
      Integrable (fun ω => localBump (U j + σ • Z j ω) (ρ⁻¹ • (x - c j))) μ := by
    intro j hj
    exact ((integrable_const (U j)).add
      ((hZ j (Finset.mem_range.mp hj)).smul σ)).inner_const _ |>.const_mul _
  have hsum := integrable_finset_sum (Finset.range M) hloc
  have hfirst := integral_add (integrable_const (-γ * x 0)) (hsum.const_mul (lam * ρ))
  have hwhole := integral_add ((integrable_const (-γ * x 0)).add (hsum.const_mul (lam * ρ)))
    (integrable_const (γ * ρ * terminalBump (ρ⁻¹ • (x - c M))))
  simp only [Pi.add_apply] at hwhole
  simp only [chainValue]
  rw [hwhole, hfirst, integral_const_mul (lam * ρ),
    integral_finset_sum _ hloc]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  congr 2
  apply congrArg (fun r : ℝ => lam * ρ * r)
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_localBump_noise μ (U j) (ρ⁻¹ • (x - c j)) σ (Z j)
    (hZ j (Finset.mem_range.mp hj)) (hmean j (Finset.mem_range.mp hj))

end NCBall
