import FreshGradientMinimax.RecursiveOutput
import FreshGradientMinimax.RecursivePotential

/-! The quadratic-coefficient potential along the implemented recursive
program. Its unconditional mean grows only linearly in the stage index. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem recursive_potential_mean_step (O : FreshOracle S.toNCObjective σ)
    (hfast : ℓ / 4 ≤ α) (δ : ℝ) (N : ℕ) (E : ℝ) (j : ℕ)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (recursiveResidualPotential μ j) ν)
    (hg : Integrable (S.dualQuadraticGap hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j)) ν)
    (hg' : Integrable (S.dualQuadraticGap hfast (recursiveCurvature μ (j + 1)) (recursiveCurvature_nonneg S.μ_pos (j + 1)))
      (((recursiveStageProgram dx dy ℓ α σ μ δ N E (j + 1)).resultKernel O.kernel).comap
        (quadraticAdvance (recursiveMass μ j)) (quadraticAdvance_continuous _).measurable ∘ₘ ν))
    (hb : (∫ z, S.dualQuadraticGap hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j) z ∂ν) ≤ recursiveAccuracy μ δ N j)
    (hb' : (∫ z, S.dualQuadraticGap hfast (recursiveCurvature μ (j + 1)) (recursiveCurvature_nonneg S.μ_pos (j + 1)) z
      ∂((recursiveStageProgram dx dy ℓ α σ μ δ N E (j + 1)).resultKernel O.kernel).comap
        (quadraticAdvance (recursiveMass μ j)) (quadraticAdvance_continuous _).measurable ∘ₘ ν) ≤ recursiveAccuracy μ δ N (j + 1)) :
    Integrable (recursiveResidualPotential μ (j + 1))
      (((recursiveStageProgram dx dy ℓ α σ μ δ N E (j + 1)).resultKernel O.kernel).comap
        (quadraticAdvance (recursiveMass μ j)) (quadraticAdvance_continuous _).measurable ∘ₘ ν) ∧
    (∫ z, recursiveResidualPotential μ (j + 1) z
      ∂((recursiveStageProgram dx dy ℓ α σ μ δ N E (j + 1)).resultKernel O.kernel).comap
        (quadraticAdvance (recursiveMass μ j)) (quadraticAdvance_continuous _).measurable ∘ₘ ν) ≤
      (∫ z, recursiveResidualPotential μ j z ∂ν) + 12 * (δ ^ 2 / (10000 * (N + 1 : ℕ) ^ 2)) := by
  let G := S.dualQuadraticGap hfast (recursiveCurvature μ j) (recursiveCurvature_nonneg S.μ_pos j)
  let G' := S.dualQuadraticGap hfast (recursiveCurvature μ (j + 1)) (recursiveCurvature_nonneg S.μ_pos (j + 1))
  let w := 4 * recursiveMass μ (j + 1)
  have hw : 0 ≤ w := by dsimp [w]; have := recursiveMass_pos S.μ_pos (j + 1); positivity
  obtain ⟨hpi, hpb⟩ := adjacent_moment_bound ν _
    (fun z => recursiveResidualPotential μ j z + w * G z)
    ((recursiveResidualPotential_continuous μ j).measurable.add
      (measurable_const.mul (S.dualQuadraticGap_measurable hfast _ _)))
    (fun z => w * G' z) (recursiveResidualPotential μ (j + 1))
    (measurable_const.mul (S.dualQuadraticGap_measurable hfast _ _))
    (recursiveResidualPotential_continuous μ (j + 1)).measurable
    (recursiveResidualPotential_nonneg μ (j + 1)) (hi.add (hg.const_mul w)) (hg'.const_mul w) (by
      filter_upwards [S.recursive_adjacent_coefficient O δ N E j ν] with p hp
      have h := S.recursive_potential_step hfast j p.1 p.2 hp
      change _ ≤ recursiveResidualPotential μ j p.1 + w * (G p.1 + G' p.2) at h
      linarith only [h])
  refine ⟨hpi, ?_⟩
  rw [integral_add hi (hg.const_mul w), integral_const_mul w G, integral_const_mul w G'] at hpb
  have hb0 := mul_le_mul_of_nonneg_left hb hw
  have hb1 := mul_le_mul_of_nonneg_left hb' hw
  have heq : w * recursiveAccuracy μ δ N j + w * recursiveAccuracy μ δ N (j + 1) =
      12 * (δ ^ 2 / (10000 * (N + 1 : ℕ) ^ 2)) := by
    have h0 := recursiveAccuracy_scaled S.μ_pos δ N j
    have h1 := recursiveAccuracy_scaled S.μ_pos δ N (j + 1)
    dsimp [w]
    rw [recursiveMass_succ] at h1 ⊢
    nlinarith only [h0, h1]
  change (∫ z, G z ∂ν) ≤ _ at hb
  change w * (∫ z, G z ∂ν) ≤ _ at hb0
  change w * (∫ z, G' z ∂_) ≤ _ at hb1
  linarith only [hpb, hb0, hb1, heq]

theorem recursiveOutputKernel_potential (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (E : ℝ)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (S.dualQuadraticEnergy hfast 0 le_rfl) ν)
    (hb : (∫ z, S.dualQuadraticEnergy hfast 0 le_rfl z ∂ν) ≤ E)
    (hzero : ∀ᵐ z ∂ν, z.1 = 0) (j : ℕ) :
    Integrable (recursiveResidualPotential μ j)
      (recursiveOutputKernel dx dy ℓ α σ μ δ N E O.kernel j ∘ₘ ν) ∧
    (∫ z, recursiveResidualPotential μ j z ∂recursiveOutputKernel dx dy ℓ α σ μ δ N E O.kernel j ∘ₘ ν) ≤
      12 * j * (δ ^ 2 / (10000 * (N + 1 : ℕ) ^ 2)) := by
  induction j with
  | zero =>
    rw [recursiveOutputKernel_zero]
    have hae : (recursiveResidualPotential μ 0) =ᵐ[
        (recursiveStageProgram dx dy ℓ α σ μ δ N E 0).resultKernel O.kernel ∘ₘ ν] 0 := by
      rw [Measure.comp_eq_comp_const_apply]
      apply Kernel.ae_comp_of_ae_ae (measurableSet_eq_fun
        (recursiveResidualPotential_continuous μ 0).measurable measurable_const)
      change ∀ᵐ z ∂ν, ∀ᵐ w ∂(recursiveStageProgram dx dy ℓ α σ μ δ N E 0).resultKernel O.kernel z,
        recursiveResidualPotential μ 0 w = 0
      filter_upwards [hzero] with z hz
      filter_upwards [S.recursiveStageProgram_coefficient O δ N E 0 z] with w hw
      simp only [recursiveResidualPotential, recursiveCurvature_zero, zero_smul, hw, hz,
        sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]
    refine ⟨(integrable_zero _ _ _).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae]
    simp
  | succ j ih =>
    have h0 := S.recursiveOutputKernel_accuracy O hαℓ hfast hδ N E ν hi hb j
    have h1 := S.recursiveOutputKernel_accuracy O hαℓ hfast hδ N E ν hi hb (j + 1)
    rw [recursiveOutputKernel_succ, ← Measure.comp_assoc] at h1 ⊢
    obtain ⟨hpi, hpb⟩ := S.recursive_potential_mean_step O hfast δ N E j _ ih.1 h0.1 h1.1 h0.2.2.1 h1.2.2.1
    refine ⟨hpi, hpb.trans ?_⟩
    calc
      _ ≤ 12 * j * (δ ^ 2 / (10000 * (N + 1 : ℕ) ^ 2)) +
          12 * (δ ^ 2 / (10000 * (N + 1 : ℕ) ^ 2)) := add_le_add_right ih.2 _
      _ = _ := by push_cast; ring

end SCObjective
end FreshGradientMinimax
