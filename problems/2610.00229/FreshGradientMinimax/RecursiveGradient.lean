import FreshGradientMinimax.RecursiveMoments

/-! The final small-gradient guarantee for the actual original-query
recursive solver. Integrability is derived along with the expectation
bound, and the only initialization moment is the unconditional energy. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem effective_gradient_continuous : Continuous (gradient S.effectiveValue) := by
  have h : (gradient S.effectiveValue) = S.effectiveGradient := funext S.true_effective_gradient
  rw [h]
  exact (S.toNCObjective.jointGradient_continuous.snd.comp
    (S.sliceMin_continuous.prodMk continuous_id)).neg

theorem recursiveSolverProgram_gradient (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (E : ℝ)
    (hscale : 5 * ℓ ≤ recursiveMass μ N)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (S.dualQuadraticEnergy hfast 0 le_rfl) ν)
    (hb : (∫ z, S.dualQuadraticEnergy hfast 0 le_rfl z ∂ν) ≤ E)
    (hzero : ∀ᵐ z ∂ν, z.1 = 0) :
    Integrable (fun z : Euclid dy × Joint dx dy => ‖gradient S.effectiveValue z.2.2‖ ^ 2)
      ((recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ z, ‖gradient S.effectiveValue z.2.2‖ ^ 2
      ∂(recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) ≤ δ ^ 2 := by
  have hacc := S.recursiveSolverProgram_accuracy O hαℓ hfast hδ N E ν hi hb
  have hpot := S.recursiveOutputKernel_potential O hαℓ hfast hδ N E ν hi hb hzero N
  rw [recursiveOutputKernel_final] at hpot
  let G := S.dualQuadraticGap hfast (recursiveCurvature μ N) (recursiveCurvature_nonneg S.μ_pos N)
  let P := recursiveResidualPotential (dx := dx) (dy := dy) μ N
  let c : ℝ := δ ^ 2 / (10000 * (N + 1 : ℕ) ^ 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hW := (hacc.1.const_mul (8 * recursiveMass μ N)).add (hpot.1.const_mul (2 * (N + 1 : ℕ)))
  have hgi : Integrable (fun z : Euclid dy × Joint dx dy => ‖gradient S.effectiveValue z.2.2‖ ^ 2)
      ((recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) := by
    apply hW.mono' ((S.effective_gradient_continuous.measurable.comp measurable_snd.snd).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      change ‖‖gradient S.effectiveValue z.2.2‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact S.recursive_gradient_potential hfast N hscale z)
  have hgb := integral_mono hgi hW (S.recursive_gradient_potential hfast N hscale)
  simp only [Pi.add_apply] at hgb
  rw [integral_add (hacc.1.const_mul (8 * recursiveMass μ N)) (hpot.1.const_mul (2 * (N + 1 : ℕ))),
    integral_const_mul (8 * recursiveMass μ N) G, integral_const_mul (2 * ((N + 1 : ℕ) : ℝ)) P] at hgb
  have hgap := mul_le_mul_of_nonneg_left hacc.2.2.1 (recursiveMass_pos S.μ_pos N).le
  rw [recursiveAccuracy_scaled S.μ_pos δ N N] at hgap
  have hpn := mul_le_mul_of_nonneg_left hpot.2 (by positivity : (0 : ℝ) ≤ 2 * (N + 1 : ℕ))
  have hraw : (∫ z, ‖gradient S.effectiveValue z.2.2‖ ^ 2
      ∂(recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) ≤
        8 * c + 24 * N * (N + 1 : ℕ) * c := by
    change recursiveMass μ N * (∫ z, G z ∂_) ≤ c at hgap
    change 2 * (N + 1 : ℕ) * (∫ z, P z ∂_) ≤ 2 * (N + 1 : ℕ) * (12 * N * c) at hpn
    nlinarith only [hgb, hgap, hpn]
  refine ⟨hgi, hraw.trans ?_⟩
  have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  calc
    _ ≤ 32 * (N + 1 : ℕ) ^ 2 * c := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      push_cast at hN ⊢
      nlinarith only [hc, mul_nonneg hN0 hc, mul_nonneg (sq_nonneg (N : ℝ)) hc]
    _ = (32 / 10000 : ℝ) * δ ^ 2 := by dsimp [c]; field_simp; ring
    _ ≤ δ ^ 2 := by nlinarith [sq_nonneg δ]

end SCObjective
end FreshGradientMinimax
