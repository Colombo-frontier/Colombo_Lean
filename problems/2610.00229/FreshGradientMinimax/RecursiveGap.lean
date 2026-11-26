import FreshGradientMinimax.RecursiveGradient
import FreshGradientMinimax.SaddleResidual

/-! Accuracy of the actual recursive solver in the true max-min gap,
with both the gap and effective-gradient moments proved integrable. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem recursiveSolverProgram_gap (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (E : ℝ)
    (hscale : 5 * ℓ ≤ recursiveMass μ N)
    (ν : Measure (Euclid dy × Joint dx dy)) [IsProbabilityMeasure ν]
    (hi : Integrable (S.dualQuadraticEnergy hfast 0 le_rfl) ν)
    (hb : (∫ z, S.dualQuadraticEnergy hfast 0 le_rfl z ∂ν) ≤ E)
    (hzero : ∀ᵐ z ∂ν, z.1 = 0) :
    Integrable (fun z : Euclid dy × Joint dx dy => S.gap z.2.1 z.2.2)
      ((recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) ∧
    (∫ z, S.gap z.2.1 z.2.2
      ∂(recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) ≤ 2 * δ ^ 2 / μ := by
  obtain ⟨hgi, hgb⟩ := S.recursiveSolverProgram_gradient O hαℓ hfast hδ N E hscale ν hi hb hzero
  obtain ⟨_, hfi, _, hfb⟩ := S.recursiveSolverProgram_accuracy O hαℓ hfast hδ N E ν hi hb
  let m := recursiveMass μ N
  let F : Euclid dy × Joint dx dy → ℝ := fun z => S.fastError m z.2
  let V : Euclid dy × Joint dx dy → ℝ := fun z => ‖gradient S.effectiveValue z.2.2‖ ^ 2
  have hW := (hgi.add (hfi.const_mul m)).div_const μ
  have hgap : Integrable (fun z : Euclid dy × Joint dx dy => S.gap z.2.1 z.2.2)
      ((recursiveSolverProgram dx dy ℓ α σ μ δ N E).resultKernel O.kernel ∘ₘ ν) := by
    apply hW.mono' (S.jointGap_continuous.measurable.comp measurable_snd).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    change ‖S.gap z.2.1 z.2.2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (S.gap_nonneg _ _)]
    exact S.gap_le_fast_effective hfast hscale z.2
  have h := integral_mono hgap hW (fun z => S.gap_le_fast_effective hfast hscale z.2)
  simp only [Pi.add_apply] at h
  rw [integral_div, integral_add hgi (hfi.const_mul m), integral_const_mul m F] at h
  have hm := mul_le_mul_of_nonneg_left hfb (recursiveMass_pos S.μ_pos N).le
  rw [recursiveAccuracy_scaled S.μ_pos δ N N] at hm
  have hc : δ ^ 2 / (10000 * (N + 1 : ℕ) ^ 2) ≤ δ ^ 2 := by
    apply div_le_self (sq_nonneg δ)
    have hN : (1 : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    nlinarith
  refine ⟨hgap, h.trans (div_le_div_of_nonneg_right ?_ S.μ_pos.le)⟩
  change m * (∫ z, F z ∂_) ≤ _ at hm
  linarith only [hgb, hm, hc]

end SCObjective
end FreshGradientMinimax
