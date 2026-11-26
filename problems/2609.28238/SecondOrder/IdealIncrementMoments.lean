import SecondOrder.IdealIncrementHistory
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped Classical BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Both physical increment energies are integrable, with the bounds derived
from actual loss decrease. They are not additional moment hypotheses. -/
theorem CommonLoss.idealIncrement_energy (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M : ℕ) :
    let a := mixedIdealDrift (M := M) P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy
    let m := mixedIdealInnovation (M := M) P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy
    (Integrable (fun w => ∑ i, ‖a i w‖^2) (η.prod (signLaw M)) ∧
      (∫ w, ∑ i, ‖a i w‖^2 ∂η.prod (signLaw M)) ≤ P.gap/P.gradientLip) ∧
    (Integrable (fun w => ∑ i, ‖m i w‖^2) (η.prod (signLaw M)) ∧
      (∫ w, ∑ i, ‖m i w‖^2 ∂η.prod (signLaw M)) ≤ 16*P.gap/(3*γ)) := by
  dsimp only
  simp_rw [mixedIdealDrift_energy,mixedIdealInnovation_energy]
  exact h.measurableIdealRun_energy hτ hγ hm hv M

theorem CommonLoss.idealIncrement_second_moments (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    {M : ℕ} (i : Fin M) :
    Integrable (fun w => ‖mixedIdealDrift P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy i w‖^2)
      (η.prod (signLaw M)) ∧
    Integrable (fun w => ‖mixedIdealInnovation P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy i w‖^2)
      (η.prod (signLaw M)) := by
  have he := h.measurableIdealRun_energy (η := η) hτ hγ hm hv M
  constructor
  · apply he.1.1.mono' ((mixedIdealDrift_measurable _ _ hm i).norm.pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact mixedIdealDrift_sq_le_energy _ _ _ i w
  · apply he.2.1.mono' ((mixedIdealInnovation_measurable _ _ hm i).norm.pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact mixedIdealInnovation_sq_le_energy _ _ _ i w

theorem CommonLoss.idealIncrement_memLp (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    {M : ℕ} (i : Fin M) :
    MemLp (mixedIdealDrift P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy i) 2
      (η.prod (signLaw M)) ∧
    MemLp (mixedIdealInnovation P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy i) 2
      (η.prod (signLaw M)) := by
  have hs := h.idealIncrement_second_moments (η := η) hτ hγ hm hv i
  exact ⟨(memLp_two_iff_integrable_sq_norm (mixedIdealDrift_measurable _ _ hm i).aestronglyMeasurable).mpr hs.1,
    (memLp_two_iff_integrable_sq_norm (mixedIdealInnovation_measurable _ _ hm i).aestronglyMeasurable).mpr hs.2⟩

theorem CommonLoss.idealIncrement_integrable (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    {M : ℕ} (i : Fin M) :
    Integrable (mixedIdealDrift P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy i)
      (η.prod (signLaw M)) ∧
    Integrable (mixedIdealInnovation P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy i)
      (η.prod (signLaw M)) := by
  have hs := h.idealIncrement_memLp (η := η) hτ hγ hm hv i
  exact ⟨hs.1.integrable (by norm_num),hs.2.integrable (by norm_num)⟩

/-- Fresh signs imply orthogonality of the actual curvature increments,
including arbitrary independent external randomness and stopped paths. -/
theorem CommonLoss.idealInnovation_orthogonal (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    {M : ℕ} (i j : Fin M) (hij : i ≠ j) :
    (∫ w, ⟪mixedIdealInnovation P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy i w,
      mixedIdealInnovation P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy j w⟫_ℝ
      ∂η.prod (signLaw M)) = 0 := by
  exact mixedInnovation_orthogonal _ (fun k => (h.idealIncrement_integrable hτ hγ hm hv k).2)
    (fun k => (h.idealIncrement_second_moments hτ hγ hm hv k).2) i j hij

end
end SecondOrder
