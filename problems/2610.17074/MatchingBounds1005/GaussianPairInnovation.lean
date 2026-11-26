import MatchingBounds1005.InnovationGaussianKL
import MatchingBounds1005.GaussianProduct

/-!
# Simultaneous independent Gaussian innovation channels

Both observation maps are fixed before either output is drawn. The two
physical channel noise scales may differ. Their actual singular Gaussian
KL contributions add, with no intervening adaptive decision.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace MatchingBounds1005.GaussianPairInnovation
open GaussianVector AdaptiveGaussian InnovationGaussianKL GaussianComparison

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def response (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d))
    (fitted signal : Vec d) (σ : ℝ) (z : Vec d) : F :=
  L (fitted + projection Vᗮ (signal + σ • z))

theorem response_measurable (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d))
    (fitted signal : Vec d) (σ : ℝ) : Measurable (response L V fitted signal σ) := by
  unfold response
  fun_prop

def law (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d))
    (fitted signal : Vec d) (σ : ℝ) : Measure F :=
  (standardGaussian d).map (response L V fitted signal σ)

instance law_probability (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d))
    (fitted signal : Vec d) (σ : ℝ) : IsProbabilityMeasure (law L V fitted signal σ) :=
  isProbabilityMeasure_map (response_measurable L V fitted signal σ).aemeasurable

def cost (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d)) (hidden : Vec d) (σ : ℝ) : ℝ :=
  ‖(innovationSpace L V).orthogonalProjection hidden‖ ^ 2 / (2 * σ ^ 2)

theorem cost_nonneg (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d))
    (hidden : Vec d) (σ : ℝ) : 0 ≤ cost L V hidden σ := by unfold cost; positivity

theorem law_klDiv (L : Vec d →L[ℝ] F) (V : Submodule ℝ (Vec d))
    (fitted visible hidden : Vec d) {σ : ℝ} (hσ : σ ≠ 0) :
    klDiv (law L V fitted visible σ) (law L V fitted (visible + hidden) σ) =
      ENNReal.ofReal (cost L V hidden σ) :=
  censored_innovation_klDiv L V fitted visible hidden hσ

variable {e : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G]

theorem pair_response_law (L₁ : Vec d →L[ℝ] F) (L₂ : Vec e →L[ℝ] G)
    (V₁ : Submodule ℝ (Vec d)) (V₂ : Submodule ℝ (Vec e))
    (m₁ s₁ : Vec d) (m₂ s₂ : Vec e) (σ₁ σ₂ : ℝ) :
    ((standardGaussian d).prod (standardGaussian e)).map
      (fun z => (response L₁ V₁ m₁ s₁ σ₁ z.1, response L₂ V₂ m₂ s₂ σ₂ z.2)) =
        (law L₁ V₁ m₁ s₁ σ₁).prod (law L₂ V₂ m₂ s₂ σ₂) := by
  exact (Measure.map_prod_map (standardGaussian d) (standardGaussian e)
    (response_measurable L₁ V₁ m₁ s₁ σ₁) (response_measurable L₂ V₂ m₂ s₂ σ₂)).symm

/-- Actual simultaneous two-channel innovation KL with the source scales. -/
theorem pair_klDiv (L₁ : Vec d →L[ℝ] F) (L₂ : Vec e →L[ℝ] G)
    (V₁ : Submodule ℝ (Vec d)) (V₂ : Submodule ℝ (Vec e))
    (m₁ visible₁ hidden₁ : Vec d) (m₂ visible₂ hidden₂ : Vec e)
    {σ₁ σ₂ : ℝ} (hσ₁ : σ₁ ≠ 0) (hσ₂ : σ₂ ≠ 0) :
    klDiv (((standardGaussian d).prod (standardGaussian e)).map
      (fun z => (response L₁ V₁ m₁ visible₁ σ₁ z.1, response L₂ V₂ m₂ visible₂ σ₂ z.2)))
      (((standardGaussian d).prod (standardGaussian e)).map
        (fun z => (response L₁ V₁ m₁ (visible₁ + hidden₁) σ₁ z.1,
          response L₂ V₂ m₂ (visible₂ + hidden₂) σ₂ z.2))) =
      ENNReal.ofReal (cost L₁ V₁ hidden₁ σ₁ + cost L₂ V₂ hidden₂ σ₂) := by
  have h₁ := law_klDiv L₁ V₁ m₁ visible₁ hidden₁ hσ₁
  have h₂ := law_klDiv L₂ V₂ m₂ visible₂ hidden₂ hσ₂
  have hf₁ : klDiv (law L₁ V₁ m₁ visible₁ σ₁) (law L₁ V₁ m₁ (visible₁ + hidden₁) σ₁) ≠ ∞ :=
    h₁ ▸ ENNReal.ofReal_ne_top
  have hf₂ : klDiv (law L₂ V₂ m₂ visible₂ σ₂) (law L₂ V₂ m₂ (visible₂ + hidden₂) σ₂) ≠ ∞ :=
    h₂ ▸ ENNReal.ofReal_ne_top
  rw [pair_response_law, pair_response_law,
    klDiv_prod (klDiv_ne_top_iff.mp hf₁).1 (klDiv_ne_top_iff.mp hf₂).1
      (klDiv_ne_top_iff.mp hf₁).2 (klDiv_ne_top_iff.mp hf₂).2,
    h₁, h₂, ENNReal.ofReal_add (cost_nonneg L₁ V₁ hidden₁ σ₁) (cost_nonneg L₂ V₂ hidden₂ σ₂)]

end MatchingBounds1005.GaussianPairInnovation
