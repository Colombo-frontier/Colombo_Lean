import Bilevel.ParametricContractiveValidData
import Bilevel.ParametricGradientMeasurable
import Bilevel.GradientJetBounds

/-! A canonical Borel inverse constructed from actual scalar Hessian bounds.
The scalar family is defined on arbitrary finite transcript data, while its
smoothness and contraction certificate are needed only on the measurable
valid-data set. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ParametricScalarInverse

variable {P E : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gradient_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 3 f) (K : NNReal)
    (hH : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ (K : ℝ)) :
    LipschitzWith K (gradient f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((GradientJetBounds.gradient_contDiff hf).differentiable (by norm_num))
  intro z
  exact_mod_cast (GradientJetBounds.hessian_norm_eq hf z).le.trans (hH z)

def inverse (S : Set P) (f : P → E → ℝ) (query fallback : P → E) (K : NNReal)
    (hK : K < 1) (hf : ∀ p : S, ContDiff ℝ 3 (f p.1))
    (hH : ∀ p : S, ∀ z, ‖iteratedFDeriv ℝ 2 (f p.1) z‖ ≤ (K : ℝ)) : P → E :=
  ParametricContractive.inverseOn S (fun p => gradient (f p)) query fallback hK
    (fun p => gradient_lipschitz (hf p) K (hH p))

theorem inverse_measurable (S : Set P) (hS : MeasurableSet S) (f : P → E → ℝ)
    (hc : Continuous (Function.uncurry f)) (query fallback : P → E)
    (hq : Measurable query) (hb : Measurable fallback) (K : NNReal)
    (hK : K < 1) (hf : ∀ p : S, ContDiff ℝ 3 (f p.1))
    (hH : ∀ p : S, ∀ z, ‖iteratedFDeriv ℝ 2 (f p.1) z‖ ≤ (K : ℝ)) :
    Measurable (inverse S f query fallback K hK hf hH) :=
  ParametricContractive.inverseOn_measurable S hS _ query fallback hK _
    (ParametricGradient.gradient_measurable f hc) hq hb

omit [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inverse_equation (S : Set P) (f : P → E → ℝ) (query fallback : P → E) (K : NNReal)
    (hK : K < 1) (hf : ∀ p : S, ContDiff ℝ 3 (f p.1))
    (hH : ∀ p : S, ∀ z, ‖iteratedFDeriv ℝ 2 (f p.1) z‖ ≤ (K : ℝ)) (p : P) (hp : p ∈ S) :
    inverse S f query fallback K hK hf hH p +
      gradient (f p) (inverse S f query fallback K hK hf hH p) = query p :=
  ParametricContractive.inverseOn_equation S _ query fallback hK _ p hp

omit [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inverse_unique (S : Set P) (f : P → E → ℝ) (query fallback : P → E) (K : NNReal)
    (hK : K < 1) (hf : ∀ p : S, ContDiff ℝ 3 (f p.1))
    (hH : ∀ p : S, ∀ z, ‖iteratedFDeriv ℝ 2 (f p.1) z‖ ≤ (K : ℝ)) (p : P) (hp : p ∈ S)
    (z : E) (hz : z + gradient (f p) z = query p) :
    z = inverse S f query fallback K hK hf hH p :=
  ParametricContractive.inverseOn_unique S _ query fallback hK _ p hp z hz

end Bilevel.ParametricScalarInverse
