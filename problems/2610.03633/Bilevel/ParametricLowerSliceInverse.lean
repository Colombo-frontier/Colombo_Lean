import Bilevel.ParametricScalarInverse
import Bilevel.ChiExtensionSliceInverse

/-! Borel partial-conjugate inversion with the outerPoint variable held fixed.
The contraction is derived from the full scalar Hessian bound, while only
the lower slice is inverted. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ParametricScalarInverse
open PrimitiveGeometry ChiExtension
set_option maxHeartbeats 800000

variable {P X U V : Type*}
  [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace (Joint U V)] [BorelSpace (Joint U V)]

omit [MeasurableSpace P] [OpensMeasurableSpace P] [CompleteSpace X]
  [CompleteSpace U] [FiniteDimensional ℝ U] [CompleteSpace V] [FiniteDimensional ℝ V]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace (Joint U V)] [BorelSpace (Joint U V)] in
theorem lowerSlice_family_continuous (f : P → Joint (Joint X U) V → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p : (P × X) × Joint U V => lowerSlice (f p.1.1) p.1.2 p.2) := by
  have hp : Continuous (fun p : (P × X) × Joint U V => pack p.1.2 p.2) :=
    (packLinear (X:=X) (Y:=Joint U V)).continuous.comp (continuous_fst.snd.prodMk continuous_snd)
  have hz := (associateLeft (X:=X) (U:=U) (V:=V)).continuous.comp hp
  exact hf.comp (continuous_fst.fst.prodMk hz)

omit [CompleteSpace X] in
theorem lowerSlice_gradient_measurable (f : P → Joint (Joint X U) V → ℝ)
    (hf : Continuous (Function.uncurry f)) (outerPoint : P → X) (hm : Measurable outerPoint) :
    Measurable (fun p : P × Joint U V => gradient (lowerSlice (f p.1) (outerPoint p.1)) p.2) := by
  have hg := ParametricGradient.gradient_measurable
    (fun p : P × X => lowerSlice (f p.1) p.2) (lowerSlice_family_continuous f hf)
  exact hg.comp ((measurable_fst.prodMk (hm.comp measurable_fst)).prodMk measurable_snd)

def inverseSlice (S : Set P) (f : P → Joint (Joint X U) V → ℝ) (outerPoint : P → X)
    (query fallback : P → Joint U V) (K : NNReal) (hK : K < 1)
    (hf : ∀ p : S, ContDiff ℝ 3 (f p.1))
    (hH : ∀ p : S, ∀ z, ‖iteratedFDeriv ℝ 2 (f p.1) z‖ ≤ (K : ℝ)) : P → Joint U V :=
  ParametricContractive.inverseOn S (fun p => gradient (lowerSlice (f p) (outerPoint p)))
    query fallback hK (fun p => lowerSlice_gradient_lipschitz (hf p) K (hH p) (outerPoint p))

theorem inverseSlice_measurable (S : Set P) (hS : MeasurableSet S)
    (f : P → Joint (Joint X U) V → ℝ) (hc : Continuous (Function.uncurry f))
    (outerPoint : P → X) (hm : Measurable outerPoint) (query fallback : P → Joint U V)
    (hq : Measurable query) (hb : Measurable fallback) (K : NNReal) (hK : K < 1)
    (hf : ∀ p : S, ContDiff ℝ 3 (f p.1))
    (hH : ∀ p : S, ∀ z, ‖iteratedFDeriv ℝ 2 (f p.1) z‖ ≤ (K : ℝ)) :
    Measurable (inverseSlice S f outerPoint query fallback K hK hf hH) :=
  ParametricContractive.inverseOn_measurable S hS _ query fallback hK _
    (lowerSlice_gradient_measurable f hc outerPoint hm) hq hb

omit [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace (Joint U V)] [BorelSpace (Joint U V)] in
theorem inverseSlice_equation (S : Set P) (f : P → Joint (Joint X U) V → ℝ) (outerPoint : P → X)
    (query fallback : P → Joint U V) (K : NNReal) (hK : K < 1)
    (hf : ∀ p : S, ContDiff ℝ 3 (f p.1))
    (hH : ∀ p : S, ∀ z, ‖iteratedFDeriv ℝ 2 (f p.1) z‖ ≤ (K : ℝ)) (p : P) (hp : p ∈ S) :
    inverseSlice S f outerPoint query fallback K hK hf hH p +
      gradient (lowerSlice (f p) (outerPoint p)) (inverseSlice S f outerPoint query fallback K hK hf hH p) = query p :=
  ParametricContractive.inverseOn_equation S _ query fallback hK _ p hp

omit [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace (Joint U V)] [BorelSpace (Joint U V)] in
theorem inverseSlice_unique (S : Set P) (f : P → Joint (Joint X U) V → ℝ) (outerPoint : P → X)
    (query fallback : P → Joint U V) (K : NNReal) (hK : K < 1)
    (hf : ∀ p : S, ContDiff ℝ 3 (f p.1))
    (hH : ∀ p : S, ∀ z, ‖iteratedFDeriv ℝ 2 (f p.1) z‖ ≤ (K : ℝ)) (p : P) (hp : p ∈ S)
    (z : Joint U V) (hz : z + gradient (lowerSlice (f p) (outerPoint p)) z = query p) :
    z = inverseSlice S f outerPoint query fallback K hK hf hH p :=
  ParametricContractive.inverseOn_unique S _ query fallback hK _ p hp z hz

omit [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace (Joint U V)] [BorelSpace (Joint U V)] in
theorem inverseSlice_eq_jointSolution (S : Set P) (f : P → Joint (Joint X U) V → ℝ)
    (outerPoint : P → X) (query fallback : P → Joint U V) (K : NNReal) (hK : K < 1)
    (hf : ∀ p : S, ContDiff ℝ 3 (f p.1))
    (hH : ∀ p : S, ∀ z, ‖iteratedFDeriv ℝ 2 (f p.1) z‖ ≤ (K : ℝ)) (p : P) (hp : p ∈ S) :
    inverseSlice S f outerPoint query fallback K hK hf hH p =
      PartialLegendre.jointSolution (reassociated_gradient_lipschitz (hf ⟨p,hp⟩) K (hH ⟨p,hp⟩))
        hK (outerPoint p) (query p) := by
  apply PartialLegendre.jointSolution_of_equation
  rw [← lowerSlice_gradient (hf ⟨p,hp⟩)]
  exact inverseSlice_equation S f outerPoint query fallback K hK hf hH p hp

end Bilevel.ParametricScalarInverse
