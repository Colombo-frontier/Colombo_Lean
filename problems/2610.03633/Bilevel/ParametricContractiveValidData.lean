import Bilevel.ParametricContractiveFixedPoint

/-! A measurable canonical inverse on valid data, with an explicit fallback
on invalid observer transcripts. Contraction is required only on the valid
data subtype; arbitrary numeric column arrays need not satisfy it. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace Bilevel.ParametricContractive

variable {P E : Type*} [MeasurableSpace P] [MetricSpace E] [CompleteSpace E]
  [Nonempty E] [MeasurableSpace E] [BorelSpace E]

open Classical in
def solutionOn (S : Set P) (F : P → E → E) {K : ℝ≥0}
    (hF : ∀ p : S,ContractingWith K (F p.1)) (fallback : P → E) (p : P) : E :=
  if hp : p∈S then solution (fun p : S => F p.1) hF ⟨p,hp⟩ else fallback p

theorem solutionOn_measurable (S : Set P) (hS : MeasurableSet S) (F : P → E → E) {K : ℝ≥0}
    (hF : ∀ p : S,ContractingWith K (F p.1)) (fallback : P → E) (hfallback : Measurable fallback)
    (hm : Measurable (fun p : P × E => F p.1 p.2)) :
    Measurable (solutionOn S F hF fallback) := by
  classical
  have hr : Measurable (fun p : S × E => F p.1.1 p.2) :=
    hm.comp (measurable_subtype_coe.prodMap measurable_id)
  exact (solution_measurable _ hF hr).dite (hfallback.comp measurable_subtype_coe) hS

omit [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E] in
theorem solutionOn_fixed (S : Set P) (F : P → E → E) {K : ℝ≥0}
    (hF : ∀ p : S,ContractingWith K (F p.1)) (fallback : P → E) (p : P) (hp : p∈S) :
    F p (solutionOn S F hF fallback p)=solutionOn S F hF fallback p := by
  simp only [solutionOn,dif_pos hp]
  exact solution_fixed _ hF ⟨p,hp⟩

omit [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E] in
theorem solutionOn_unique (S : Set P) (F : P → E → E) {K : ℝ≥0}
    (hF : ∀ p : S,ContractingWith K (F p.1)) (fallback : P → E) (p : P) (hp : p∈S)
    (z : E) (hz : F p z=z) : z=solutionOn S F hF fallback p := by
  simp only [solutionOn,dif_pos hp]
  exact solution_unique _ hF ⟨p,hp⟩ z hz

section Inverse
variable {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

def inverseOn (S : Set P) (G : P → V → V) (query fallback : P → V) {K : ℝ≥0}
    (hK : K<1) (hG : ∀ p : S,LipschitzWith K (G p.1)) : P → V :=
  solutionOn S (inverseField G query)
    (fun p => inverseField_contracting (fun p : S => G p.1) (fun p : S => query p.1) hK hG p)
    fallback

theorem inverseOn_measurable (S : Set P) (hS : MeasurableSet S)
    (G : P → V → V) (query fallback : P → V) {K : ℝ≥0}
    (hK : K<1) (hG : ∀ p : S,LipschitzWith K (G p.1))
    (hm : Measurable (fun p : P × V => G p.1 p.2))
    (hq : Measurable query) (hfallback : Measurable fallback) :
    Measurable (inverseOn S G query fallback hK hG) :=
  solutionOn_measurable S hS (inverseField G query) _ fallback hfallback
    ((hq.comp measurable_fst).sub hm)

omit [MeasurableSpace P] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem inverseOn_equation (S : Set P) (G : P → V → V) (query fallback : P → V) {K : ℝ≥0}
    (hK : K<1) (hG : ∀ p : S,LipschitzWith K (G p.1)) (p : P) (hp : p∈S) :
    inverseOn S G query fallback hK hG p+G p (inverseOn S G query fallback hK hG p)=query p := by
  have h := solutionOn_fixed S (inverseField G query)
    (fun p => inverseField_contracting (fun p : S => G p.1) (fun p : S => query p.1) hK hG p)
    fallback p hp
  exact (sub_eq_iff_eq_add.mp h).symm

omit [MeasurableSpace P] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem inverseOn_unique (S : Set P) (G : P → V → V) (query fallback : P → V) {K : ℝ≥0}
    (hK : K<1) (hG : ∀ p : S,LipschitzWith K (G p.1)) (p : P) (hp : p∈S)
    (z : V) (hz : z+G p z=query p) : z=inverseOn S G query fallback hK hG p :=
  solutionOn_unique S (inverseField G query) _ fallback p hp z (eq_sub_iff_add_eq.mpr hz).symm

end Inverse
end Bilevel.ParametricContractive
