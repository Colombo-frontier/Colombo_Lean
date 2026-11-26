import Bilevel.ParametricContractiveFixedPoint
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! A total Borel Picard-limit evaluator without global contraction or a
measurable validity predicate. Outside the convergence set it returns the
fixed default used by limUnder. At each contractive parameter it equals
the unique Banach fixed point, with no hypothesis on other parameters. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace Bilevel.ParametricPartialFixedPoint
variable {P E : Type*} [MeasurableSpace P] [MetricSpace E] [CompleteSpace E]
  [Nonempty E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def solution (F : P → E → E) (initial : P → E) (p : P) : E :=
  limUnder atTop (fun n : ℕ => (F p)^[n] (initial p))

theorem solution_measurable (F : P → E → E) (initial : P → E)
    (hm : Measurable (fun p : P × E => F p.1 p.2)) (hi : Measurable initial) :
    Measurable (solution F initial) :=
  (StronglyMeasurable.limUnder (fun n =>
    (ParametricContractive.picard_measurable F hm initial hi n).stronglyMeasurable)).measurable

omit [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem solution_eq_of_tendsto (F : P → E → E) (initial : P → E)
    (p : P) (z : E) (hz : Tendsto (fun n : ℕ => (F p)^[n] (initial p)) atTop (𝓝 z)) :
    solution F initial p=z := hz.limUnder_eq

omit [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem solution_eq_fixedPoint (F : P → E → E) (initial : P → E)
    (p : P) {K : ℝ≥0} (hF : ContractingWith K (F p)) :
    solution F initial p=hF.fixedPoint (F p) :=
  solution_eq_of_tendsto F initial p _ (hF.tendsto_iterate_fixedPoint (initial p))

omit [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem solution_fixed (F : P → E → E) (initial : P → E)
    (p : P) {K : ℝ≥0} (hF : ContractingWith K (F p)) :
    F p (solution F initial p)=solution F initial p := by
  rw [solution_eq_fixedPoint F initial p hF]
  exact hF.fixedPoint_isFixedPt

omit [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem solution_unique (F : P → E → E) (initial : P → E)
    (p : P) {K : ℝ≥0} (hF : ContractingWith K (F p)) (z : E) (hz : F p z=z) :
    z=solution F initial p := by
  rw [solution_eq_fixedPoint F initial p hF]
  exact hF.fixedPoint_unique hz

section Inverse
variable {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

def inverse (G : P → V → V) (query initial : P → V) : P → V :=
  solution (fun p z => query p-G p z) initial

theorem inverse_measurable (G : P → V → V) (query initial : P → V)
    (hm : Measurable (fun p : P × V => G p.1 p.2))
    (hq : Measurable query) (hi : Measurable initial) : Measurable (inverse G query initial) :=
  solution_measurable _ initial ((hq.comp measurable_fst).sub hm) hi

omit [MeasurableSpace P] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem inverse_equation (G : P → V → V) (query initial : P → V)
    (p : P) {K : ℝ≥0} (hK : K<1) (hG : LipschitzWith K (G p)) :
    inverse G query initial p+G p (inverse G query initial p)=query p := by
  have hF : ContractingWith K (fun z => query p-G p z) := by
    refine ⟨hK,LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simpa only [dist_sub_left] using hG.dist_le_mul x y
  have hh := solution_fixed (fun p z => query p-G p z) initial p hF
  exact (sub_eq_iff_eq_add.mp hh).symm

omit [MeasurableSpace P] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem inverse_unique (G : P → V → V) (query initial : P → V)
    (p : P) {K : ℝ≥0} (hK : K<1) (hG : LipschitzWith K (G p)) (z : V)
    (hz : z+G p z=query p) : z=inverse G query initial p := by
  have hF : ContractingWith K (fun z => query p-G p z) := by
    refine ⟨hK,LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simpa only [dist_sub_left] using hG.dist_le_mul x y
  exact solution_unique (fun p z => query p-G p z) initial p hF z
    (eq_sub_iff_add_eq.mpr hz).symm
end Inverse
end Bilevel.ParametricPartialFixedPoint
