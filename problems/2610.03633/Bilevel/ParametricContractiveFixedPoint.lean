import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! A canonical jointly measurable parameterized Banach fixed point.
Measurability follows from the actual Picard iterates and their pointwise
convergence; no measurable choice of solutions or frame completions is used. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace Bilevel.ParametricContractive

variable {P E : Type*} [MeasurableSpace P] [MetricSpace E] [CompleteSpace E]
  [Nonempty E] [MeasurableSpace E] [BorelSpace E]

def solution (F : P → E → E) {K : ℝ≥0} (hF : ∀ p,ContractingWith K (F p)) (p : P) : E :=
  (hF p).fixedPoint (F p)

omit [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E] in
theorem solution_fixed (F : P → E → E) {K : ℝ≥0} (hF : ∀ p,ContractingWith K (F p)) (p : P) :
    F p (solution F hF p)=solution F hF p :=
  (hF p).fixedPoint_isFixedPt

omit [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E] in
theorem solution_unique (F : P → E → E) {K : ℝ≥0} (hF : ∀ p,ContractingWith K (F p))
    (p : P) (z : E) (hz : F p z=z) : z=solution F hF p :=
  (hF p).fixedPoint_unique hz

omit [MetricSpace E] [CompleteSpace E] [Nonempty E] [BorelSpace E] in
theorem picard_measurable (F : P → E → E) (hF : Measurable (fun p : P × E => F p.1 p.2))
    (initial : P → E) (hi : Measurable initial) (n : ℕ) :
    Measurable (fun p => (F p)^[n] (initial p)) := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using hF.comp (measurable_id.prodMk ih)

omit [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E] in
theorem picard_converges (F : P → E → E) {K : ℝ≥0} (hF : ∀ p,ContractingWith K (F p))
    (p : P) (z : E) : Tendsto (fun n => (F p)^[n] z) atTop (𝓝 (solution F hF p)) :=
  (hF p).tendsto_iterate_fixedPoint z

theorem solution_measurable (F : P → E → E) {K : ℝ≥0} (hF : ∀ p,ContractingWith K (F p))
    (hm : Measurable (fun p : P × E => F p.1 p.2)) : Measurable (solution F hF) := by
  let z : E := Classical.choice (inferInstance : Nonempty E)
  apply measurable_of_tendsto_metrizable
    (fun n => picard_measurable F hm (fun _ => z) measurable_const n)
  apply tendsto_pi_nhds.mpr
  intro p
  exact picard_converges F hF p z

omit [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E] in
theorem solution_stability (F : P → E → E) {K : ℝ≥0} (hF : ∀ p,ContractingWith K (F p))
    (p q : P) (C : ℝ) (hclose : ∀ z,dist (F p z) (F q z)≤C) :
    dist (solution F hF p) (solution F hF q)≤C/(1-(K:ℝ)) :=
  (hF p).fixedPoint_lipschitz_in_map (hF q) hclose

section Inverse
variable {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

def inverseField (G : P → V → V) (query : P → V) (p : P) (z : V) : V := query p-G p z

omit [MeasurableSpace P] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem inverseField_contracting (G : P → V → V) (query : P → V) {K : ℝ≥0}
    (hK : K<1) (hG : ∀ p,LipschitzWith K (G p)) (p : P) :
    ContractingWith K (inverseField G query p) := by
  refine ⟨hK,LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simpa only [inverseField,dist_sub_left] using (hG p).dist_le_mul x y

def inverse (G : P → V → V) (query : P → V) {K : ℝ≥0}
    (hK : K<1) (hG : ∀ p,LipschitzWith K (G p)) : P → V :=
  solution (inverseField G query) (inverseField_contracting G query hK hG)

omit [MeasurableSpace P] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem inverse_equation (G : P → V → V) (query : P → V) {K : ℝ≥0}
    (hK : K<1) (hG : ∀ p,LipschitzWith K (G p)) (p : P) :
    inverse G query hK hG p+G p (inverse G query hK hG p)=query p := by
  have h := solution_fixed (inverseField G query) (inverseField_contracting G query hK hG) p
  exact (sub_eq_iff_eq_add.mp h).symm

omit [MeasurableSpace P] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem inverse_unique (G : P → V → V) (query : P → V) {K : ℝ≥0}
    (hK : K<1) (hG : ∀ p,LipschitzWith K (G p)) (p : P) (z : V)
    (hz : z+G p z=query p) : z=inverse G query hK hG p := by
  exact solution_unique (inverseField G query) (inverseField_contracting G query hK hG) p z
    (eq_sub_iff_add_eq.mpr hz).symm

theorem inverse_measurable (G : P → V → V) (query : P → V) {K : ℝ≥0}
    (hK : K<1) (hG : ∀ p,LipschitzWith K (G p))
    (hm : Measurable (fun p : P × V => G p.1 p.2)) (hq : Measurable query) :
    Measurable (inverse G query hK hG) :=
  solution_measurable (inverseField G query) (inverseField_contracting G query hK hG)
    ((hq.comp measurable_fst).sub hm)

end Inverse
end Bilevel.ParametricContractive

