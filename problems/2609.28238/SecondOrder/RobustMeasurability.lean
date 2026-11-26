import SecondOrder.RobustCenter
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {R : ℕ}

/-- The finite comparison matrix used by the first-admissible-point selector. -/
def neighborCode (z : Fin R → E) (r : ℝ) : Fin R → Fin R → Bool :=
  fun i j => if dist (z j) (z i) ≤ 2*r then true else false

def codedCandidates (b : Fin R → Fin R → Bool) : Finset (Fin R) :=
  Finset.univ.filter (fun i => R < 2*(Finset.univ.filter (fun j => b i j = true)).card)

def codedCenterIndex (hR : 0 < R) (b : Fin R → Fin R → Bool) : Fin R :=
  if h : (codedCandidates b).Nonempty then (codedCandidates b).min' h else ⟨0,hR⟩

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem codedCandidates_neighborCode (z : Fin R → E) (r : ℝ) :
    codedCandidates (neighborCode z r) = centerCandidates z r := by
  simp only [codedCandidates, neighborCode, centerCandidates, goodObservations]
  congr 1
  funext i
  congr 3
  ext j
  simp

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem robustCenter_eq_coded (hR : 0 < R) (z : Fin R → E) (r : ℝ) :
    robustCenter hR z r = z (codedCenterIndex hR (neighborCode z r)) := by
  simp only [robustCenter, codedCenterIndex, codedCandidates_neighborCode]
  split_ifs <;> rfl

theorem neighborCode_measurable (r : ℝ) :
    Measurable (fun z : Fin R → E => neighborCode z r) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact Measurable.ite (measurableSet_le ((measurable_pi_apply j).dist (measurable_pi_apply i))
    measurable_const) measurable_const measurable_const

/-- The selector in the manuscript is Borel; ties use the first index and the
empty-candidate case uses index zero. -/
theorem robustCenter_measurable (hR : 0 < R) (r : ℝ) :
    Measurable (fun z : Fin R → E => robustCenter hR z r) := by
  have hi : Measurable (fun z : Fin R → E => codedCenterIndex hR (neighborCode z r)) :=
    (measurable_of_finite (codedCenterIndex hR)).comp (neighborCode_measurable r)
  have he : Measurable (fun p : (Fin R → E) × Fin R => p.1 p.2) :=
    measurable_from_prod_countable (fun i => measurable_pi_apply i)
  simpa only [Function.comp_def, id_eq, ← robustCenter_eq_coded] using
    he.comp (measurable_id.prodMk hi)

end
end SecondOrder
