import MinimaxAudit.Model

/-! Audit of the deterministic/randomized class boundary.
A constant seed does not remove measurability requirements on histories.
This proves the exact condition needed for the usual inclusion argument;
it does not assume every unrestricted deterministic policy meets it. -/
namespace MinimaxAudit
open MeasureTheory

 theorem constant_seed_map_measurable_iff {H Z : Type*} [MeasurableSpace H]
    [MeasurableSpace Z] (f : H → Z) :
    Measurable (fun s : Unit × H => f s.2) ↔ Measurable f := by
  constructor
  · intro h
    exact h.comp (measurable_const.prodMk measurable_id : Measurable (fun x : H => ((), x)))
  · intro h
    exact h.comp measurable_snd

/-- Exact source-policy version: seed-independent query/output maps are
jointly measurable precisely when the original deterministic maps are. -/
theorem constant_seed_policy_measurability_iff {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (A : DeterministicScalarPolicy p dx dy N X Y) :
    (Measurable (fun s : Unit × ScalarHistory p dx dy => A.query s.2) ∧
      Measurable (fun s : Unit × ScalarHistory p dx dy => A.output s.2)) ↔
    (Measurable A.query ∧ Measurable A.output) := by
  exact and_congr (constant_seed_map_measurable_iff A.query)
    (constant_seed_map_measurable_iff A.output)

/-- A nonmeasurable history map cannot be embedded unchanged by adding a
constant random seed. The nonmeasurability hypothesis is explicit. -/
theorem no_constant_seed_lift_of_nonmeasurable_output {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (A : DeterministicScalarPolicy p dx dy N X Y) (hA : ¬ Measurable A.output) :
    ¬ Measurable (fun s : Unit × ScalarHistory p dx dy => A.output s.2) := by
  exact fun h => hA ((constant_seed_map_measurable_iff A.output).1 h)
end MinimaxAudit
