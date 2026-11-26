import MinimaxAudit.ComplexityModel
import MinimaxAudit.AdmissibleErrorMeasurability

/-! The actual success events in the revised global complexity definition
are measurable consequences of policy/class membership, not extra success
premises and not merely outer-measure evaluations of arbitrary sets. -/
open Set MeasureTheory
namespace MinimaxAudit

theorem criterion_saved_output_measurable
    {p dx dy B : ℕ} {L D : ℝ} {X : Set (Primal dx)} {Y : Set (Dual dy)}
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (E : OracleErrorCriterion) (A : RandomizedScalarPolicy p dx dy B X Y Seed mu)
    {phi : SaddleSpace dx dy → ℝ} (hphi : AdmissibleScalar p L D X Y phi) :
    Measurable (fun seed => criterionValue E X Y phi
      (Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) B [])) := by
  cases E
  · exact (admissible_actual_errors_measurable A hphi).1
  · exact (admissible_actual_errors_measurable A hphi).2

theorem criterion_success_event_measurable
    {p dx dy B : ℕ} {L D : ℝ} {X : Set (Primal dx)} {Y : Set (Dual dy)}
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (E : OracleErrorCriterion) (A : RandomizedScalarPolicy p dx dy B X Y Seed mu)
    {phi : SaddleSpace dx dy → ℝ} (hphi : AdmissibleScalar p L D X Y phi) (eps : ℝ) :
    MeasurableSet {seed | criterionValue E X Y phi
      (Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) B []) ≤ eps} :=
  measurableSet_le (criterion_saved_output_measurable E A hphi) measurable_const

end MinimaxAudit
