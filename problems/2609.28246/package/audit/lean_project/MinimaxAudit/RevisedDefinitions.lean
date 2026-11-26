import MinimaxAudit.RevisedModel

/-! Full source-facing policy definitions for the separately frozen revision.
The arbitrary-map class remains an internal stronger lower-bound model. -/
namespace MinimaxAudit
open MeasureTheory
open scoped ENNReal

/-- Revised random definition and the independently fixed-instance quantifier
constraint, without asserting a lower-bound witness as an assumed field. -/
theorem revised_randomized_definition_full {p dx dy N : ℕ}
    (X : Set (Primal dx)) (Y : Set (Dual dy))
    (Seed : Type*) [MeasurableSpace Seed] (mu : Measure Seed) :
    (Nonempty (RandomizedScalarPolicy p dx dy N X Y Seed mu) ↔
      IsProbabilityMeasure mu ∧
      ∃ family : Seed → BorelDeterministicScalarPolicy p dx dy N X Y,
        Measurable (fun s : Seed × ScalarHistory p dx dy => (family s.1).policy.query s.2) ∧
        Measurable (fun s : Seed × ScalarHistory p dx dy => (family s.1).policy.output s.2)) ∧
    (∀ (Instance : Type*) (failure : Instance → Seed → Prop) (threshold : ℝ≥0∞),
      FixedInstanceObstruction mu failure threshold ↔
        ∃ omega, threshold ≤ mu {seed | failure omega seed}) := by
  exact ⟨revised_randomized_definition_source, fun _ _ _ => Iff.rfl⟩
end MinimaxAudit
