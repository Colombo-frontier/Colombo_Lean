import MinimaxAudit.Model
import MinimaxAudit.MeasurableExecution

/-! The revised source requires both deterministic decision maps to be Borel
on the canonical disjoint union of finite scalar-response histories. The old
unrestricted class is retained, so all existing lower bounds remain stronger. -/
open Set MeasureTheory
namespace MinimaxAudit
noncomputable section

structure BorelDeterministicScalarPolicy (p dx dy N : ℕ)
    (X : Set (Primal dx)) (Y : Set (Dual dy)) where
  policy : DeterministicScalarPolicy p dx dy N X Y
  measurable_query : Measurable policy.query
  measurable_output : Measurable policy.output

theorem borel_deterministic_policy_source {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} :
    Nonempty (BorelDeterministicScalarPolicy p dx dy N X Y) ↔
    ∃ query : ScalarHistory p dx dy → Option (SaddleSpace dx dy),
    ∃ output : ScalarHistory p dx dy → SaddleSpace dx dy,
      (∀ h, N ≤ h.length → query h = none) ∧
      (∀ h z, query h = some z → z ∈ productDomain X Y) ∧
      (∀ h, output h ∈ productDomain X Y) ∧
      Measurable query ∧ Measurable output := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.policy.query, A.policy.output, A.policy.cap,
      A.policy.feasible_query, A.policy.feasible_output, A.measurable_query, A.measurable_output⟩
  · rintro ⟨q, o, hc, hq, ho, hmq, hmo⟩
    exact ⟨⟨⟨q, o, hc, hq, ho⟩, hmq, hmo⟩⟩



namespace BorelDeterministicScalarPolicy
variable {p dx dy N B : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}

def monoBudget (A : BorelDeterministicScalarPolicy p dx dy N X Y) (hNB : N ≤ B) :
    BorelDeterministicScalarPolicy p dx dy B X Y where
  policy := {
    query := A.policy.query
    output := A.policy.output
    cap := fun h hh => A.policy.cap h (hNB.trans hh)
    feasible_query := A.policy.feasible_query
    feasible_output := A.policy.feasible_output }
  measurable_query := A.measurable_query
  measurable_output := A.measurable_output

@[simp] theorem monoBudget_query (A : BorelDeterministicScalarPolicy p dx dy N X Y)
    (hNB : N ≤ B) (h : ScalarHistory p dx dy) :
    (A.monoBudget hNB).policy.query h = A.policy.query h := rfl

@[simp] theorem monoBudget_output (A : BorelDeterministicScalarPolicy p dx dy N X Y)
    (hNB : N ≤ B) (h : ScalarHistory p dx dy) :
    (A.monoBudget hNB).policy.output h = A.policy.output h := rfl

end BorelDeterministicScalarPolicy
/-- Every seed section of a jointly Borel randomized policy is a Borel
source deterministic policy, as required by the revised definition. -/
def RandomizedScalarPolicy.borelSection {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {Seed : Type*}
    [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (seed : Seed) :
    BorelDeterministicScalarPolicy p dx dy N X Y where
  policy := A.policy seed
  measurable_query := A.measurable_query.comp (measurable_const.prodMk measurable_id)
  measurable_output := A.measurable_output.comp (measurable_const.prodMk measurable_id)

/-- Exact revised randomized definition: an independent probability seed,
Borel deterministic sections, and joint Borel decision maps on all histories. -/
theorem revised_randomized_definition_source {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {Seed : Type*}
    [MeasurableSpace Seed] {mu : Measure Seed} :
    Nonempty (RandomizedScalarPolicy p dx dy N X Y Seed mu) ↔
    IsProbabilityMeasure mu ∧
    ∃ family : Seed → BorelDeterministicScalarPolicy p dx dy N X Y,
      Measurable (fun s : Seed × ScalarHistory p dx dy => (family s.1).policy.query s.2) ∧
      Measurable (fun s : Seed × ScalarHistory p dx dy => (family s.1).policy.output s.2) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.probability, A.borelSection, A.measurable_query, A.measurable_output⟩
  · rintro ⟨hmu, family, hq, ho⟩
    exact ⟨⟨hmu, fun seed => (family seed).policy, hq, ho⟩⟩

end
end MinimaxAudit
