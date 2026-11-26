import MinimaxAudit.ScalarJet
import MinimaxAudit.UpperReduction

/-!
Concrete Euclidean scalar instance, total-history capped deterministic policy,
and measurable randomized policy. Policy types contain public sets and budgets
but no unknown objective or hidden frame. Source definitions at lines220--262.
-/
open Set MeasureTheory
namespace MinimaxAudit

abbrev Primal (dx : ℕ) := EuclideanSpace ℝ (Fin dx)
abbrev Dual (dy : ℕ) := EuclideanSpace ℝ (Fin dy)
abbrev SaddleSpace (dx dy : ℕ) := EuclideanSpace ℝ (Fin dx ⊕ Fin dy)

noncomputable def joinBlocks {dx dy : ℕ} (x : Primal dx) (y : Dual dy) : SaddleSpace dx dy :=
  WithLp.toLp 2 (Sum.elim x y)

noncomputable def primalBlock {dx dy : ℕ} (z : SaddleSpace dx dy) : Primal dx :=
  WithLp.toLp 2 (fun i => z (Sum.inl i))

noncomputable def dualBlock {dx dy : ℕ} (z : SaddleSpace dx dy) : Dual dy :=
  WithLp.toLp 2 (fun i => z (Sum.inr i))

@[simp] theorem primal_join {dx dy : ℕ} (x : Primal dx) (y : Dual dy) :
    primalBlock (joinBlocks x y) = x := by ext i; rfl
@[simp] theorem dual_join {dx dy : ℕ} (x : Primal dx) (y : Dual dy) :
    dualBlock (joinBlocks x y) = y := by ext i; rfl
@[simp] theorem join_blocks {dx dy : ℕ} (z : SaddleSpace dx dy) :
    joinBlocks (primalBlock z) (dualBlock z) = z := by
  ext i
  cases i <;> rfl

def productDomain {dx dy : ℕ} (X : Set (Primal dx)) (Y : Set (Dual dy)) : Set (SaddleSpace dx dy) :=
  {z | primalBlock z ∈ X ∧ dualBlock z ∈ Y}

/-- Every clause of the source admissible class, with Euclidean L2 diameter. -/
def AdmissibleScalar {dx dy : ℕ} (p : ℕ) (L D : ℝ)
    (X : Set (Primal dx)) (Y : Set (Dual dy)) (phi : SaddleSpace dx dy → ℝ) : Prop :=
  2 ≤ p ∧ 0 < L ∧ 0 < D ∧
  X.Nonempty ∧ Y.Nonempty ∧ IsCompact X ∧ IsCompact Y ∧ Convex ℝ X ∧ Convex ℝ Y ∧
  (∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D) ∧
  (∃ O : Set (SaddleSpace dx dy), IsOpen O ∧ productDomain X Y ⊆ O ∧ ContDiffOn ℝ p phi O) ∧
  (∀ y ∈ Y, ConvexOn ℝ X (fun x => phi (joinBlocks x y))) ∧
  (∀ x ∈ X, ConcaveOn ℝ Y (fun y => phi (joinBlocks x y))) ∧
  (∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y,
    ‖iteratedFDeriv ℝ p phi z - iteratedFDeriv ℝ p phi w‖ ≤ L * ‖z - w‖) ∧
  (∃ x ∈ X, ∃ y ∈ Y, ∀ u ∈ X, ∀ v ∈ Y,
    phi (joinBlocks x v) ≤ phi (joinBlocks x y) ∧
    phi (joinBlocks x y) ≤ phi (joinBlocks u y))

/-- Expanded characterization; this does not prove a saddle-existence theorem
from compactness, since existence is explicitly included in source item(vi). -/
theorem admissible_scalar_iff {dx dy : ℕ} (p : ℕ) (L D : ℝ)
    (X : Set (Primal dx)) (Y : Set (Dual dy)) (phi : SaddleSpace dx dy → ℝ) :
    AdmissibleScalar p L D X Y phi ↔
    2 ≤ p ∧ 0 < L ∧ 0 < D ∧
    X.Nonempty ∧ Y.Nonempty ∧ IsCompact X ∧ IsCompact Y ∧ Convex ℝ X ∧ Convex ℝ Y ∧
    (∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D) ∧
    (∃ O : Set (SaddleSpace dx dy), IsOpen O ∧ productDomain X Y ⊆ O ∧ ContDiffOn ℝ p phi O) ∧
    (∀ y ∈ Y, ConvexOn ℝ X (fun x => phi (joinBlocks x y))) ∧
    (∀ x ∈ X, ConcaveOn ℝ Y (fun y => phi (joinBlocks x y))) ∧
    (∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y,
      ‖iteratedFDeriv ℝ p phi z - iteratedFDeriv ℝ p phi w‖ ≤ L * ‖z - w‖) ∧
    (∃ x ∈ X, ∃ y ∈ Y, ∀ u ∈ X, ∀ v ∈ Y,
      phi (joinBlocks x v) ≤ phi (joinBlocks x y) ∧
      phi (joinBlocks x y) ≤ phi (joinBlocks u y)) := Iff.rfl

abbrev ScalarHistory (p dx dy : ℕ) := List (SaddleSpace dx dy × ScalarJet p (SaddleSpace dx dy))

/-- The canonical Borel sigma algebra on the finite product of tensors. -/
noncomputable instance scalarJetMeasurableSpace (p dx dy : ℕ) :
    MeasurableSpace (ScalarJet p (SaddleSpace dx dy)) := borel _

noncomputable def historyEncoding {p dx dy : ℕ} (h : ScalarHistory p dx dy) :
    Σ n : ℕ, Fin n → SaddleSpace dx dy × ScalarJet p (SaddleSpace dx dy) :=
  ⟨h.length, fun i => h.get i⟩

/-- A finite history has the standard disjoint-union sigma algebra of its
fixed-length Borel sequence spaces. -/
noncomputable instance scalarHistoryMeasurableSpace (p dx dy : ℕ) :
    MeasurableSpace (ScalarHistory p dx dy) := MeasurableSpace.comap historyEncoding inferInstance

noncomputable def optionPointEncoding {dx dy : ℕ} : Option (SaddleSpace dx dy) → Unit ⊕ SaddleSpace dx dy
  | none => Sum.inl ()
  | some z => Sum.inr z

noncomputable instance optionPointMeasurableSpace (dx dy : ℕ) :
    MeasurableSpace (Option (SaddleSpace dx dy)) :=
  MeasurableSpace.comap optionPointEncoding inferInstance

/-- A total adaptive policy stops by N on every response history. Its saved
output is arbitrary and need not equal a query point. -/
structure DeterministicScalarPolicy (p dx dy N : ℕ)
    (X : Set (Primal dx)) (Y : Set (Dual dy)) where
  query : ScalarHistory p dx dy → Option (SaddleSpace dx dy)
  output : ScalarHistory p dx dy → SaddleSpace dx dy
  cap : ∀ h, N ≤ h.length → query h = none
  feasible_query : ∀ h z, query h = some z → z ∈ productDomain X Y
  feasible_output : ∀ h, output h ∈ productDomain X Y

theorem deterministic_policy_expanded {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (A : DeterministicScalarPolicy p dx dy N X Y) :
    (∀ h, N ≤ h.length → A.query h = none) ∧
    (∀ h z, A.query h = some z → z ∈ productDomain X Y) ∧
    (∀ h, A.output h ∈ productDomain X Y) :=
  ⟨A.cap, A.feasible_query, A.feasible_output⟩

/-- Randomness is an independent seed; objective/frame are absent from the
policy's input type. Joint measurability on all histories makes truncated
transcript simulation meaningful, as required by the source convention. -/
structure RandomizedScalarPolicy (p dx dy N : ℕ)
    (X : Set (Primal dx)) (Y : Set (Dual dy))
    (Seed : Type*) [MeasurableSpace Seed]
    (mu : Measure Seed) where
  probability : IsProbabilityMeasure mu
  policy : Seed → DeterministicScalarPolicy p dx dy N X Y
  measurable_query : Measurable (fun s : Seed × ScalarHistory p dx dy => (policy s.1).query s.2)
  measurable_output : Measurable (fun s : Seed × ScalarHistory p dx dy => (policy s.1).output s.2)

theorem randomized_policy_expanded {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {Seed : Type*} [MeasurableSpace Seed]
    {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) :
    IsProbabilityMeasure mu ∧
    Measurable (fun s : Seed × ScalarHistory p dx dy => (A.policy s.1).query s.2) ∧
    Measurable (fun s : Seed × ScalarHistory p dx dy => (A.policy s.1).output s.2) ∧
    (∀ seed h, N ≤ h.length → (A.policy seed).query h = none) ∧
    (∀ seed h, (A.policy seed).output h ∈ productDomain X Y) :=
  ⟨A.probability, A.measurable_query, A.measurable_output,
    fun seed => (A.policy seed).cap, fun seed => (A.policy seed).feasible_output⟩

end MinimaxAudit

namespace MinimaxAudit
open Set MeasureTheory

/-- No update-rule restriction is hidden in the policy structure: every total
capped feasible query/output pair constructs a policy, and conversely. -/
theorem deterministic_policy_iff {p dx dy N : ℕ}
    (X : Set (Primal dx)) (Y : Set (Dual dy)) :
    Nonempty (DeterministicScalarPolicy p dx dy N X Y) ↔
    ∃ query : ScalarHistory p dx dy → Option (SaddleSpace dx dy),
    ∃ output : ScalarHistory p dx dy → SaddleSpace dx dy,
      (∀ h, N ≤ h.length → query h = none) ∧
      (∀ h z, query h = some z → z ∈ productDomain X Y) ∧
      (∀ h, output h ∈ productDomain X Y) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.query, A.output, A.cap, A.feasible_query, A.feasible_output⟩
  · rintro ⟨query, output, cap, hq, ho⟩
    exact ⟨⟨query, output, cap, hq, ho⟩⟩

/-- The randomized definition is exactly a measurable family of the complete
deterministic policies over one probability seed space. -/
theorem randomized_policy_iff {p dx dy N : ℕ}
    (X : Set (Primal dx)) (Y : Set (Dual dy))
    (Seed : Type*) [MeasurableSpace Seed] (mu : Measure Seed) :
    Nonempty (RandomizedScalarPolicy p dx dy N X Y Seed mu) ↔
    IsProbabilityMeasure mu ∧
    ∃ policy : Seed → DeterministicScalarPolicy p dx dy N X Y,
      Measurable (fun s : Seed × ScalarHistory p dx dy => (policy s.1).query s.2) ∧
      Measurable (fun s : Seed × ScalarHistory p dx dy => (policy s.1).output s.2) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.probability, A.policy, A.measurable_query, A.measurable_output⟩
  · rintro ⟨hmu, policy, hq, ho⟩
    exact ⟨⟨hmu, policy, hq, ho⟩⟩

end MinimaxAudit

namespace MinimaxAudit
open MeasureTheory
open scoped ENNReal

/-- A lower-bound witness is chosen outside the event over the realized seed.
This definition records the quantifier constraint in definition-L251; it does
not claim such a witness exists for every policy. -/
def FixedInstanceObstruction {Seed Instance : Type*} [MeasurableSpace Seed]
    (mu : Measure Seed) (failure : Instance → Seed → Prop) (threshold : ℝ≥0∞) : Prop :=
  ∃ omega, threshold ≤ mu {seed | failure omega seed}

/-- Complete random-model paragraph: the measurable algorithm-object
characterization and the independently fixed-instance witness constraint. -/
theorem randomized_definition_source {p dx dy N : ℕ}
    (X : Set (Primal dx)) (Y : Set (Dual dy))
    (Seed : Type*) [MeasurableSpace Seed] (mu : Measure Seed) :
    (Nonempty (RandomizedScalarPolicy p dx dy N X Y Seed mu) ↔
      IsProbabilityMeasure mu ∧
      ∃ policy : Seed → DeterministicScalarPolicy p dx dy N X Y,
        Measurable (fun s : Seed × ScalarHistory p dx dy => (policy s.1).query s.2) ∧
        Measurable (fun s : Seed × ScalarHistory p dx dy => (policy s.1).output s.2)) ∧
    (∀ (Instance : Type*) (failure : Instance → Seed → Prop) (threshold : ℝ≥0∞),
      FixedInstanceObstruction mu failure threshold ↔
        ∃ omega, threshold ≤ mu {seed | failure omega seed}) := by
  exact ⟨randomized_policy_iff X Y Seed mu, fun _ _ _ => Iff.rfl⟩

end MinimaxAudit
