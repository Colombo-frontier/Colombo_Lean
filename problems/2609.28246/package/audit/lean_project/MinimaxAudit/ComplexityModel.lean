import MinimaxAudit.RevisedModel
import MinimaxAudit.Deterministic
import MinimaxAudit.CriterionFull
import Mathlib.Data.Real.ENatENNReal

/-!
# Global oracle complexity for the revised measurable policy model

A successful budget is uniform over all finite dimensions and all public
compact convex product domains. Its policy is chosen from public data before
the unknown scalar objective. Complexity is the infimum of these budgets in
extended naturals; an empty set of successful budgets has value infinity.
-/
open Set MeasureTheory
open scoped ENNReal
namespace MinimaxAudit
noncomputable section
universe u

inductive OracleErrorCriterion where
  | tangent
  | gap
  deriving DecidableEq, Fintype

/-- The actual two source error criteria, evaluated at the saved output. -/
def criterionValue {dx dy : ℕ} (E : OracleErrorCriterion)
    (X : Set (Primal dx)) (Y : Set (Dual dy)) (phi : SaddleSpace dx dy → ℝ)
    (z : SaddleSpace dx dy) : ℝ :=
  match E with
  | .tangent => auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) z
  | .gap => auditedSaddleGap X Y (fun x y => phi (joinBlocks x y)) (primalBlock z) (dualBlock z)

/-- The criterion-dependent dimensionless accuracy ratio in the source. -/
def criterionRatio (E : OracleErrorCriterion) (p : ℕ) (L D eps : ℝ) : ℝ :=
  match E with
  | .tangent => L * D ^ p / eps
  | .gap => L * D ^ (p + 1) / eps

/-- Only public data. In particular no unknown objective or frame occurs in
this structure, and a policy must be chosen before the objective quantifier. -/
structure PublicProductDomain (p : ℕ) (L D : ℝ) {dx dy : ℕ}
    (X : Set (Primal dx)) (Y : Set (Dual dy)) : Prop where
  order_ge_two : 2 ≤ p
  lipschitz_pos : 0 < L
  diameter_pos : 0 < D
  primal_nonempty : X.Nonempty
  dual_nonempty : Y.Nonempty
  primal_compact : IsCompact X
  dual_compact : IsCompact Y
  primal_convex : Convex ℝ X
  dual_convex : Convex ℝ Y
  diameter_bound : ∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D

theorem publicProductDomain_of_admissible {p dx dy : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {phi : SaddleSpace dx dy → ℝ}
    (h : AdmissibleScalar p L D X Y phi) : PublicProductDomain p L D X Y := by
  rcases h with ⟨hp,hL,hD,hX,hY,hcX,hcY,hvX,hvY,hdiam,_⟩
  exact ⟨hp,hL,hD,hX,hY,hcX,hcY,hvX,hvY,hdiam⟩

/-- A deterministic solver has one Borel policy for each public domain,
working for every admissible unknown objective with the same budget. -/
def DetSuccessfulBudget (E : OracleErrorCriterion) (p : ℕ) (L D eps : ℝ) (B : ℕ) : Prop :=
  ∀ (dx dy : ℕ) (X : Set (Primal dx)) (Y : Set (Dual dy)),
    PublicProductDomain p L D X Y →
    ∃ A : BorelDeterministicScalarPolicy p dx dy B X Y,
      ∀ phi : SaddleSpace dx dy → ℝ, AdmissibleScalar p L D X Y phi →
        criterionValue E X Y phi
          (Deterministic.runScalarPolicy A.policy (exactScalarJet p phi) B []) ≤ eps

/-- Randomized success on one public domain, with the objective after the
seed law and entire policy. The seed is not resampled after seeing phi. -/
def RandomSolvesPublicDomain {p dx dy B : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (E : OracleErrorCriterion) (L D eps : ℝ)
    (Seed : Type u) [MeasurableSpace Seed] (mu : Measure Seed)
    (A : RandomizedScalarPolicy p dx dy B X Y Seed mu) : Prop :=
  ∀ phi : SaddleSpace dx dy → ℝ, AdmissibleScalar p L D X Y phi →
    (2 / 3 : ℝ≥0∞) ≤ mu {seed |
      criterionValue E X Y phi
        (Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) B []) ≤ eps}

/-- Universe-polymorphic global randomized budget. Explicit measurable-space
binders avoid assuming a distinguished seed law; the policy and its law are
chosen using public data, before the unknown objective. -/
def RandSuccessfulBudget (E : OracleErrorCriterion) (p : ℕ) (L D eps : ℝ) (B : ℕ) : Prop :=
  ∀ (dx dy : ℕ) (X : Set (Primal dx)) (Y : Set (Dual dy)),
    PublicProductDomain p L D X Y →
    ∃ (Seed : Type u) (mSeed : MeasurableSpace Seed) (mu : @Measure Seed mSeed)
      (A : @RandomizedScalarPolicy p dx dy B X Y Seed mSeed mu),
      @RandomSolvesPublicDomain p dx dy B X Y E L D eps Seed mSeed mu A

/-- Extended-natural complexity: infinity if no finite budget succeeds. -/
def detOracleComplexity (E : OracleErrorCriterion) (p : ℕ) (L D eps : ℝ) : ℕ∞ :=
  ⨅ B : {B : ℕ // DetSuccessfulBudget E p L D eps B}, (B.1 : ℕ∞)

/-- Extended-natural random complexity, for arbitrary seed universe u. -/
def randOracleComplexity (E : OracleErrorCriterion) (p : ℕ) (L D eps : ℝ) : ℕ∞ :=
  ⨅ B : {B : ℕ // RandSuccessfulBudget.{u} E p L D eps B}, (B.1 : ℕ∞)

/-- A genuine one-point independent seed lift, requiring the revised Borel
deterministic model rather than silently assuming arbitrary history maps
are Borel. -/
def BorelDeterministicScalarPolicy.toRandomizedUnit {p dx dy B : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (A : BorelDeterministicScalarPolicy p dx dy B X Y) :
    RandomizedScalarPolicy p dx dy B X Y (ULift.{u} Unit) (Measure.dirac (ULift.up ())) where
  probability := inferInstance
  policy := fun _ => A.policy
  measurable_query := A.measurable_query.comp measurable_snd
  measurable_output := A.measurable_output.comp measurable_snd

/-- The revised deterministic policy class really embeds into the random
class on each public domain, with exactly the same original oracle budget. -/
theorem detSuccessfulBudget_implies_rand {E : OracleErrorCriterion} {p B : ℕ}
    {L D eps : ℝ} (h : DetSuccessfulBudget E p L D eps B) :
    RandSuccessfulBudget.{u} E p L D eps B := by
  intro dx dy X Y hpub
  obtain ⟨A,hA⟩ := h dx dy X Y hpub
  let Aseed : RandomizedScalarPolicy p dx dy B X Y (ULift.{u} Unit)
      (Measure.dirac (ULift.up ())) := A.toRandomizedUnit
  refine ⟨ULift.{u} Unit, inferInstance, Measure.dirac (ULift.up ()), Aseed, ?_⟩
  intro phi hphi
  have hall : {seed : ULift.{u} Unit |
      criterionValue E X Y phi
        (Deterministic.runScalarPolicy (Aseed.policy seed) (exactScalarJet p phi) B []) ≤ eps} = Set.univ := by
    ext seed
    exact iff_true_intro (hA phi hphi)
  rw [hall]
  exact (ENNReal.div_le_iff (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num)).mpr (by norm_num)

/-- Any certified finite successful budget bounds the infimum. -/
theorem detOracleComplexity_le_budget {E : OracleErrorCriterion} {p B : ℕ}
    {L D eps : ℝ} (h : DetSuccessfulBudget E p L D eps B) :
    detOracleComplexity E p L D eps ≤ (B : ℕ∞) := by
  unfold detOracleComplexity
  exact iInf_le (fun b : {b : ℕ // DetSuccessfulBudget E p L D eps b} => (b.1 : ℕ∞)) ⟨B,h⟩

theorem randOracleComplexity_le_budget {E : OracleErrorCriterion} {p B : ℕ}
    {L D eps : ℝ} (h : RandSuccessfulBudget.{u} E p L D eps B) :
    randOracleComplexity.{u} E p L D eps ≤ (B : ℕ∞) := by
  unfold randOracleComplexity
  exact iInf_le (fun b : {b : ℕ // RandSuccessfulBudget.{u} E p L D eps b} => (b.1 : ℕ∞)) ⟨B,h⟩

/-- The middle comparison in the revised source is now an actual theorem
of the global budget model, including the infinity cases. -/
theorem randOracleComplexity_le_det (E : OracleErrorCriterion) (p : ℕ) (L D eps : ℝ) :
    randOracleComplexity.{u} E p L D eps ≤ detOracleComplexity E p L D eps := by
  apply le_iInf
  intro B
  exact randOracleComplexity_le_budget (detSuccessfulBudget_implies_rand B.2)

/-- If there is no successful finite budget, the infimum is infinity. -/
theorem detOracleComplexity_eq_top_iff (E : OracleErrorCriterion) (p : ℕ) (L D eps : ℝ) :
    detOracleComplexity E p L D eps = ⊤ ↔ ¬ ∃ B, DetSuccessfulBudget E p L D eps B := by
  rw [detOracleComplexity, ENat.iInf_coe_eq_top]
  constructor
  · intro hnone hex
    obtain ⟨B,hB⟩ := hex
    exact hnone.false ⟨B,hB⟩
  · intro hnone
    exact ⟨fun B => hnone ⟨B.1,B.2⟩⟩

theorem randOracleComplexity_eq_top_iff (E : OracleErrorCriterion) (p : ℕ) (L D eps : ℝ) :
    randOracleComplexity.{u} E p L D eps = ⊤ ↔ ¬ ∃ B, RandSuccessfulBudget.{u} E p L D eps B := by
  rw [randOracleComplexity, ENat.iInf_coe_eq_top]
  constructor
  · intro hnone hex
    obtain ⟨B,hB⟩ := hex
    exact hnone.false ⟨B,hB⟩
  · intro hnone
    exact ⟨fun B => hnone ⟨B.1,B.2⟩⟩

/-- Generic lower-budget transfer to the infimum; no existence of a solver
or finite complexity is needed. -/
theorem detOracleComplexity_lower_of_budget_bound {E : OracleErrorCriterion} {p : ℕ}
    {L D eps : ℝ} {k : ℕ∞}
    (h : ∀ B, DetSuccessfulBudget E p L D eps B → k ≤ (B : ℕ∞)) :
    k ≤ detOracleComplexity E p L D eps := by
  apply le_iInf
  intro B
  exact h B.1 B.2

theorem randOracleComplexity_lower_of_budget_bound {E : OracleErrorCriterion} {p : ℕ}
    {L D eps : ℝ} {k : ℕ∞}
    (h : ∀ B, RandSuccessfulBudget.{u} E p L D eps B → k ≤ (B : ℕ∞)) :
    k ≤ randOracleComplexity.{u} E p L D eps := by
  apply le_iInf
  intro B
  exact h B.1 B.2

/-- Real lower estimates on every successful budget transfer to the genuine
extended-natural infimum, including the case of no finite successful budget. -/
theorem randOracleComplexity_real_lower_of_budget_bound
    {E : OracleErrorCriterion} {p : ℕ} {L D eps r : ℝ}
    (h : ∀ B, RandSuccessfulBudget.{u} E p L D eps B → r ≤ (B : ℝ)) :
    ENNReal.ofReal r ≤ (randOracleComplexity.{u} E p L D eps : ℝ≥0∞) := by
  have hceil : ((Nat.ceil r : ℕ) : ℕ∞) ≤ randOracleComplexity.{u} E p L D eps := by
    apply randOracleComplexity_lower_of_budget_bound
    intro B hB
    exact ENat.coe_le_coe.mpr (Nat.ceil_le.mpr (h B hB))
  have hr : ENNReal.ofReal r ≤ (((Nat.ceil r : ℕ) : ℕ∞) : ℝ≥0∞) := by
    simpa only [ENat.toENNReal_coe, ENNReal.ofReal_natCast] using
      (ENNReal.ofReal_le_ofReal (Nat.le_ceil r))
  exact hr.trans (ENat.toENNReal_mono hceil)

theorem detOracleComplexity_real_lower_of_budget_bound
    {E : OracleErrorCriterion} {p : ℕ} {L D eps r : ℝ}
    (h : ∀ B, DetSuccessfulBudget E p L D eps B → r ≤ (B : ℝ)) :
    ENNReal.ofReal r ≤ (detOracleComplexity E p L D eps : ℝ≥0∞) := by
  have hceil : ((Nat.ceil r : ℕ) : ℕ∞) ≤ detOracleComplexity E p L D eps := by
    apply detOracleComplexity_lower_of_budget_bound
    intro B hB
    exact ENat.coe_le_coe.mpr (Nat.ceil_le.mpr (h B hB))
  have hr : ENNReal.ofReal r ≤ (((Nat.ceil r : ℕ) : ℕ∞) : ℝ≥0∞) := by
    simpa only [ENat.toENNReal_coe, ENNReal.ofReal_natCast] using
      (ENNReal.ofReal_le_ofReal (Nat.le_ceil r))
  exact hr.trans (ENat.toENNReal_mono hceil)

end
end MinimaxAudit
