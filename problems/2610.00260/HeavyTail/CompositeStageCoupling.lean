import HeavyTail.RejectionDistributionCoupling
import HeavyTail.CompositeStagePolicy

/-! Manuscript ideal/capped coupling specialized to the actual composite
stage oracle and public learner. Acceptance positivity and the raw rejection
tail are discharged from the private-instance contract. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
namespace HeavyTail.PrivateInstance
universe u
variable {E W : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace W]
  {θ : OracleParameters} {B : PublicProblem E θ}

theorem stageRule_acceptance_pos (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R)
    (s : CompositeStageState W E) :
    I.oracle ((B.stageRule hR hn τ L).query s)
      (Prod.mk s ⁻¹' (B.stageRule hR hn τ L).acceptance) ≠ 0 := by
  change I.stageRawKernel hR hn (L.point s.1)
    (Prod.mk (L.point s.1) ⁻¹' B.stageAcceptance hR hn τ) ≠ 0
  exact I.stageAcceptance_pos hR hn hτ _ (I.stageLearner_point_distance L hc s.1)

def idealStageLaw (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R) (P : Measure PUnit) :
    Measure B.X :=
  (B.stageRule hR hn τ L).idealOutputLaw I.oracle (I.stageRule_acceptance_pos hR hn hτ L hc)
    (initial := PublicProblem.stageInitial L) measurable_const n P

def stageIdealCappedCoupling (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R) (P : Measure PUnit) :
    Measure (B.X × B.X) :=
  (B.stageRule hR hn τ L).cappedIdealCoupling I.oracle (I.stageRule_acceptance_pos hR hn hτ L hc)
    (initial := PublicProblem.stageInitial L) measurable_const n (4 * n) P

instance stageIdealCappedCoupling_probability (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R) (P : Measure PUnit)
    [IsProbabilityMeasure P] : IsProbabilityMeasure (I.stageIdealCappedCoupling hR hn hτ L hc P) := by
  unfold stageIdealCappedCoupling
  infer_instance

theorem stageIdeal_acceptedReply (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R) (s : CompositeStageState W E) :
    (B.stageRule hR hn τ L).idealAcceptedReply I.oracle
      (I.stageRule_acceptance_pos hR hn hτ L hc) s = I.acceptedRawLaw hR hn τ (L.point s.1) := by
  rw [CappedRaw.Rule.idealAcceptedReply_eq_cond]
  rfl

theorem stageIdealCappedCoupling_marginals (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R) (P : Measure PUnit)
    [IsProbabilityMeasure P] :
    (I.stageIdealCappedCoupling hR hn hτ L hc P).fst =
      (B.cappedStagePolicy hR hn τ L (4 * n)).outputLaw P I.oracle ∧
    (I.stageIdealCappedCoupling hR hn hτ L hc P).snd = I.idealStageLaw hR hn hτ L hc P := by
  exact ⟨(B.stageRule hR hn τ L).cappedIdealCoupling_fst I.oracle _ measurable_const n (4 * n) P,
    (B.stageRule hR hn τ L).cappedIdealCoupling_snd I.oracle _ measurable_const n (4 * n) P⟩

private theorem feasible_disagreement_measurable : MeasurableSet {z : B.X × B.X | z.1 ≠ z.2} := by
  have h := (measurableSet_eq_fun
    (measurable_subtype_coe.comp (measurable_fst : Measurable (Prod.fst : B.X × B.X → B.X)))
    (measurable_subtype_coe.comp (measurable_snd : Measurable (Prod.snd : B.X × B.X → B.X)))).compl
  convert h using 1
  ext z
  change (z.1 ≠ z.2) ↔ ((z.1 : E) ≠ (z.2 : E))
  exact not_congr Subtype.ext_iff

theorem stageIdealCappedCoupling_disagreement (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R) (P : Measure PUnit)
    [IsProbabilityMeasure P] :
    (I.stageIdealCappedCoupling hR hn hτ L hc P).real {z | z.1 ≠ z.2} ≤
      ((2 : ℝ) ^ (8 * n))⁻¹ :=
  (B.stageRule hR hn τ L).cappedIdealCoupling_disagreement_probability I.oracle
    (I.stageRule_acceptance_pos hR hn hτ L hc) measurable_const n P
    feasible_disagreement_measurable (I.cappedStage_rejection_bound hR hn hτ L hc)

theorem cappedStage_failure_le_ideal (I : PrivateInstance B) {c : E} {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (L : StageLearner W E c R) (hc : ‖c - I.minimizer‖ ≤ R) (P : Measure PUnit)
    [IsProbabilityMeasure P] {S : Set B.X} (hS : MeasurableSet S) :
    ((B.cappedStagePolicy hR hn τ L (4 * n)).outputLaw P I.oracle).real S ≤
      (I.idealStageLaw hR hn hτ L hc P).real S + ((2 : ℝ) ^ (8 * n))⁻¹ :=
  (B.stageRule hR hn τ L).capped_failure_le_ideal_plus_tail I.oracle
    (I.stageRule_acceptance_pos hR hn hτ L hc) measurable_const n P
    feasible_disagreement_measurable (I.cappedStage_rejection_bound hR hn hτ L hc) hS

end HeavyTail.PrivateInstance
