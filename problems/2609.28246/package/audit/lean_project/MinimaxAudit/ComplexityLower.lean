import MinimaxAudit.ComplexityModel
import MinimaxAudit.MainLower
import MinimaxAudit.ComplexityArithmetic

/-!
# Actual minimax obstructions imply global oracle complexity lower bounds

The successful-budget predicates quantify over all public domains before
choosing the unknown objective. They are instantiated here on the concrete
hard balls, and the proved scalar lower bounds rule out every insufficient
budget, including budget zero. No obstruction is postulated as a solver field.
-/
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace MinimaxAudit
noncomputable section
universe u
set_option maxHeartbeats 1500000

/-- Source rate constant for the requested actual error criterion. -/
def criterionRateConstant (E : OracleErrorCriterion) (p : ℕ) : ℝ :=
  match E with
  | .tangent => tangentRateConstant standardGateProfile p
  | .gap => gapRateConstant standardGateProfile p

def criterionNumerator (E : OracleErrorCriterion) (p : ℕ) (L D : ℝ) : ℝ :=
  match E with
  | .tangent => L * D ^ p
  | .gap => L * D ^ (p + 1)

theorem criterionRateConstant_pos (E : OracleErrorCriterion) (p : ℕ) :
    0 < criterionRateConstant E p := by
  cases E
  · exact tangentRateConstant_pos standardGateProfile p
  · exact gapRateConstant_pos standardGateProfile p

theorem criterionRatio_pos (E : OracleErrorCriterion) (p : ℕ)
    {L D eps : ℝ} (hL : 0 < L) (hD : 0 < D) (heps : 0 < eps) :
    0 < criterionRatio E p L D eps := by
  cases E <;> simp only [criterionRatio] <;> positivity

theorem oracleRateExponent_pos {p : ℕ} (hp : 2 ≤ p) : 0 < oracleRateExponent p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold oracleRateExponent
  linarith

theorem inverse_oracleRateExponent {p : ℕ} (hp : 2 ≤ p) :
    1 / oracleRateExponent p = 2 / (3 * (p : ℝ) - 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : 3 * (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  unfold oracleRateExponent
  field_simp [hden]

/-- These are public domains in all finite dimensions, independently of any
hidden frame or unknown scalar objective. -/
theorem publicProductDomain_hardBalls {p dx dy : ℕ} (hp : 2 ≤ p)
    {L D : ℝ} (hL : 0 < L) (hD : 0 < D) :
    PublicProductDomain p L D
      (Metric.closedBall (0 : Primal dx) (publicHardRadius D))
      (Metric.closedBall (0 : Dual dy) (publicHardRadius D)) := by
  let R := publicHardRadius D
  have hR : 0 < R := by dsimp [R, publicHardRadius]; positivity
  refine ⟨hp,hL,hD,⟨0, by simpa using hR.le⟩,⟨0, by simpa using hR.le⟩,
    isCompact_closedBall _ _,isCompact_closedBall _ _,convex_closedBall _ _,convex_closedBall _ _,?_⟩
  intro z hz w hw
  have hscale : 2 * Real.sqrt 2 * R = D := by
    dsimp [R, publicHardRadius]
    field_simp
  simpa only [hscale] using productBall_diameter_bound hR.le hz hw

/-- A successful deterministic budget must exceed the actual hard error
scale, on the same fixed scalar potential and saved arbitrary output. -/
theorem det_successful_budget_physical_constraint
    {E : OracleErrorCriterion} {p B : ℕ} (hp : 2 ≤ p)
    {L D eps : ℝ} (hL : 0 < L) (hD : 0 < D)
    (hbudget : DetSuccessfulBudget E p L D eps B) :
    criterionRateConstant E p * criterionNumerator E p L D /
      (B + 1 : ℝ) ^ oracleRateExponent p ≤ eps := by
  obtain ⟨A,hA⟩ := hbudget (2*B+2) (2*B+2)
    (Metric.closedBall 0 (publicHardRadius D)) (Metric.closedBall 0 (publicHardRadius D))
    (publicProductDomain_hardBalls hp hL hD)
  obtain ⟨phi,hadm,hdiam,htan,hgap⟩ := deterministic_lower_standard hp hL hD A.policy
  have hs := hA phi hadm
  cases E
  · have ht := htan.trans hs
    simpa only [criterionRateConstant,criterionNumerator,mul_assoc] using ht
  · have hg := hgap.trans hs
    simpa only [criterionRateConstant,criterionNumerator,mul_assoc] using hg

/-- Probabilistic incompatibility, using a genuinely measurable bad event.
No measurability of a favorable outer-measure event is used in its place. -/
theorem success_and_failure_incompatible
    {Seed : Type u} [MeasurableSpace Seed] (mu : Measure Seed) [IsProbabilityMeasure mu]
    (S J : Set Seed) (hJ : MeasurableSet J) (hdisj : S ⊆ Jᶜ)
    (hS : (2/3 : ℝ≥0∞) ≤ mu S) (hbad : (3/4 : ℝ≥0∞) ≤ mu J) : False := by
  have hupper : mu S ≤ 1 - mu J := by
    calc
      mu S ≤ mu Jᶜ := measure_mono hdisj
      _ = 1 - mu J := by rw [measure_compl hJ (measure_ne_top _ _)]; simp
  have hnum : (2/3 : ℝ≥0∞) ≤ 1 - (3/4 : ℝ≥0∞) :=
    hS.trans (hupper.trans (tsub_le_tsub_left hbad 1))
  have h34 : (3/4 : ℝ≥0∞) ≤ 1 :=
    (ENNReal.div_le_iff (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)).mpr (by norm_num)
  have hfinite : (1 - (3/4 : ℝ≥0∞)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) tsub_le_self
  have hreal := ENNReal.toReal_mono hfinite hnum
  rw [ENNReal.toReal_sub_of_le h34 (by norm_num)] at hreal
  norm_num at hreal

/-- Instantiate the actual fixed-frame scalar random lower bound on a public
hard domain. The chosen frame precedes the realized seed and gives a genuine
measurable joint bad event, so 2/3 success cannot coexist with a larger error
threshold. This theorem covers every finite budget B, including zero. -/
theorem rand_successful_budget_physical_constraint
    {E : OracleErrorCriterion} {p B : ℕ} (hp : 2 ≤ p)
    {L D eps : ℝ} (hL : 0 < L) (hD : 0 < D)
    (hbudget : RandSuccessfulBudget.{u} E p L D eps B) :
    criterionRateConstant E p * criterionNumerator E p L D /
      (B + 1 : ℝ) ^ oracleRateExponent p ≤ eps := by
  let d := randomHardDimension B
  let R := publicHardRadius D
  have hR : 0 < R := by dsimp [R, publicHardRadius]; positivity
  obtain ⟨Seed,mSeed,mu,A,hA⟩ := hbudget d d
    (Metric.closedBall 0 R) (Metric.closedBall 0 R)
    (publicProductDomain_hardBalls hp hL hD)
  letI : MeasurableSpace Seed := mSeed
  letI : IsProbabilityMeasure mu := A.probability
  obtain ⟨U,V,hU,hV,hadm,hdiam,hdim,hprob⟩ := randomized_scalar_lower_bound hp hL hD A
  let phi := minimaxHardPotential standardGateProfile (hardGateWidth B R)
    (hardAmplitude standardGateProfile p B L R) (balancedQ B) (hardSeed B R) hU hV
  have hreg : ContDiff ℝ ∞ phi := (hardInstance_global standardGateProfile hp hL hR hU hV).1
  let output := fun seed => Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) B []
  let J : Set Seed := {seed |
    tangentRateConstant standardGateProfile p * L * D ^ p / (B+1 : ℝ) ^ oracleRateExponent p ≤
      criterionValue .tangent (Metric.closedBall 0 R) (Metric.closedBall 0 R) phi (output seed) ∧
    gapRateConstant standardGateProfile p * L * D ^ (p+1) / (B+1 : ℝ) ^ oracleRateExponent p ≤
      criterionValue .gap (Metric.closedBall 0 R) (Metric.closedBall 0 R) phi (output seed)}
  let S : Set Seed := {seed |
    criterionValue E (Metric.closedBall 0 R) (Metric.closedBall 0 R) phi (output seed) ≤ eps}
  have hprobJ : (3/4 : ℝ≥0∞) ≤ mu J := hprob
  have hprobS : (2/3 : ℝ≥0∞) ≤ mu S := hA phi hadm
  let fill : productDomain (Metric.closedBall (0 : Primal d) R) (Metric.closedBall (0 : Dual d) R) :=
    ⟨0, source_inner_zero_feasible hR.le (by simp; positivity)⟩
  have hJ : MeasurableSet J := source_joint_error_event_measurable A fill
    (isCompact_closedBall 0 R) (isCompact_closedBall 0 R)
    ⟨0, by simpa using hR.le⟩ ⟨0, by simpa using hR.le⟩ hreg _ _
  by_contra hthreshold
  have ht : eps < criterionRateConstant E p * criterionNumerator E p L D /
      (B + 1 : ℝ) ^ oracleRateExponent p := lt_of_not_ge hthreshold
  apply success_and_failure_incompatible mu S J hJ ?_ hprobS hprobJ
  intro seed hseed hj
  have hbad : criterionRateConstant E p * criterionNumerator E p L D /
      (B + 1 : ℝ) ^ oracleRateExponent p ≤
      criterionValue E (Metric.closedBall 0 R) (Metric.closedBall 0 R) phi (output seed) := by
    cases E
    · simpa only [criterionRateConstant,criterionNumerator,mul_assoc] using hj.1
    · simpa only [criterionRateConstant,criterionNumerator,mul_assoc] using hj.2
  exact (not_le_of_gt ht) (hbad.trans hseed)

/-- Normalize the actual error scale into the source accuracy ratio. -/
theorem normalize_criterion_rate {E : OracleErrorCriterion} {p B : ℕ}
    {L D eps : ℝ} (heps : 0 < eps)
    (h : criterionRateConstant E p * criterionNumerator E p L D /
      (B + 1 : ℝ) ^ oracleRateExponent p ≤ eps) :
    criterionRateConstant E p * criterionRatio E p L D eps /
      (B + 1 : ℝ) ^ oracleRateExponent p ≤ 1 := by
  have hid : criterionRateConstant E p * criterionRatio E p L D eps /
      (B + 1 : ℝ) ^ oracleRateExponent p =
      (criterionRateConstant E p * criterionNumerator E p L D /
        (B + 1 : ℝ) ^ oracleRateExponent p) / eps := by
    cases E <;> simp only [criterionRatio,criterionNumerator] <;> ring
  rw [hid, div_le_iff₀ heps]
  simpa using h

theorem det_successful_budget_rate_constraint
    {E : OracleErrorCriterion} {p B : ℕ} (hp : 2 ≤ p)
    {L D eps : ℝ} (hL : 0 < L) (hD : 0 < D) (heps : 0 < eps)
    (hbudget : DetSuccessfulBudget E p L D eps B) :
    criterionRateConstant E p * criterionRatio E p L D eps /
      (B + 1 : ℝ) ^ oracleRateExponent p ≤ 1 :=
  normalize_criterion_rate heps (det_successful_budget_physical_constraint hp hL hD hbudget)

theorem rand_successful_budget_rate_constraint
    {E : OracleErrorCriterion} {p B : ℕ} (hp : 2 ≤ p)
    {L D eps : ℝ} (hL : 0 < L) (hD : 0 < D) (heps : 0 < eps)
    (hbudget : RandSuccessfulBudget.{u} E p L D eps B) :
    criterionRateConstant E p * criterionRatio E p L D eps /
      (B + 1 : ℝ) ^ oracleRateExponent p ≤ 1 :=
  normalize_criterion_rate heps (rand_successful_budget_physical_constraint hp hL hD hbudget)

/-- Natural-budget lower bound with its explicit large-ratio threshold. -/
theorem rand_successful_budget_asymptotic
    {E : OracleErrorCriterion} {p B : ℕ} (hp : 2 ≤ p)
    {L D eps : ℝ} (hL : 0 < L) (hD : 0 < D) (heps : 0 < eps)
    (hQ : (2 : ℝ) ^ oracleRateExponent p / criterionRateConstant E p ≤
      criterionRatio E p L D eps)
    (hbudget : RandSuccessfulBudget.{u} E p L D eps B) :
    (criterionRateConstant E p) ^ (1 / oracleRateExponent p) / 2 *
      (criterionRatio E p L D eps) ^ (1 / oracleRateExponent p) ≤ (B : ℝ) :=
  rate_budget_asymptotic (oracleRateExponent_pos hp) (criterionRateConstant_pos E p)
    (Nat.cast_nonneg B) hQ (rand_successful_budget_rate_constraint hp hL hD heps hbudget)

/-- The two criteria share one positive p-only lower constant and threshold. -/
def complexityLowerConstant (p : ℕ) : ℝ :=
  min ((criterionRateConstant .tangent p) ^ (1 / oracleRateExponent p) / 2)
    ((criterionRateConstant .gap p) ^ (1 / oracleRateExponent p) / 2)

def complexityLowerThreshold (p : ℕ) : ℝ :=
  max ((2 : ℝ) ^ oracleRateExponent p / criterionRateConstant .tangent p)
    ((2 : ℝ) ^ oracleRateExponent p / criterionRateConstant .gap p)

theorem complexityLowerConstant_pos (p : ℕ) : 0 < complexityLowerConstant p := by
  apply lt_min
  · exact div_pos (Real.rpow_pos_of_pos (criterionRateConstant_pos .tangent p) _) (by norm_num)
  · exact div_pos (Real.rpow_pos_of_pos (criterionRateConstant_pos .gap p) _) (by norm_num)

theorem complexityLowerThreshold_pos (p : ℕ) : 0 < complexityLowerThreshold p := by
  exact (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (criterionRateConstant_pos .tangent p)).trans_le
    (le_max_left _ _)

/-- Actual global random complexity lower bound, not an abstract inverse-rate
contract. The extended-natural infimum handles absent/finite solvers alike. -/
theorem randOracleComplexity_lower
    (E : OracleErrorCriterion) {p : ℕ} (hp : 2 ≤ p)
    {L D eps : ℝ} (hL : 0 < L) (hD : 0 < D) (heps : 0 < eps)
    (hQ : complexityLowerThreshold p ≤ criterionRatio E p L D eps) :
    ENNReal.ofReal (complexityLowerConstant p *
      (criterionRatio E p L D eps) ^ (2 / (3 * (p : ℝ) - 1))) ≤
      (randOracleComplexity.{u} E p L D eps : ℝ≥0∞) := by
  apply randOracleComplexity_real_lower_of_budget_bound
  intro B hB
  have hthr : (2 : ℝ) ^ oracleRateExponent p / criterionRateConstant E p ≤
      criterionRatio E p L D eps := by
    apply le_trans _ hQ
    cases E
    · exact le_max_left _ _
    · exact le_max_right _ _
  have h := rand_successful_budget_asymptotic hp hL hD heps hthr hB
  rw [inverse_oracleRateExponent hp] at h
  apply le_trans _ h
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (criterionRatio_pos E p hL hD heps).le _)
  unfold complexityLowerConstant
  rw [inverse_oracleRateExponent hp]
  cases E
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- Same lower estimate for deterministic complexity follows from the
proved Borel one-seed inclusion, with no informal policy-class argument. -/
theorem detOracleComplexity_lower
    (E : OracleErrorCriterion) {p : ℕ} (hp : 2 ≤ p)
    {L D eps : ℝ} (hL : 0 < L) (hD : 0 < D) (heps : 0 < eps)
    (hQ : complexityLowerThreshold p ≤ criterionRatio E p L D eps) :
    ENNReal.ofReal (complexityLowerConstant p *
      (criterionRatio E p L D eps) ^ (2 / (3 * (p : ℝ) - 1))) ≤
      (detOracleComplexity E p L D eps : ℝ≥0∞) :=
  (randOracleComplexity_lower.{0} E hp hL hD heps hQ).trans
    (ENat.toENNReal_mono (randOracleComplexity_le_det.{0} E p L D eps))

end
end MinimaxAudit
