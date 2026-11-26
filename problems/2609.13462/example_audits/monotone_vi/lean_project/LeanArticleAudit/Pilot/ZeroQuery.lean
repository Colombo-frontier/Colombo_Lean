import LeanArticleAudit.Pilot.Contracts

/-!
# The zero-query lower bound

This module formalizes `lem:zero-query`.  A budget-zero Borel stopping policy
can only return a seed-dependent feasible point; in particular its output law
is identical for the two unknown constant operators used below.
-/

open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace LeanArticleAudit.Pilot

noncomputable section

/-- The public one-dimensional interval instance used in `lem:zero-query`. -/
def intervalVIData (p : ℕ) (hp : 2 ≤ p) (Lp D : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D) : VIPublicData ℝ where
  dimension_pos := by simp
  p := p
  p_ge_two := hp
  Lp := Lp
  Lp_pos := hLp
  D := D
  D_pos := hD
  X := Set.Icc (-D / 2) (D / 2)
  X_nonempty := ⟨0, by constructor <;> linarith⟩
  X_compact := isCompact_Icc
  X_convex := convex_Icc _ _
  x0 := 0
  x0_mem := by constructor <;> linarith
  diameter_le := by
    intro x hx y hy
    rw [Real.dist_eq]
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The positive constant adversary `F₊(x)=M`. -/
def zeroQueryPlusOperator (M : ℝ) : ℝ → ℝ := fun _ => M

/-- The negative constant adversary `F₋(x)=-M`. -/
def zeroQueryMinusOperator (M : ℝ) : ℝ → ℝ := fun _ => -M

theorem zeroQueryPlusOperator_admissible
    (p : ℕ) (hp : 2 ≤ p) (Lp D M : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D) :
    IsAdmissibleOperator (intervalVIData p hp Lp D hLp hD)
      (zeroQueryPlusOperator M) := by
  refine ⟨⟨Set.univ, isOpen_univ, subset_univ _, ?_⟩, ?_, ?_⟩
  · exact contDiff_const.contDiffOn
  · intro x hx y hy
    simp [zeroQueryPlusOperator]
  · intro x hx y hy
    have hn : p - 1 ≠ 0 := by omega
    change ‖iteratedFDeriv ℝ (p - 1) (fun _ : ℝ => M) x -
      iteratedFDeriv ℝ (p - 1) (fun _ : ℝ => M) y‖ ≤ Lp * ‖x - y‖
    rw [iteratedFDeriv_const_of_ne hn]
    simpa using mul_nonneg hLp.le (norm_nonneg (x - y))

theorem zeroQueryMinusOperator_admissible
    (p : ℕ) (hp : 2 ≤ p) (Lp D M : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D) :
    IsAdmissibleOperator (intervalVIData p hp Lp D hLp hD)
      (zeroQueryMinusOperator M) := by
  refine ⟨⟨Set.univ, isOpen_univ, subset_univ _, ?_⟩, ?_, ?_⟩
  · exact contDiff_const.contDiffOn
  · intro x hx y hy
    simp [zeroQueryMinusOperator]
  · intro x hx y hy
    have hn : p - 1 ≠ 0 := by omega
    change ‖iteratedFDeriv ℝ (p - 1) (fun _ : ℝ => -M) x -
      iteratedFDeriv ℝ (p - 1) (fun _ : ℝ => -M) y‖ ≤ Lp * ‖x - y‖
    rw [iteratedFDeriv_const_of_ne hn]
    simpa using mul_nonneg hLp.le (norm_nonneg (x - y))

private theorem zero_mem_interval_normalCone (D x : ℝ) :
    0 ∈ normalCone (Set.Icc (-D / 2) (D / 2)) x := by
  intro z hz
  simp

private theorem normal_nonneg_of_not_left
    {D x n : ℝ} (hD : 0 < D)
    (hx : x ∈ Set.Icc (-D / 2) (D / 2)) (hne : x ≠ -D / 2)
    (hn : n ∈ normalCone (Set.Icc (-D / 2) (D / 2)) x) :
    0 ≤ n := by
  have hleft : -D / 2 < x := lt_of_le_of_ne hx.1 (Ne.symm hne)
  have htest := hn (-D / 2) ⟨le_rfl, by linarith⟩
  rw [Real.inner_apply] at htest
  nlinarith

private theorem normal_nonpos_of_not_right
    {D x n : ℝ} (hD : 0 < D)
    (hx : x ∈ Set.Icc (-D / 2) (D / 2)) (hne : x ≠ D / 2)
    (hn : n ∈ normalCone (Set.Icc (-D / 2) (D / 2)) x) :
    n ≤ 0 := by
  have hright : x < D / 2 := lt_of_le_of_ne hx.2 hne
  have htest := hn (D / 2) ⟨by linarith, le_rfl⟩
  rw [Real.inner_apply] at htest
  nlinarith

theorem zeroQueryPlus_tangentResidual_left
    (p : ℕ) (hp : 2 ≤ p) (Lp D M : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D) (hM : 0 < M) :
    tangentResidual (intervalVIData p hp Lp D hLp hD)
      (zeroQueryPlusOperator M) (-D / 2) = 0 := by
  apply Metric.infDist_zero_of_mem
  refine ⟨-M, ?_, ?_⟩
  · intro z hz
    rw [Real.inner_apply]
    nlinarith [hz.1]
  · simp [zeroQueryPlusOperator]

theorem zeroQueryMinus_tangentResidual_right
    (p : ℕ) (hp : 2 ≤ p) (Lp D M : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D) (hM : 0 < M) :
    tangentResidual (intervalVIData p hp Lp D hLp hD)
      (zeroQueryMinusOperator M) (D / 2) = 0 := by
  apply Metric.infDist_zero_of_mem
  refine ⟨M, ?_, ?_⟩
  · intro z hz
    rw [Real.inner_apply]
    nlinarith [hz.2]
  · simp [zeroQueryMinusOperator]

theorem zeroQueryPlus_tangentResidual_of_not_left
    (p : ℕ) (hp : 2 ≤ p) (Lp D M : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D) (hM : 0 < M)
    (x : ℝ) (hx : x ∈ Set.Icc (-D / 2) (D / 2))
    (hne : x ≠ -D / 2) :
    tangentResidual (intervalVIData p hp Lp D hLp hD)
      (zeroQueryPlusOperator M) x = M := by
  let S := (fun n : ℝ => zeroQueryPlusOperator M x + n) ''
    normalCone (Set.Icc (-D / 2) (D / 2)) x
  have hMmem : M ∈ S := by
    refine ⟨0, zero_mem_interval_normalCone D x, ?_⟩
    simp [zeroQueryPlusOperator]
  have hSne : S.Nonempty := ⟨M, hMmem⟩
  change Metric.infDist 0 S = M
  apply le_antisymm
  · simpa [Real.dist_eq, abs_of_pos hM] using
      (Metric.infDist_le_dist_of_mem (x := (0 : ℝ)) hMmem)
  · apply (Metric.le_infDist hSne).2
    intro y hy
    rcases hy with ⟨n, hn, rfl⟩
    rw [Real.dist_eq, abs_sub_comm, sub_zero, abs_of_nonneg]
    · simp only [zeroQueryPlusOperator]
      linarith [normal_nonneg_of_not_left hD hx hne hn]
    · simp only [zeroQueryPlusOperator]
      linarith [normal_nonneg_of_not_left hD hx hne hn]

theorem zeroQueryMinus_tangentResidual_of_not_right
    (p : ℕ) (hp : 2 ≤ p) (Lp D M : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D) (hM : 0 < M)
    (x : ℝ) (hx : x ∈ Set.Icc (-D / 2) (D / 2))
    (hne : x ≠ D / 2) :
    tangentResidual (intervalVIData p hp Lp D hLp hD)
      (zeroQueryMinusOperator M) x = M := by
  let S := (fun n : ℝ => zeroQueryMinusOperator M x + n) ''
    normalCone (Set.Icc (-D / 2) (D / 2)) x
  have hnegMmem : -M ∈ S := by
    refine ⟨0, zero_mem_interval_normalCone D x, ?_⟩
    simp [zeroQueryMinusOperator]
  have hSne : S.Nonempty := ⟨-M, hnegMmem⟩
  change Metric.infDist 0 S = M
  apply le_antisymm
  · simpa [Real.dist_eq, abs_of_pos hM] using
      (Metric.infDist_le_dist_of_mem (x := (0 : ℝ)) hnegMmem)
  · apply (Metric.le_infDist hSne).2
    intro y hy
    rcases hy with ⟨n, hn, rfl⟩
    rw [Real.dist_eq, abs_sub_comm, sub_zero, abs_of_nonpos]
    · simp only [zeroQueryMinusOperator]
      linarith [normal_nonpos_of_not_right hD hx hne hn]
    · simp only [zeroQueryMinusOperator]
      linarith [normal_nonpos_of_not_right hD hx hne hn]

section ZeroQueryPolicy

variable {E Answer : Type*} [MeasurableSpace E] [MeasurableSpace Answer]

/-- There is exactly one history of length zero. -/
def emptyOracleHistory (X : Set E) : OracleHistory X Answer 0 :=
  fun i => Fin.elim0 i

/-- Execute a budget-zero policy.  The fallback branch is unreachable by
`cap_stops`; it only makes the eliminator a total measurable map. -/
def BorelStoppingPolicy.zeroQueryOutput {X : Set E}
    (policy : BorelStoppingPolicy (Answer := Answer) X 0) (fallback : X)
    (seed : policy.Seed) : X :=
  Sum.elim id (fun _ => fallback)
    (policy.rule ⟨0, Nat.zero_lt_one⟩
      (seed, emptyOracleHistory (Answer := Answer) X))

theorem BorelStoppingPolicy.zeroQuery_action {X : Set E}
    (policy : BorelStoppingPolicy (Answer := Answer) X 0) (fallback : X)
    (seed : policy.Seed) :
    policy.rule ⟨0, Nat.zero_lt_one⟩
        (seed, emptyOracleHistory (Answer := Answer) X) =
      Sum.inl (policy.zeroQueryOutput fallback seed) := by
  obtain ⟨output, houtput⟩ := policy.cap_stops
    (seed, emptyOracleHistory (Answer := Answer) X)
  change policy.rule ⟨0, Nat.zero_lt_one⟩
      (seed, emptyOracleHistory (Answer := Answer) X) =
    Sum.inl (Sum.elim id (fun _ => fallback)
      (policy.rule ⟨0, Nat.zero_lt_one⟩
        (seed, emptyOracleHistory (Answer := Answer) X)))
  have haction : policy.rule ⟨0, Nat.zero_lt_one⟩
      (seed, emptyOracleHistory (Answer := Answer) X) = Sum.inl output := by
    simpa using houtput
  rw [haction]
  simp [id]

/-- A budget-zero execution makes no oracle calls and returns the same point
for every oracle.  This is the formal same-output-distribution premise of the
source proof. -/
theorem BorelStoppingPolicy.zeroQuery_isUnpaddedRun {X : Set E}
    (policy : BorelStoppingPolicy (Answer := Answer) X 0) (fallback : X)
    (oracle : E → Answer) (seed : policy.Seed) :
    policy.IsUnpaddedRun oracle seed 0 le_rfl
      (emptyOracleHistory (Answer := Answer) X)
      (policy.zeroQueryOutput fallback seed) := by
  constructor
  · intro i
    exact Fin.elim0 i
  · exact policy.zeroQuery_action fallback seed

theorem BorelStoppingPolicy.measurable_zeroQueryOutput {X : Set E}
    (policy : BorelStoppingPolicy (Answer := Answer) X 0) (fallback : X) :
    @Measurable policy.Seed X policy.seedMeasurable inferInstance
      (policy.zeroQueryOutput fallback) := by
  let state : policy.Seed →
      policy.Seed × OracleHistory X Answer 0 :=
    fun seed => (seed, emptyOracleHistory (Answer := Answer) X)
  have hstate : @Measurable policy.Seed
      (policy.Seed × OracleHistory X Answer 0) policy.seedMeasurable
      (MeasurableSpace.prod policy.seedMeasurable inferInstance) state :=
    measurable_id.prodMk measurable_const
  exact (measurable_id.sumElim measurable_const).comp
    ((policy.rule_measurable ⟨0, Nat.zero_lt_one⟩).comp hstate)

end ZeroQueryPolicy

section EndpointEvents

variable (p : ℕ) (hp : 2 ≤ p) (Lp D epsilon M : ℝ)
  (hLp : 0 < Lp) (hD : 0 < D)

abbrev ZeroQueryAnswer := SymmetricExactJet ℝ p

def intervalLeftEndpoint :
    (intervalVIData p hp Lp D hLp hD).X :=
  ⟨-D / 2, ⟨le_rfl, by linarith⟩⟩

def intervalRightEndpoint :
    (intervalVIData p hp Lp D hLp hD).X :=
  ⟨D / 2, ⟨by linarith, le_rfl⟩⟩

variable (policy : BorelStoppingPolicy
  (Answer := ZeroQueryAnswer p)
  (intervalVIData p hp Lp D hLp hD).X 0)

def zeroQueryReturnedPoint (seed : policy.Seed) :
    (intervalVIData p hp Lp D hLp hD).X :=
  policy.zeroQueryOutput
    ⟨(intervalVIData p hp Lp D hLp hD).x0,
      (intervalVIData p hp Lp D hLp hD).x0_mem⟩ seed

def zeroQueryPlusSuccessEvent : Set policy.Seed :=
  {seed | tangentResidual (intervalVIData p hp Lp D hLp hD)
    (zeroQueryPlusOperator M) (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≤
      epsilon}

def zeroQueryMinusSuccessEvent : Set policy.Seed :=
  {seed | tangentResidual (intervalVIData p hp Lp D hLp hD)
    (zeroQueryMinusOperator M) (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≤
      epsilon}

theorem measurable_zeroQueryReturnedPoint :
    @Measurable policy.Seed (intervalVIData p hp Lp D hLp hD).X
      policy.seedMeasurable inferInstance
      (zeroQueryReturnedPoint p hp Lp D hLp hD policy) := by
  exact policy.measurable_zeroQueryOutput _

theorem mem_zeroQueryPlusSuccessEvent_iff
    (hepsilon : 0 < epsilon) (hM : epsilon < M) (seed : policy.Seed) :
    seed ∈ zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy ↔
      zeroQueryReturnedPoint p hp Lp D hLp hD policy seed =
        intervalLeftEndpoint p hp Lp D hLp hD := by
  constructor
  · intro hsuccess
    change tangentResidual (intervalVIData p hp Lp D hLp hD)
      (zeroQueryPlusOperator M)
      (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≤ epsilon at hsuccess
    by_contra hne
    have hne' :
        (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≠ -D / 2 := by
      intro heq
      apply hne
      apply Subtype.ext
      exact heq
    rw [zeroQueryPlus_tangentResidual_of_not_left p hp Lp D M hLp hD
        (hM.trans' hepsilon) _
        (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).2 hne'] at hsuccess
    linarith
  · intro hout
    change tangentResidual (intervalVIData p hp Lp D hLp hD)
      (zeroQueryPlusOperator M)
      (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≤ epsilon
    rw [hout]
    change tangentResidual (intervalVIData p hp Lp D hLp hD)
      (zeroQueryPlusOperator M) (-D / 2) ≤ epsilon
    rw [zeroQueryPlus_tangentResidual_left p hp Lp D M hLp hD
      (hM.trans' hepsilon)]
    exact hepsilon.le

theorem mem_zeroQueryMinusSuccessEvent_iff
    (hepsilon : 0 < epsilon) (hM : epsilon < M) (seed : policy.Seed) :
    seed ∈ zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy ↔
      zeroQueryReturnedPoint p hp Lp D hLp hD policy seed =
        intervalRightEndpoint p hp Lp D hLp hD := by
  constructor
  · intro hsuccess
    change tangentResidual (intervalVIData p hp Lp D hLp hD)
      (zeroQueryMinusOperator M)
      (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≤ epsilon at hsuccess
    by_contra hne
    have hne' :
        (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≠ D / 2 := by
      intro heq
      apply hne
      apply Subtype.ext
      exact heq
    rw [zeroQueryMinus_tangentResidual_of_not_right p hp Lp D M hLp hD
        (hM.trans' hepsilon) _
        (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).2 hne'] at hsuccess
    linarith
  · intro hout
    change tangentResidual (intervalVIData p hp Lp D hLp hD)
      (zeroQueryMinusOperator M)
      (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≤ epsilon
    rw [hout]
    change tangentResidual (intervalVIData p hp Lp D hLp hD)
      (zeroQueryMinusOperator M) (D / 2) ≤ epsilon
    rw [zeroQueryMinus_tangentResidual_right p hp Lp D M hLp hD
      (hM.trans' hepsilon)]
    exact hepsilon.le

theorem measurableSet_zeroQueryPlusSuccessEvent
    (hepsilon : 0 < epsilon) (hM : epsilon < M) :
    @MeasurableSet policy.Seed policy.seedMeasurable
      (zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy) := by
  have heq : zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy =
      zeroQueryReturnedPoint p hp Lp D hLp hD policy ⁻¹'
        {intervalLeftEndpoint p hp Lp D hLp hD} := by
    ext seed
    exact mem_zeroQueryPlusSuccessEvent_iff p hp Lp D epsilon M hLp hD
      policy hepsilon hM seed
  rw [heq]
  exact (measurableSet_singleton _).preimage
    (measurable_zeroQueryReturnedPoint p hp Lp D hLp hD policy)

theorem measurableSet_zeroQueryMinusSuccessEvent
    (hepsilon : 0 < epsilon) (hM : epsilon < M) :
    @MeasurableSet policy.Seed policy.seedMeasurable
      (zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy) := by
  have heq : zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy =
      zeroQueryReturnedPoint p hp Lp D hLp hD policy ⁻¹'
        {intervalRightEndpoint p hp Lp D hLp hD} := by
    ext seed
    exact mem_zeroQueryMinusSuccessEvent_iff p hp Lp D epsilon M hLp hD
      policy hepsilon hM seed
  rw [heq]
  exact (measurableSet_singleton _).preimage
    (measurable_zeroQueryReturnedPoint p hp Lp D hLp hD policy)

theorem zeroQuerySuccessEvents_disjoint
    (hepsilon : 0 < epsilon) (hM : epsilon < M) :
    Disjoint
      (zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy)
      (zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy) := by
  rw [Set.disjoint_left]
  intro seed hplus hminus
  have hl := (mem_zeroQueryPlusSuccessEvent_iff p hp Lp D epsilon M hLp hD
    policy hepsilon hM seed).1 hplus
  have hr := (mem_zeroQueryMinusSuccessEvent_iff p hp Lp D epsilon M hLp hD
    policy hepsilon hM seed).1 hminus
  have hend : (-D / 2 : ℝ) = D / 2 := congrArg Subtype.val (hl.symm.trans hr)
  linarith

theorem zeroQuery_not_both_two_thirds
    (hepsilon : 0 < epsilon) (hM : epsilon < M) :
    ¬ ((2 / 3 : ℝ≥0∞) ≤ policy.seedMeasure
        (zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy) ∧
      (2 / 3 : ℝ≥0∞) ≤ policy.seedMeasure
      (zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy)) := by
  letI := policy.seedMeasurable
  letI := policy.seedProbability
  intro hboth
  have hmeasPlus := measurableSet_zeroQueryPlusSuccessEvent p hp Lp D epsilon M
    hLp hD policy hepsilon hM
  have hmeasMinus := measurableSet_zeroQueryMinusSuccessEvent p hp Lp D epsilon M
    hLp hD policy hepsilon hM
  have hdisj := zeroQuerySuccessEvents_disjoint p hp Lp D epsilon M hLp hD
    policy hepsilon hM
  have hunion : policy.seedMeasure
      (zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy ∪
        zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy) =
      policy.seedMeasure
          (zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy) +
        policy.seedMeasure
          (zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy) := by
    exact measure_union hdisj hmeasMinus
  have hleOne : policy.seedMeasure
      (zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy ∪
        zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy) ≤ 1 := by
    calc
      _ ≤ policy.seedMeasure Set.univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  rw [hunion] at hleOne
  have hfourthirds : (2 / 3 : ℝ≥0∞) + (2 / 3 : ℝ≥0∞) ≤
      policy.seedMeasure
          (zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy) +
        policy.seedMeasure
          (zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy) :=
    add_le_add hboth.1 hboth.2
  have : (2 / 3 : ℝ≥0∞) + (2 / 3 : ℝ≥0∞) ≤ 1 :=
    hfourthirds.trans hleOne
  have hgt : (1 : ℝ≥0∞) < (2 / 3 : ℝ≥0∞) + (2 / 3 : ℝ≥0∞) := by
    apply (ENNReal.toReal_lt_toReal (by simp) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_div]
    norm_num
  exact (not_lt_of_ge this) hgt

end EndpointEvents

/-- Literal uniform-success predicate for a zero-query policy on the fixed
public interval data.  The unknown operator is quantified only after the
policy and its seed law have been fixed. -/
def ZeroQueryUniformSuccess
    (p : ℕ) (hp : 2 ≤ p) (Lp D epsilon : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D)
    (policy : BorelStoppingPolicy.{0, 0, 0}
      (Answer := ZeroQueryAnswer p)
      (intervalVIData p hp Lp D hLp hD).X 0) : Prop :=
  ∀ F : ℝ → ℝ,
    IsAdmissibleOperator (intervalVIData p hp Lp D hLp hD) F →
      @MeasurableSet policy.Seed policy.seedMeasurable
        {seed | tangentResidual (intervalVIData p hp Lp D hLp hD) F
          (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≤ epsilon} ∧
      (2 / 3 : ℝ≥0∞) ≤ policy.seedMeasure
        {seed | tangentResidual (intervalVIData p hp Lp D hLp hD) F
          (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≤ epsilon}

/-- Full source-facing conclusion for one budget-zero randomized policy.

The single `zeroQueryReturnedPoint` is used for both operators, and the
`IsUnpaddedRun` conjunct says that this very output is returned against every
possible oracle without making a call.  The next two conjuncts identify the
two epsilon-solution sets exactly with opposite endpoints. -/
def ZeroQueryConclusion
    (p : ℕ) (hp : 2 ≤ p) (Lp D epsilon M : ℝ)
    (hLp : 0 < Lp) (hD : 0 < D)
    (policy : BorelStoppingPolicy.{0, 0, 0}
      (Answer := ZeroQueryAnswer p)
      (intervalVIData p hp Lp D hLp hD).X 0) : Prop :=
  epsilon < M ∧
  IsAdmissibleOperator (intervalVIData p hp Lp D hLp hD)
    (zeroQueryPlusOperator M) ∧
  IsAdmissibleOperator (intervalVIData p hp Lp D hLp hD)
    (zeroQueryMinusOperator M) ∧
  @Measurable policy.Seed (intervalVIData p hp Lp D hLp hD).X
    policy.seedMeasurable inferInstance
    (zeroQueryReturnedPoint p hp Lp D hLp hD policy) ∧
  (∀ (oracle : ℝ → ZeroQueryAnswer p) (seed : policy.Seed),
    policy.IsUnpaddedRun oracle seed 0 le_rfl
      (emptyOracleHistory
        (Answer := ZeroQueryAnswer p) (intervalVIData p hp Lp D hLp hD).X)
      (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed)) ∧
  (∀ seed : policy.Seed,
    tangentResidual (intervalVIData p hp Lp D hLp hD)
        (zeroQueryPlusOperator M)
        (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≤ epsilon ↔
      zeroQueryReturnedPoint p hp Lp D hLp hD policy seed =
        intervalLeftEndpoint p hp Lp D hLp hD) ∧
  (∀ seed : policy.Seed,
    tangentResidual (intervalVIData p hp Lp D hLp hD)
        (zeroQueryMinusOperator M)
        (zeroQueryReturnedPoint p hp Lp D hLp hD policy seed).1 ≤ epsilon ↔
      zeroQueryReturnedPoint p hp Lp D hLp hD policy seed =
        intervalRightEndpoint p hp Lp D hLp hD) ∧
  @MeasurableSet policy.Seed policy.seedMeasurable
    (zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy) ∧
  @MeasurableSet policy.Seed policy.seedMeasurable
    (zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy) ∧
  ¬ ((2 / 3 : ℝ≥0∞) ≤ policy.seedMeasure
        (zeroQueryPlusSuccessEvent p hp Lp D epsilon M hLp hD policy) ∧
      (2 / 3 : ℝ≥0∞) ≤ policy.seedMeasure
        (zeroQueryMinusSuccessEvent p hp Lp D epsilon M hLp hD policy)) ∧
  ¬ ZeroQueryUniformSuccess p hp Lp D epsilon hLp hD policy

/-- Audit-facing statement of `lem:zero-query`: for every positive public
triple and every measurable randomized zero-query policy, the two admissible
constant instances force disjoint success events, so uniform success at
probability `2/3` is impossible. -/
def ZeroQueryLowerClaim : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p)
    (Lp D epsilon : ℝ) (hLp : 0 < Lp) (hD : 0 < D)
    (_hepsilon : 0 < epsilon)
    (policy : BorelStoppingPolicy.{0, 0, 0}
      (Answer := ZeroQueryAnswer p)
      (intervalVIData p hp Lp D hLp hD).X 0),
    ∃ M : ℝ, ZeroQueryConclusion p hp Lp D epsilon M hLp hD policy

theorem zeroQueryLowerClaim_proof : ZeroQueryLowerClaim := by
  intro p hp Lp D epsilon hLp hD hepsilon policy
  refine ⟨2 * epsilon, ?_⟩
  have hM : epsilon < 2 * epsilon := by linarith
  refine ⟨hM,
    zeroQueryPlusOperator_admissible p hp Lp D (2 * epsilon) hLp hD,
    zeroQueryMinusOperator_admissible p hp Lp D (2 * epsilon) hLp hD,
    measurable_zeroQueryReturnedPoint p hp Lp D hLp hD policy,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro oracle seed
    exact policy.zeroQuery_isUnpaddedRun
      ⟨(intervalVIData p hp Lp D hLp hD).x0,
        (intervalVIData p hp Lp D hLp hD).x0_mem⟩ oracle seed
  · intro seed
    exact mem_zeroQueryPlusSuccessEvent_iff p hp Lp D epsilon (2 * epsilon)
      hLp hD policy hepsilon hM seed
  · intro seed
    exact mem_zeroQueryMinusSuccessEvent_iff p hp Lp D epsilon (2 * epsilon)
      hLp hD policy hepsilon hM seed
  · exact measurableSet_zeroQueryPlusSuccessEvent p hp Lp D epsilon
      (2 * epsilon) hLp hD policy hepsilon hM
  · exact measurableSet_zeroQueryMinusSuccessEvent p hp Lp D epsilon
      (2 * epsilon) hLp hD policy hepsilon hM
  · exact zeroQuery_not_both_two_thirds p hp Lp D epsilon (2 * epsilon)
      hLp hD policy hepsilon hM
  · intro huniform
    have hplus := huniform (zeroQueryPlusOperator (2 * epsilon))
      (zeroQueryPlusOperator_admissible p hp Lp D (2 * epsilon) hLp hD)
    have hminus := huniform (zeroQueryMinusOperator (2 * epsilon))
      (zeroQueryMinusOperator_admissible p hp Lp D (2 * epsilon) hLp hD)
    exact (zeroQuery_not_both_two_thirds p hp Lp D epsilon (2 * epsilon)
      hLp hD policy hepsilon hM) ⟨hplus.2, hminus.2⟩

end

end LeanArticleAudit.Pilot
