import LeanArticleAudit.Pilot.RandomLower
import LeanArticleAudit.Pilot.DeterministicLower

/-!
# Executing the randomized lower-bound simulation

This module connects the abstract `SeededRandomRun` package to the concrete
early-stopping policy and symmetric exact-oracle interfaces.  The construction
keeps a genuine stopped prefix; padding is used only to expose fixed-index
queries to the concentration argument.
-/

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace LeanArticleAudit.Pilot

namespace OracleHistory

variable {E Answer : Type*} {X : Set E}

/-- Append one completed query/answer pair to a dependent finite history. -/
def snoc {n : ℕ} (history : OracleHistory X Answer n) (entry : X × Answer) :
    OracleHistory X Answer (n + 1) :=
  Fin.lastCases entry history

@[simp] theorem snoc_castSucc {n : ℕ} (history : OracleHistory X Answer n)
    (entry : X × Answer) (i : Fin n) :
    snoc history entry i.castSucc = history i := by
  simp [snoc]

@[simp] theorem snoc_last {n : ℕ} (history : OracleHistory X Answer n)
    (entry : X × Answer) :
    snoc history entry (Fin.last n) = entry := by
  simp [snoc]

end OracleHistory

section StageExecution

variable {E Answer : Type*} [MeasurableSpace E] [MeasurableSpace Answer]

/-- A stopped simulation may answer its `i`th query with a different oracle
from later stages.  This is the exact execution relation for the truncated
operators in the random-frame proof. -/
def BorelStoppingPolicy.IsUnpaddedStageRun {X : Set E} {budget : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Fin budget → E → Answer) (seed : policy.Seed)
    (n : ℕ) (hn : n ≤ budget) (history : OracleHistory X Answer n)
    (output : X) : Prop :=
  (∀ i : Fin n,
    policy.rule
        ⟨i.1, Nat.lt_trans (Nat.lt_of_lt_of_le i.2 hn)
          (Nat.lt_succ_self budget)⟩
        (seed, OracleHistory.restrict history (Nat.le_of_lt i.2)) =
          Sum.inr (history i).1 ∧
    (history i).2 = stageOracle
      ⟨i.1, Nat.lt_of_lt_of_le i.2 hn⟩ (history i).1) ∧
  policy.rule ⟨n, Nat.lt_succ_of_le hn⟩ (seed, history) = Sum.inl output

/-- Prefix consistency before the policy has stopped. -/
def BorelStoppingPolicy.IsStageRunPrefix {X : Set E} {budget : ℕ}
    (policy : BorelStoppingPolicy (Answer := Answer) X budget)
    (stageOracle : Fin budget → E → Answer) (seed : policy.Seed)
    (n : ℕ) (hn : n ≤ budget) (history : OracleHistory X Answer n) : Prop :=
  ∀ i : Fin n,
    policy.rule
        ⟨i.1, Nat.lt_trans (Nat.lt_of_lt_of_le i.2 hn)
          (Nat.lt_succ_self budget)⟩
        (seed, OracleHistory.restrict history (Nat.le_of_lt i.2)) =
          Sum.inr (history i).1 ∧
    (history i).2 = stageOracle
      ⟨i.1, Nat.lt_of_lt_of_le i.2 hn⟩ (history i).1

/-- Pointwise equality between all stage answers actually present in a
stopped history and one fixed oracle turns the simulation into a genuine run
against that fixed oracle. -/
theorem BorelStoppingPolicy.IsUnpaddedStageRun.to_fixedOracle
    {X : Set E} {budget : ℕ}
    {policy : BorelStoppingPolicy (Answer := Answer) X budget}
    {stageOracle : Fin budget → E → Answer} {fixedOracle : E → Answer}
    {seed : policy.Seed} {n : ℕ} {hn : n ≤ budget}
    {history : OracleHistory X Answer n} {output : X}
    (hrun : policy.IsUnpaddedStageRun stageOracle seed n hn history output)
    (hcouple : ∀ i : Fin n,
      stageOracle ⟨i.1, Nat.lt_of_lt_of_le i.2 hn⟩ (history i).1 =
        fixedOracle (history i).1) :
    policy.IsUnpaddedRun fixedOracle seed n hn history output := by
  refine ⟨?_, hrun.2⟩
  intro i
  refine ⟨hrun.1 i |>.1, ?_⟩
  rw [hrun.1 i |>.2, hcouple i]

end StageExecution

section SymmetricOracleCoupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Equality of the complete ordinary jets forces equality of any two exact
symmetric-jet oracle answers; the subtype symmetry certificates are
proof-irrelevant. -/
theorem ExactSymmetricJetOracle.answer_eq_of_fullJetCoupledAt
    {data : VIPublicData E} {F G : E → E}
    (oracleF : ExactSymmetricJetOracle data F)
    (oracleG : ExactSymmetricJetOracle data G) {x : E}
    (hjet : FullJetCoupledAt data.p F G x) :
    oracleF.answer x = oracleG.answer x := by
  funext j
  apply Subtype.ext
  rw [oracleF.exact, oracleG.exact]
  exact congrFun hjet j

end SymmetricOracleCoupling

section SlabJetCoupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- The links omitted by the stage-`t` truncated hidden map. -/
noncomputable def omittedHiddenMap (profile : GateProfile) (R : ℝ)
    (N t : ℕ) (v : Fin (N + 1) → E) (x : E) : E :=
  hiddenQ N • ∑ i : Fin N, if t ≤ i.1 then
    gateRidge profile (hiddenTau R N) (v i.castSucc) (v i.succ) x else 0

theorem hiddenMap_eq_truncated_add_omitted (profile : GateProfile) (R : ℝ)
    (N t : ℕ) (v : Fin (N + 1) → E) :
    hiddenMap profile R N v =
      truncatedHiddenMap profile R N t v +
        omittedHiddenMap profile R N t v := by
  funext x
  simp only [hiddenMap, truncatedHiddenMap, omittedHiddenMap, gateRidge,
    Pi.add_apply]
  have hsum : (∑ i : Fin N,
      gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) x) • v i.succ) =
      (∑ i : Fin N, if i.1 < t then
        gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) x) • v i.succ else 0) +
      (∑ i : Fin N, if t ≤ i.1 then
        gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) x) • v i.succ else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hit : i.1 < t
    · simp [hit, Nat.not_le.mpr hit]
    · simp [hit, Nat.le_of_not_gt hit]
  rw [hsum]
  module

theorem omittedHiddenMap_iteratedFDeriv_eq_zero (n : ℕ)
    (profile : GateProfile) {R : ℝ} (hR : 0 < R) (N t : ℕ)
    (v : Fin (N + 1) → E) (x : E)
    (hslab : ∀ i : Fin N, t ≤ i.1 →
      |inner ℝ (v i.castSucc) x| ≤ hiddenTau R N / 2) :
    iteratedFDeriv ℝ n (omittedHiddenMap profile R N t v) x = 0 := by
  let G : E → E := fun z => ∑ i : Fin N, if t ≤ i.1 then
    gateRidge profile (hiddenTau R N) (v i.castSucc) (v i.succ) z else 0
  have hridge (i : Fin N) : ContDiff ℝ n
      (gateRidge profile (hiddenTau R N) (v i.castSucc) (v i.succ)) := by
    exact ((contDiff_infty.mp
      (gate_contDiff profile (hiddenTau_pos hR N).ne') n).comp
        (innerSL ℝ (v i.castSucc)).contDiff).smul_const _
  have hG : ContDiff ℝ n G := by
    apply ContDiff.sum
    intro i _hi
    by_cases hit : t ≤ i.1
    · simpa [G, hit] using hridge i
    · simpa [hit] using (contDiff_const : ContDiff ℝ n (fun _ : E => (0 : E)))
  have hqG : ContDiff ℝ n (fun z => hiddenQ N • G z) :=
    hG.const_smul (hiddenQ N)
  have hdef : omittedHiddenMap profile R N t v =
      fun z => hiddenQ N • G z := by
    rfl
  rw [hdef, iteratedFDeriv_const_smul_apply' hG.contDiffAt]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [smul_apply,
    iteratedFDeriv_fun_sum_apply (fun i _ => by
      by_cases hit : t ≤ i.1
      · simpa [G, hit] using (hridge i).contDiffAt
      · simpa [hit] using
          (contDiffAt_const : ContDiffAt ℝ n (fun _ : E => (0 : E)) x))]
  rw [sum_apply]
  have hsum : (∑ i : Fin N,
      iteratedFDeriv ℝ n
        (fun z => if t ≤ i.1 then
          gateRidge profile (hiddenTau R N) (v i.castSucc) (v i.succ) z else 0)
        x u) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    by_cases hit : t ≤ i.1
    · simp only [hit, if_pos]
      rw [gateRidge_iteratedFDeriv_apply n profile
        (hiddenTau_pos hR N).ne']
      rw [gate_all_derivatives_zero_core profile (hiddenTau_pos hR N) n
        (hslab i hit)]
      simp
    · simp [hit]
  rw [hsum, smul_zero]
  simp

theorem truncatedHiddenMap_iteratedFDeriv_eq_of_slab (n : ℕ)
    (profile : GateProfile) {R : ℝ} (hR : 0 < R) (N t : ℕ)
    (v : Fin (N + 1) → E) (x : E)
    (hslab : ∀ i : Fin N, t ≤ i.1 →
      |inner ℝ (v i.castSucc) x| ≤ hiddenTau R N / 2) :
    iteratedFDeriv ℝ n (truncatedHiddenMap profile R N t v) x =
      iteratedFDeriv ℝ n (hiddenMap profile R N v) x := by
  have htrunc : ContDiff ℝ n (truncatedHiddenMap profile R N t v) := by
    have htau := (hiddenTau_pos hR N).ne'
    apply ContDiff.add
    · fun_prop
    · apply ContDiff.const_smul
      apply ContDiff.sum
      intro i _hi
      by_cases hit : i.1 < t
      · simpa [truncatedHiddenMap, hit] using
          ((contDiff_infty.mp (gate_contDiff profile htau) n).comp
            (innerSL ℝ (v i.castSucc)).contDiff).smul_const (v i.succ)
      · simpa [hit] using (contDiff_const : ContDiff ℝ n (fun _ : E => (0 : E)))
  have homit : ContDiff ℝ n (omittedHiddenMap profile R N t v) := by
    change ContDiff ℝ n (fun z => hiddenQ N •
      ∑ i : Fin N, if t ≤ i.1 then
        gateRidge profile (hiddenTau R N) (v i.castSucc) (v i.succ) z else 0)
    apply ContDiff.const_smul
    apply ContDiff.sum
    intro i _hi
    by_cases hit : t ≤ i.1
    · simp only [hit, if_pos]
      change ContDiff ℝ n (fun z : E =>
        gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) z) • v i.succ)
      exact (((contDiff_infty.mp
        (gate_contDiff profile (hiddenTau_pos hR N).ne') n).comp
          (innerSL ℝ (v i.castSucc)).contDiff).smul_const (v i.succ))
    · simpa [hit] using (contDiff_const : ContDiff ℝ n (fun _ : E => (0 : E)))
  rw [hiddenMap_eq_truncated_add_omitted profile R N t v,
    iteratedFDeriv_add_apply htrunc.contDiffAt homit.contDiffAt,
    omittedHiddenMap_iteratedFDeriv_eq_zero n profile hR N t v x hslab,
    add_zero]

theorem truncatedHiddenOperator_iteratedFDeriv_eq_of_slab (n p : ℕ)
    (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) (v : Fin (N + 1) → E) (x : E)
    (hslab : ∀ i : Fin N, t ≤ i.1 →
      |inner ℝ (v i.castSucc) x| ≤ hiddenTau R N / 2) :
    iteratedFDeriv ℝ n (truncatedHiddenOperator p profile Lp R N t v) x =
      iteratedFDeriv ℝ n (hiddenOperator p profile Lp R N v) x := by
  let A : E → E := fun y => y - truncatedHiddenMap profile R N t v y
  let B : E → E := fun y => y - hiddenMap profile R N v y
  have htrunc : ContDiff ℝ n (truncatedHiddenMap profile R N t v) := by
    have htau := (hiddenTau_pos hR N).ne'
    apply ContDiff.add
    · fun_prop
    · apply ContDiff.const_smul
      apply ContDiff.sum
      intro i _hi
      by_cases hit : i.1 < t
      · simpa [truncatedHiddenMap, hit] using
          ((contDiff_infty.mp (gate_contDiff profile htau) n).comp
            (innerSL ℝ (v i.castSucc)).contDiff).smul_const (v i.succ)
      · simpa [hit] using (contDiff_const : ContDiff ℝ n (fun _ : E => (0 : E)))
  have hhidden : ContDiff ℝ n (hiddenMap profile R N v) :=
    contDiff_infty.mp (hiddenMap_contDiff profile hR v) n
  have hA : ContDiff ℝ n A := contDiff_id.sub htrunc
  have hB : ContDiff ℝ n B := contDiff_id.sub hhidden
  change iteratedFDeriv ℝ n (fun y => hiddenLambda p profile Lp R N • A y) x =
    iteratedFDeriv ℝ n (fun y => hiddenLambda p profile Lp R N • B y) x
  rw [iteratedFDeriv_const_smul_apply' hA.contDiffAt,
    iteratedFDeriv_const_smul_apply' hB.contDiffAt]
  congr 1
  dsimp [A, B]
  change iteratedFDeriv ℝ n (id - truncatedHiddenMap profile R N t v) x =
    iteratedFDeriv ℝ n (id - hiddenMap profile R N v) x
  rw [iteratedFDeriv_sub_apply contDiffAt_id htrunc.contDiffAt,
    iteratedFDeriv_sub_apply contDiffAt_id hhidden.contDiffAt,
    truncatedHiddenMap_iteratedFDeriv_eq_of_slab n profile hR N t v x hslab]

theorem truncatedHiddenOperator_fullJetCoupledAt_of_slab (p : ℕ)
    (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) (v : Fin (N + 1) → E) (x : E)
    (hslab : ∀ i : Fin N, t ≤ i.1 →
      |inner ℝ (v i.castSucc) x| ≤ hiddenTau R N / 2) :
    FullJetCoupledAt p
      (truncatedHiddenOperator p profile Lp R N t v)
      (hiddenOperator p profile Lp R N v) x := by
  rw [fullJetCoupledAt_iff]
  intro j
  exact truncatedHiddenOperator_iteratedFDeriv_eq_of_slab j.1 p profile Lp hR
    N t v x hslab

/-- Membership in the joint finite slab event exposes every future-coordinate
bound needed at a particular simulated query. -/
theorem randomSlabEvent_query_slab
    {prior : SequentialFramePrior E N d R}
    (sim : FixedSeedSimulation prior) {omega : prior.Omega}
    (hgood : omega ∈ randomSlabEvent prior sim) (t i : Fin N)
    (hti : t.1 ≤ i.1) :
    |inner ℝ (prior.frame omega i.castSucc) (sim.query t omega)| ≤
      hiddenTau R N / 2 := by
  have h := Set.mem_iInter.mp hgood (Sum.inl (t, i))
  simpa [randomSlabGood, hti] using h

end SlabJetCoupling

section BorelBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Concrete execution data needed to derive `SeededRandomRun` from a
`BorelStoppingPolicy`.

The policy execution and both exact oracles are explicit.  The only fields
not forced by the operational semantics are the prefix/measurability facts
required by the probability layer.  Complete-jet equality on the closed slab
is proved above, including at `|inner| = tau/2`; it is not assumed here. -/
structure BorelRandomExecution
    (prior : SequentialFramePrior E N d R)
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
    (policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E p) (Metric.closedBall (0 : E) R) N) where
  simulation : policy.Seed → FixedSeedSimulation prior
  stageOracle : (omega : prior.Omega) → (t : Fin N) →
    ExactSymmetricJetOracle
      (ballVIData (E := E) p hp Lp hLp R hR)
      (truncatedHiddenOperator p profile Lp R N t.1 (prior.frame omega))
  actualOracle : ∀ omega,
    ExactSymmetricJetOracle
      (ballVIData (E := E) p hp Lp hLp R hR)
      (hiddenOperator p profile Lp R N (prior.frame omega))
  stoppedAt : prior.Omega → policy.Seed → ℕ
  stoppedAt_le : ∀ omega seed, stoppedAt omega seed ≤ N
  history : (omega : prior.Omega) → (seed : policy.Seed) →
    OracleHistory (Metric.closedBall (0 : E) R) (SymmetricExactJet E p)
      (stoppedAt omega seed)
  output : prior.Omega → policy.Seed → Metric.closedBall (0 : E) R
  /-- Saved output of a genuine execution against the final fixed hidden
  oracle, defined for every frame and seed, including outside the slab. -/
  actualOutput : prior.Omega → policy.Seed → Metric.closedBall (0 : E) R
  stage_run : ∀ omega seed,
    policy.IsUnpaddedStageRun
      (fun t => (stageOracle omega t).answer) seed
      (stoppedAt omega seed) (stoppedAt_le omega seed)
      (history omega seed) (output omega seed)
  history_query_eq : ∀ omega seed (i : Fin (stoppedAt omega seed)),
    ((history omega seed) i).1.1 =
      (simulation seed).query
        ⟨i.1, Nat.lt_of_lt_of_le i.2 (stoppedAt_le omega seed)⟩ omega
  output_eq : ∀ omega seed,
    (output omega seed).1 = (simulation seed).output omega
  actual_run : ∀ omega seed,
    ∃ n, ∃ hn : n ≤ N,
      ∃ history : OracleHistory (Metric.closedBall (0 : E) R)
          (SymmetricExactJet E p) n,
        policy.IsUnpaddedRun (actualOracle omega).answer seed n hn history
          (actualOutput omega seed)
  actualOutput_eq_on_slab : ∀ omega seed,
    omega ∈ randomSlabEvent prior (simulation seed) →
      actualOutput omega seed = output omega seed
  joint_slab_measurable : @MeasurableSet (prior.Omega × policy.Seed)
    (MeasurableSpace.prod prior.measurableSpace policy.seedMeasurable)
    {z : prior.Omega × policy.Seed |
      z.1 ∈ randomSlabEvent prior (simulation z.2)}

attribute [instance] BorelStoppingPolicy.seedMeasurable
attribute [instance] BorelStoppingPolicy.seedProbability

/-- On the slab event the simulated stopped prefix is an actual execution of
the same Borel policy against the single exact oracle of the final hidden
operator, with exactly the same saved output. -/
theorem BorelRandomExecution.actual_run_on_slab
    {prior : SequentialFramePrior E N d R}
    {p : ℕ} {hp : 2 ≤ p} {profile : GateProfile}
    {Lp : ℝ} {hLp : 0 < Lp} {hR : 0 < R}
    {policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E p) (Metric.closedBall (0 : E) R) N}
    (exec : BorelRandomExecution prior p hp profile Lp hLp hR policy)
    (omega : prior.Omega) (seed : policy.Seed)
    (hslab : omega ∈ randomSlabEvent prior (exec.simulation seed)) :
    policy.IsUnpaddedRun (exec.actualOracle omega).answer seed
      (exec.stoppedAt omega seed) (exec.stoppedAt_le omega seed)
      (exec.history omega seed) (exec.output omega seed) := by
  apply (exec.stage_run omega seed).to_fixedOracle
  intro i
  let t : Fin N :=
    ⟨i.1, Nat.lt_of_lt_of_le i.2 (exec.stoppedAt_le omega seed)⟩
  have hjet := truncatedHiddenOperator_fullJetCoupledAt_of_slab p profile Lp hR
    N t.1 (prior.frame omega) ((exec.simulation seed).query t omega)
    (fun j hj => randomSlabEvent_query_slab (exec.simulation seed) hslab t j hj)
  have hanswer :=
    (exec.stageOracle omega t).answer_eq_of_fullJetCoupledAt
      (exec.actualOracle omega) hjet
  have hquery := exec.history_query_eq omega seed i
  simpa only [ballVIData, t, hquery] using hanswer

/-- Fixed-cap padding is a transcript representation of the just-proved
actual unpadded run.  It retains exactly `exec.output`; no post-stop policy
rule or oracle call is used by the unpadded execution. -/
theorem BorelRandomExecution.exists_padded_actual_run_on_slab
    {prior : SequentialFramePrior E N d R}
    {p : ℕ} {hp : 2 ≤ p} {profile : GateProfile}
    {Lp : ℝ} {hLp : 0 < Lp} {hR : 0 < R}
    {policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E p) (Metric.closedBall (0 : E) R) N}
    (exec : BorelRandomExecution prior p hp profile Lp hLp hR policy)
    (omega : prior.Omega) (seed : policy.Seed)
    (hslab : omega ∈ randomSlabEvent prior (exec.simulation seed))
    (fill : Metric.closedBall (0 : E) R) :
    ∃ paddedHistory : OracleHistory (Metric.closedBall (0 : E) R)
        (SymmetricExactJet E p) N,
      policy.IsPaddedRun (exec.actualOracle omega).answer seed
        paddedHistory (exec.output omega seed) := by
  apply (policy.unpadded_iff_padded (exec.actualOracle omega).answer seed fill
    (exec.output omega seed)).mp
  exact ⟨exec.stoppedAt omega seed, exec.stoppedAt_le omega seed,
    exec.history omega seed, exec.actual_run_on_slab omega seed hslab⟩

/-- A concrete Borel exact-oracle simulation instantiates the probability
layer's `SeededRandomRun`; the returned companion theorem records that its
saved output really belongs to an unpadded run of the original policy. -/
noncomputable def BorelRandomExecution.toSeededRandomRun
    {prior : SequentialFramePrior E N d R}
    {p : ℕ} {hp : 2 ≤ p} {profile : GateProfile}
    {Lp : ℝ} {hLp : 0 < Lp} {hR : 0 < R}
    {policy : BorelStoppingPolicy
      (Answer := SymmetricExactJet E p) (Metric.closedBall (0 : E) R) N}
    (exec : BorelRandomExecution prior p hp profile Lp hLp hR policy)
    (hN : 1 ≤ N) : SeededRandomRun prior p hp profile Lp hLp hR where
  Seed := policy.Seed
  seedMeasurableSpace := policy.seedMeasurable
  seedMeasure := policy.seedMeasure
  seedProbability := policy.seedProbability
  simulation := exec.simulation
  truncatedOperator := fun _seed t omega =>
    truncatedHiddenOperator p profile Lp R N t.1 (prior.frame omega)
  actualOutput := fun omega seed => (exec.actualOutput omega seed).1
  budget_pos := hN
  actualOutput_feasible := fun omega seed => by
    have hm := (exec.actualOutput omega seed).2
    simpa only [Metric.mem_closedBall, dist_zero_right] using hm
  full_jet_coupling := by
    intro omega seed hslab t
    exact (truncatedHiddenOperator_fullJetCoupledAt_of_slab p profile Lp hR
      N t.1 (prior.frame omega) ((exec.simulation seed).query t omega)
      (fun i hi => randomSlabEvent_query_slab
        (exec.simulation seed) hslab t i hi)).symm
  saved_output_coupling := by
    intro omega seed hslab
    rw [exec.actualOutput_eq_on_slab omega seed hslab, exec.output_eq]
  joint_slab_measurable := exec.joint_slab_measurable

end BorelBridge

end LeanArticleAudit.Pilot
