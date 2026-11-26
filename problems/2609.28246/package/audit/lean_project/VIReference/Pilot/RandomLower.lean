import VIReference.Pilot.Residual
import VIReference.Pilot.Sphere
import VIReference.Pilot.Execution
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Random-frame lower-bound infrastructure

This file formalizes the probability and quantifier-management part of
`thm:random`.  Mathlib does not currently provide a normalized Haar measure on
real Stiefel manifolds together with the sequential conditional-sphere law.
Accordingly, that one geometric input is exposed as the field
`SequentialFramePrior.adapted_slab_tail`; every subsequent union-bound,
fixed-seed, product-measure, and fixed-frame averaging step is kernel proved.
-/

open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace VIReference.Pilot

section Dimension

/-- The dimension hypothesis in equation `eq:random-dimension`. -/
def RandomDimensionCondition (N d : ℕ) (delta : ℝ) : Prop :=
  let m : ℝ := hiddenM N
  d ≥ hiddenM N + Nat.ceil (2048 * m ^ 3 * Real.log (2 * (m ^ 2 + 1) / delta))

/-- The one-event upper bound after inserting
`tau=R/(16 m^(3/2))` and threshold `tau/2`. -/
noncomputable def randomSingleBadReal (N d : ℕ) : ℝ :=
  2 * Real.exp (-((d - hiddenM N : ℕ) : ℝ) /
    (2048 * (hiddenM N : ℝ) ^ 3))

/-- The dimension condition makes the paper's loose union bound, over at most
`m^2+1` events, no larger than `delta`. -/
theorem random_dimension_controls_union {N d : ℕ} {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdim : RandomDimensionCondition N d delta) :
    ((hiddenM N : ℝ) ^ 2 + 1) * randomSingleBadReal N d ≤ delta := by
  let m : ℝ := hiddenM N
  let A : ℝ := 2 * (m ^ 2 + 1) / delta
  have hm0 : 0 < m := by
    dsimp [m]
    exact_mod_cast hiddenM_pos N
  have hA1 : 1 < A := by
    dsimp [A]
    have hm1 : 1 ≤ m := by
      dsimp [m]
      exact_mod_cast hiddenM_pos N
    have hm_sq : 1 ≤ m ^ 2 := by nlinarith
    have hnum : 2 < 2 * (m ^ 2 + 1) := by nlinarith
    apply (lt_div_iff₀ hdelta0).2
    nlinarith
  have hlog0 : 0 < Real.log A := Real.log_pos hA1
  have hceil : 2048 * m ^ 3 * Real.log A ≤
      (Nat.ceil (2048 * m ^ 3 * Real.log A) : ℝ) := Nat.le_ceil _
  have hdm : hiddenM N ≤ d := by
    dsimp [RandomDimensionCondition] at hdim
    omega
  have hdimR : (Nat.ceil (2048 * m ^ 3 * Real.log A) : ℝ) ≤
      ((d - hiddenM N : ℕ) : ℝ) := by
    have hdim' : d ≥ hiddenM N +
        Nat.ceil (2048 * m ^ 3 * Real.log A) := by
      simpa [RandomDimensionCondition, m, A] using hdim
    exact_mod_cast (show Nat.ceil (2048 * m ^ 3 * Real.log A) ≤
      d - hiddenM N by omega)
  have hden0 : 0 < 2048 * m ^ 3 := by positivity
  have hexpArg :
      -((d - hiddenM N : ℕ) : ℝ) / (2048 * m ^ 3) ≤ -Real.log A := by
    apply (div_le_iff₀ hden0).2
    nlinarith
  have hexp : Real.exp
      (-((d - hiddenM N : ℕ) : ℝ) / (2048 * m ^ 3)) ≤ 1 / A := by
    calc
      Real.exp (-((d - hiddenM N : ℕ) : ℝ) / (2048 * m ^ 3)) ≤
          Real.exp (-Real.log A) := Real.exp_le_exp.mpr hexpArg
      _ = 1 / A := by
        rw [Real.exp_neg, Real.exp_log (lt_trans (by norm_num) hA1)]
        simp [one_div]
  have hfac0 : 0 ≤ 2 * (m ^ 2 + 1) := by positivity
  change (m ^ 2 + 1) *
      (2 * Real.exp (-((d - hiddenM N : ℕ) : ℝ) / (2048 * m ^ 3))) ≤ delta
  calc
    (m ^ 2 + 1) *
        (2 * Real.exp (-((d - hiddenM N : ℕ) : ℝ) / (2048 * m ^ 3))) =
        (2 * (m ^ 2 + 1)) *
          Real.exp (-((d - hiddenM N : ℕ) : ℝ) / (2048 * m ^ 3)) := by ring
    _ ≤ (2 * (m ^ 2 + 1)) * (1 / A) :=
      mul_le_mul_of_nonneg_left hexp hfac0
    _ = delta := by
      dsimp [A]
      field_simp

theorem randomSingleBadReal_nonneg (N d : ℕ) :
    0 ≤ randomSingleBadReal N d := by
  rw [randomSingleBadReal]
  positivity

/-- Exact arithmetic behind the constant `2048`: applying `lem:sphere` at
threshold `tau/2` turns `k a^2/(2R^2)` into `k/(2048m^3)`. -/
theorem hiddenTau_slab_exponent (N k : ℕ) {R : ℝ} (hR : 0 < R) :
    (k : ℝ) * (hiddenTau R N / 2) ^ 2 / (2 * R ^ 2) =
      (k : ℝ) / (2048 * (hiddenM N : ℝ) ^ 3) := by
  have hm0 : (0 : ℝ) < hiddenM N := by exact_mod_cast hiddenM_pos N
  have hsqrt : Real.sqrt (hiddenM N : ℝ) ^ 2 = hiddenM N :=
    Real.sq_sqrt hm0.le
  rw [hiddenTau, hiddenC]
  field_simp [hR.ne', hm0.ne', Real.sqrt_ne_zero'.mpr hm0]
  nlinarith

end Dimension

section FiniteEvents

variable {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]

/-- Simultaneous occurrence of a finite family of good events. -/
def allGoodEvent (good : I → Set Omega) : Set Omega := ⋂ i, good i

theorem measurableSet_allGoodEvent {good : I → Set Omega}
    (hgood : ∀ i, MeasurableSet (good i)) : MeasurableSet (allGoodEvent good) := by
  exact MeasurableSet.iInter hgood

/-- Finite union bound, stated as a bound on failure of the simultaneous-good
event.  No independence assumptions are used. -/
theorem measure_compl_allGoodEvent_le (mu : Measure Omega) (good : I → Set Omega) :
    mu (allGoodEvent good)ᶜ ≤ ∑ i, mu (good i)ᶜ := by
  rw [allGoodEvent, compl_iInter]
  exact measure_iUnion_fintype_le mu fun i => (good i)ᶜ

theorem measure_compl_allGoodEvent_le_card_mul (mu : Measure Omega)
    (good : I → Set Omega) (b : ℝ≥0∞)
    (hbad : ∀ i, mu (good i)ᶜ ≤ b) :
    mu (allGoodEvent good)ᶜ ≤ Fintype.card I * b := by
  calc
    mu (allGoodEvent good)ᶜ ≤ ∑ i, mu (good i)ᶜ :=
      measure_compl_allGoodEvent_le mu good
    _ ≤ ∑ _i : I, b := Finset.sum_le_sum fun i _ => hbad i
    _ = Fintype.card I * b := by simp

end FiniteEvents

section SequentialPrior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A probe depends only on the first `t` columns of a random frame.  This is
the precise non-probabilistic adaptation condition used in the source proof;
it avoids conditioning on previously selected success events. -/
def DependsOnlyOnFramePrefix {Omega : Type*} {m : ℕ}
    (frame : Omega → Fin m → E) (t : ℕ) (x : Omega → E) : Prop :=
  ∀ omega omega',
    (∀ j : Fin m, j.1 < t → frame omega j = frame omega' j) →
      x omega = x omega'

/-- Contract for the uniform random Stiefel frame used by `thm:random`.

The final field is exactly the consequence of the conditional spherical law
and `lem:sphere` needed below.  Its explicit presence records the only missing
mathlib construction instead of hiding it behind an axiom. -/
structure SequentialFramePrior (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (N d : ℕ) (R : ℝ) where
  Omega : Type
  measurableSpace : MeasurableSpace Omega
  measure : @Measure Omega measurableSpace
  probability : @IsProbabilityMeasure Omega measurableSpace measure
  frame : Omega → Fin (hiddenM N) → E
  orthonormal : ∀ omega, Orthonormal ℝ (frame omega)
  adapted_slab_tail :
    ∀ (t : ℕ) (ht : t ≤ hiddenM N) (i : Fin (hiddenM N)) (hti : t ≤ i.1)
      (x : Omega → E),
      Measurable (fun omega => inner ℝ (frame omega i) (x omega)) →
      DependsOnlyOnFramePrefix frame t x →
      (∀ omega, ‖x omega‖ ≤ R) →
      MeasurableSet {omega | |inner ℝ (frame omega i) (x omega)| >
        hiddenTau R N / 2} →
      measure {omega | |inner ℝ (frame omega i) (x omega)| >
        hiddenTau R N / 2} ≤ ENNReal.ofReal (randomSingleBadReal N d)

attribute [instance] SequentialFramePrior.measurableSpace
attribute [instance] SequentialFramePrior.probability

/-- Rectangular event index.  Pairs with `i<t` are harmless copies of `univ`;
the valid pairs contain all source events `E_(t,i)`.  The extra copies make the
cardinality exactly `N^2+1`, still below the paper's `m^2+1` budget. -/
abbrev RandomSlabIndex (N : ℕ) := (Fin N × Fin N) ⊕ Unit

/-- Fixed-seed simulated run data.  Query `t` sees only frame columns `<t`, and
the saved output sees only the first `N` columns, including for padded
early-stopped executions. -/
structure FixedSeedSimulation (prior : SequentialFramePrior E N d R) where
  query : Fin N → prior.Omega → E
  output : prior.Omega → E
  query_projection_measurable : ∀ (t i : Fin N),
    Measurable (fun omega => inner ℝ (prior.frame omega i.castSucc)
      (query t omega))
  output_projection_measurable :
    Measurable (fun omega => inner ℝ (prior.frame omega (Fin.last N))
      (output omega))
  query_prefix : ∀ t, DependsOnlyOnFramePrefix prior.frame t.1 (query t)
  output_prefix : DependsOnlyOnFramePrefix prior.frame N output
  query_feasible : ∀ t omega, ‖query t omega‖ ≤ R
  output_feasible : ∀ omega, ‖output omega‖ ≤ R
  query_slab_measurable : ∀ (t i : Fin N),
    MeasurableSet {omega | |inner ℝ (prior.frame omega i.castSucc)
      (query t omega)| ≤ hiddenTau R N / 2}
  output_slab_measurable :
    MeasurableSet {omega | |inner ℝ (prior.frame omega (Fin.last N))
      (output omega)| ≤ hiddenTau R N / 2}

/-- The source event family for one fixed algorithm seed. -/
def randomSlabGood (prior : SequentialFramePrior E N d R)
    (sim : FixedSeedSimulation prior) : RandomSlabIndex N → Set prior.Omega
  | Sum.inl (t, i) =>
      if t.1 ≤ i.1 then
        {omega | |inner ℝ (prior.frame omega i.castSucc) (sim.query t omega)| ≤
          hiddenTau R N / 2}
      else Set.univ
  | Sum.inr _ =>
      {omega | |inner ℝ (prior.frame omega (Fin.last N)) (sim.output omega)| ≤
        hiddenTau R N / 2}

def randomSlabEvent (prior : SequentialFramePrior E N d R)
    (sim : FixedSeedSimulation prior) : Set prior.Omega :=
  allGoodEvent (randomSlabGood prior sim)

theorem measurableSet_randomSlabGood (prior : SequentialFramePrior E N d R)
    (sim : FixedSeedSimulation prior) (idx : RandomSlabIndex N) :
    MeasurableSet (randomSlabGood prior sim idx) := by
  rcases idx with ti | u
  · rcases ti with ⟨t, i⟩
    simp only [randomSlabGood]
    split
    · exact sim.query_slab_measurable t i
    · exact MeasurableSet.univ
  · exact sim.output_slab_measurable

theorem measurableSet_randomSlabEvent (prior : SequentialFramePrior E N d R)
    (sim : FixedSeedSimulation prior) : MeasurableSet (randomSlabEvent prior sim) :=
  measurableSet_allGoodEvent (measurableSet_randomSlabGood prior sim)

theorem randomSlabGood_bad_le (prior : SequentialFramePrior E N d R)
    (sim : FixedSeedSimulation prior) (idx : RandomSlabIndex N) :
    prior.measure (randomSlabGood prior sim idx)ᶜ ≤
      ENNReal.ofReal (randomSingleBadReal N d) := by
  rcases idx with ti | u
  · rcases ti with ⟨t, i⟩
    simp only [randomSlabGood]
    split_ifs with hti
    · rw [show {omega | |inner ℝ (prior.frame omega i.castSucc)
          (sim.query t omega)| ≤ hiddenTau R N / 2}ᶜ =
          {omega | |inner ℝ (prior.frame omega i.castSucc)
            (sim.query t omega)| > hiddenTau R N / 2} by ext; simp]
      have hmeas : MeasurableSet
          {omega | |inner ℝ (prior.frame omega i.castSucc)
            (sim.query t omega)| > hiddenTau R N / 2} := by
        convert (sim.query_slab_measurable t i).compl using 1 <;> ext omega <;> simp
      exact prior.adapted_slab_tail t.1 (by simp [hiddenM]; omega)
        i.castSucc hti (sim.query t) (sim.query_projection_measurable t i)
        (sim.query_prefix t)
        (sim.query_feasible t) hmeas
    · simp
  · simp only [randomSlabGood]
    rw [show {omega | |inner ℝ (prior.frame omega (Fin.last N))
        (sim.output omega)| ≤ hiddenTau R N / 2}ᶜ =
        {omega | |inner ℝ (prior.frame omega (Fin.last N))
          (sim.output omega)| > hiddenTau R N / 2} by ext; simp]
    have hmeas : MeasurableSet
        {omega | |inner ℝ (prior.frame omega (Fin.last N))
          (sim.output omega)| > hiddenTau R N / 2} := by
      convert sim.output_slab_measurable.compl using 1 <;> ext omega <;> simp
    exact prior.adapted_slab_tail N (by simp [hiddenM]) (Fin.last N) (by simp)
      sim.output sim.output_projection_measurable sim.output_prefix sim.output_feasible
      hmeas

theorem randomSlabEvent_failure_le (prior : SequentialFramePrior E N d R)
    (sim : FixedSeedSimulation prior) :
    prior.measure (randomSlabEvent prior sim)ᶜ ≤
      Fintype.card (RandomSlabIndex N) *
        ENNReal.ofReal (randomSingleBadReal N d) :=
  measure_compl_allGoodEvent_le_card_mul prior.measure (randomSlabGood prior sim)
    _ (randomSlabGood_bad_le prior sim)

@[simp] theorem card_randomSlabIndex (N : ℕ) :
    Fintype.card (RandomSlabIndex N) = N ^ 2 + 1 := by
  simp [RandomSlabIndex, pow_two]

theorem randomSlabEvent_failure_le_delta
    (prior : SequentialFramePrior E N d R) (sim : FixedSeedSimulation prior)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdim : RandomDimensionCondition N d delta) :
    prior.measure (randomSlabEvent prior sim)ᶜ ≤ ENNReal.ofReal delta := by
  have hreal := random_dimension_controls_union hdelta0 hdelta1 hdim
  have hNm : (N : ℝ) ≤ hiddenM N := by
    simp [hiddenM]
  have hcount : (N : ℝ) ^ 2 + 1 ≤ (hiddenM N : ℝ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (hiddenM N : ℝ), sq_nonneg (N : ℝ)]
  have hbad0 := randomSingleBadReal_nonneg N d
  have hsmall : ((N : ℝ) ^ 2 + 1) * randomSingleBadReal N d ≤ delta :=
    (mul_le_mul_of_nonneg_right hcount hbad0).trans hreal
  calc
    prior.measure (randomSlabEvent prior sim)ᶜ ≤
        Fintype.card (RandomSlabIndex N) *
          ENNReal.ofReal (randomSingleBadReal N d) :=
      randomSlabEvent_failure_le prior sim
    _ = ENNReal.ofReal (((N : ℝ) ^ 2 + 1) * randomSingleBadReal N d) := by
      rw [card_randomSlabIndex]
      rw [← ENNReal.ofReal_natCast (N ^ 2 + 1),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (N ^ 2 + 1))]
      congr 2
      norm_num [pow_two]
    _ ≤ ENNReal.ofReal delta := ENNReal.ofReal_le_ofReal hsmall

/-- Probability form of the fixed-seed union bound. -/
theorem randomSlabEvent_probability_ge
    (prior : SequentialFramePrior E N d R) (sim : FixedSeedSimulation prior)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdim : RandomDimensionCondition N d delta) :
    ENNReal.ofReal (1 - delta) ≤ prior.measure (randomSlabEvent prior sim) := by
  have hfail := randomSlabEvent_failure_le_delta prior sim hdelta0 hdelta1 hdim
  have hmeas := measurableSet_randomSlabEvent prior sim
  have hsum := measure_add_measure_compl (μ := prior.measure) hmeas
  rw [measure_univ] at hsum
  have hdelta_le : ENNReal.ofReal delta ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hdelta1.le
  have hone_sub : ENNReal.ofReal (1 - delta) = 1 - ENNReal.ofReal delta := by
    rw [ENNReal.ofReal_sub 1 hdelta0.le]
    simp
  rw [hone_sub]
  have hevent : prior.measure (randomSlabEvent prior sim) =
      1 - prior.measure (randomSlabEvent prior sim)ᶜ := by
    exact ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) hsum
  rw [hevent]
  exact tsub_le_tsub_left hfail 1

end SequentialPrior

section Averaging

variable {Frame Seed : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
  (muFrame : Measure Frame) (muSeed : Measure Seed)
  [IsProbabilityMeasure muFrame] [IsProbabilityMeasure muSeed]

/-- Integrating fixed-seed success probabilities gives the joint success
probability. -/
theorem joint_probability_ge_of_seedwise {G : Set (Frame × Seed)}
    (hG : MeasurableSet G) (alpha : ℝ≥0∞)
    (hseed : ∀ seed, alpha ≤ muFrame {frame | (frame, seed) ∈ G}) :
    alpha ≤ (muFrame.prod muSeed) G := by
  rw [Measure.prod_apply_symm hG]
  calc
    alpha = ∫⁻ _seed : Seed, alpha ∂muSeed := by simp
    _ ≤ ∫⁻ seed, muFrame {frame | (frame, seed) ∈ G} ∂muSeed :=
      lintegral_mono hseed

/-- Averaging over frames selects one fixed frame whose conditional success
probability is at least the joint success probability. -/
theorem exists_fixed_frame_probability_ge_joint {G : Set (Frame × Seed)}
    (hG : MeasurableSet G) :
    ∃ frame, (muFrame.prod muSeed) G ≤ muSeed {seed | (frame, seed) ∈ G} := by
  have hfinite :
      (∫⁻ frame, muSeed {seed | (frame, seed) ∈ G} ∂muFrame) ≠ ∞ := by
    change (∫⁻ frame, muSeed (Prod.mk frame ⁻¹' G) ∂muFrame) ≠ ∞
    rw [← Measure.prod_apply hG]
    exact measure_ne_top _ _
  rw [Measure.prod_apply hG]
  apply exists_lintegral_le
  exact hfinite

theorem exists_fixed_frame_of_seedwise {G : Set (Frame × Seed)}
    (hG : MeasurableSet G) (alpha : ℝ≥0∞)
    (hseed : ∀ seed, alpha ≤ muFrame {frame | (frame, seed) ∈ G}) :
    ∃ frame, alpha ≤ muSeed {seed | (frame, seed) ∈ G} := by
  have hjoint := joint_probability_ge_of_seedwise muFrame muSeed hG alpha hseed
  rcases exists_fixed_frame_probability_ge_joint muFrame muSeed hG with ⟨frame, hframe⟩
  exact ⟨frame, hjoint.trans hframe⟩

end Averaging

section RandomizedLowerCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- Equality of the complete order-`p` returned tensors at one query.  This is
stronger than equality after applying derivatives to previously chosen
directions. -/
def FullJetCoupledAt (p : ℕ) (F G : E → E) (x : E) : Prop :=
  exactJet p F x = exactJet p G x

theorem fullJetCoupledAt_iff (p : ℕ) (F G : E → E) (x : E) :
    FullJetCoupledAt p F G x ↔
      ∀ j : Fin p, iteratedFDeriv ℝ j.1 F x = iteratedFDeriv ℝ j.1 G x := by
  simp only [FullJetCoupledAt, exactJet, funext_iff]

/-- Exact residual threshold in `eq:hard-residual`, in the parameterization
used by the hidden operator. -/
noncomputable def randomResidualThreshold (p : ℕ) (profile : GateProfile)
    (Lp R : ℝ) (N : ℕ) : ℝ :=
  hiddenLambda p profile Lp R N * R / (8 * (hiddenM N : ℝ))

theorem randomResidualThreshold_eq_closedForm (p : ℕ) (hp : 1 ≤ p)
    (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R) (N : ℕ) :
    randomResidualThreshold p profile Lp R N =
      hiddenResidualClosedForm p profile Lp R N :=
  hidden_residual_scale_eq p hp profile Lp hR N

/-- A seeded simulated execution together with the transcript-coupling
certificate used in the source proof.

`full_jet_coupling` records equality of every returned tensor at every query
on the slab event.  `saved_output_coupling` separately records the consequence
for the output retained by a possibly early-stopped padded run.  The final
The slab-to-residual implication is not a field: it is proved below directly
from `hidden_tangentResidual_lower`. -/
structure SeededRandomRun
    (prior : SequentialFramePrior E N d R)
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (hR : 0 < R) where
  Seed : Type
  seedMeasurableSpace : MeasurableSpace Seed
  seedMeasure : @Measure Seed seedMeasurableSpace
  seedProbability : @IsProbabilityMeasure Seed seedMeasurableSpace seedMeasure
  simulation : Seed → FixedSeedSimulation prior
  truncatedOperator : Seed → Fin N → prior.Omega → (E → E)
  actualOutput : prior.Omega → Seed → E
  budget_pos : 1 ≤ N
  actualOutput_feasible : ∀ omega seed, ‖actualOutput omega seed‖ ≤ R
  full_jet_coupling : ∀ omega seed,
    omega ∈ randomSlabEvent prior (simulation seed) →
      ∀ t : Fin N,
        FullJetCoupledAt p
          (hiddenOperator p profile Lp R N (prior.frame omega))
          (truncatedOperator seed t omega) ((simulation seed).query t omega)
  saved_output_coupling : ∀ omega seed,
    omega ∈ randomSlabEvent prior (simulation seed) →
      actualOutput omega seed = (simulation seed).output omega
  joint_slab_measurable : MeasurableSet
    {z : prior.Omega × Seed |
      z.1 ∈ randomSlabEvent prior (simulation z.2)}

attribute [instance] SeededRandomRun.seedMeasurableSpace
attribute [instance] SeededRandomRun.seedProbability

def randomJointSlabEvent (prior : SequentialFramePrior E N d R)
    {p : ℕ} {hp : 2 ≤ p} {profile : GateProfile} {Lp : ℝ}
    {hLp : 0 < Lp} {hR : 0 < R}
    (run : SeededRandomRun prior p hp profile Lp hLp hR) :
    Set (prior.Omega × run.Seed) :=
  {z | z.1 ∈ randomSlabEvent prior (run.simulation z.2)}

def randomHardEvent (prior : SequentialFramePrior E N d R)
    {p : ℕ} {hp : 2 ≤ p} {profile : GateProfile} {Lp : ℝ}
    {hLp : 0 < Lp} {hR : 0 < R}
    (run : SeededRandomRun prior p hp profile Lp hLp hR) :
    Set (prior.Omega × run.Seed) :=
  {z | randomResidualThreshold p profile Lp R N ≤
    tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
      (hiddenOperator p profile Lp R N (prior.frame z.1))
      (run.actualOutput z.1 z.2)}

theorem randomJointSlabEvent_measurable
    (prior : SequentialFramePrior E N d R)
    {p : ℕ} {hp : 2 ≤ p} {profile : GateProfile} {Lp : ℝ}
    {hLp : 0 < Lp} {hR : 0 < R}
    (run : SeededRandomRun prior p hp profile Lp hLp hR) :
    MeasurableSet (randomJointSlabEvent prior run) :=
  run.joint_slab_measurable

theorem randomJointSlabEvent_subset_hard
    (prior : SequentialFramePrior E N d R)
    {p : ℕ} {hp : 2 ≤ p} {profile : GateProfile} {Lp : ℝ}
    {hLp : 0 < Lp} {hR : 0 < R}
    (run : SeededRandomRun prior p hp profile Lp hLp hR) :
    randomJointSlabEvent prior run ⊆ randomHardEvent prior run := by
  intro z hz
  have houtGood : z.1 ∈ randomSlabGood prior (run.simulation z.2) (Sum.inr ()) :=
    Set.mem_iInter.mp hz (Sum.inr ())
  have hslabSim : |inner ℝ (prior.frame z.1 (Fin.last N))
      ((run.simulation z.2).output z.1)| ≤ hiddenTau R N / 2 := by
    simpa [randomSlabGood] using houtGood
  have houtput := run.saved_output_coupling z.1 z.2 hz
  have hslab : |inner ℝ (prior.frame z.1 (Fin.last N))
      (run.actualOutput z.1 z.2)| ≤ hiddenTau R N / 2 := by
    rw [houtput]
    exact hslabSim
  have hx : run.actualOutput z.1 z.2 ∈ Metric.closedBall (0 : E) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact run.actualOutput_feasible z.1 z.2
  exact hidden_tangentResidual_lower p hp profile hLp hR run.budget_pos
    (prior.frame z.1) (prior.orthonormal z.1) (run.actualOutput z.1 z.2) hx hslab

/-- The source's fixed-seed statement: every deterministic seed sees a random
frame hard with probability at least `1-delta`. -/
theorem randomHard_probability_ge_fixed_seed
    (prior : SequentialFramePrior E N d R)
    {p : ℕ} {hp : 2 ≤ p} {profile : GateProfile} {Lp : ℝ}
    {hLp : 0 < Lp} {hR : 0 < R}
    (run : SeededRandomRun prior p hp profile Lp hLp hR)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdim : RandomDimensionCondition N d delta) (seed : run.Seed) :
    ENNReal.ofReal (1 - delta) ≤
      prior.measure {omega | (omega, seed) ∈ randomHardEvent prior run} := by
  have hslab := randomSlabEvent_probability_ge prior (run.simulation seed)
    hdelta0 hdelta1 hdim
  apply hslab.trans
  apply measure_mono
  intro omega homega
  exact randomJointSlabEvent_subset_hard prior run homega

/-- Joint frame/seed probability and the fixed-frame averaging conclusion of
`thm:random`. -/
theorem randomLower_probability_core
    (prior : SequentialFramePrior E N d R)
    {p : ℕ} {hp : 2 ≤ p} {profile : GateProfile} {Lp : ℝ}
    {hLp : 0 < Lp} {hR : 0 < R}
    (run : SeededRandomRun prior p hp profile Lp hLp hR)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdim : RandomDimensionCondition N d delta) :
    ENNReal.ofReal (1 - delta) ≤
        (prior.measure.prod run.seedMeasure) (randomJointSlabEvent prior run) ∧
      ∃ omega, ENNReal.ofReal (1 - delta) ≤
        run.seedMeasure {seed | (omega, seed) ∈ randomJointSlabEvent prior run} := by
  have hseed : ∀ seed, ENNReal.ofReal (1 - delta) ≤
      prior.measure {omega | (omega, seed) ∈ randomJointSlabEvent prior run} := by
    intro seed
    exact randomSlabEvent_probability_ge prior (run.simulation seed)
      hdelta0 hdelta1 hdim
  have hjoint := joint_probability_ge_of_seedwise prior.measure run.seedMeasure
    (randomJointSlabEvent_measurable prior run) (ENNReal.ofReal (1 - delta)) hseed
  refine ⟨hjoint, ?_⟩
  exact exists_fixed_frame_of_seedwise prior.measure run.seedMeasure
    (randomJointSlabEvent_measurable prior run) (ENNReal.ofReal (1 - delta)) hseed

/-- Auditable *conditional* headline contract for the probability-theoretic
core of `thm:random`.  The only remaining upstream obligations are:

1. construct the uniform Stiefel `SequentialFramePrior` and prove its
   sequential adapted-slab tail from `lem:sphere`;
2. instantiate `SeededRandomRun` from the Borel exact-oracle execution,
   including complete-jet transcript equality, saved-output equality, and the
   two joint-event measurability proofs.

The slab-to-residual step itself is already discharged from `lem:residual`. -/
def ConditionalRandomLowerCoreClaim : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
    (Lp : ℝ) (hLp : 0 < Lp) (R : ℝ) (hR : 0 < R)
    (N d : ℕ) (prior : SequentialFramePrior E N d R)
    (run : SeededRandomRun prior p hp profile Lp hLp hR)
    (delta : ℝ), 0 < delta → delta < 1 →
      RandomDimensionCondition N d delta →
      ENNReal.ofReal (1 - delta) ≤
          (prior.measure.prod run.seedMeasure) (randomJointSlabEvent prior run) ∧
        ∃ omega, ENNReal.ofReal (1 - delta) ≤
          run.seedMeasure {seed | (omega, seed) ∈ randomJointSlabEvent prior run}

theorem conditionalRandomLowerCoreClaim_proof : ConditionalRandomLowerCoreClaim := by
  intro E _ _ _ _ p hp profile Lp hLp R hR N d prior run delta
    hdelta0 hdelta1 hdim
  exact randomLower_probability_core prior run hdelta0 hdelta1 hdim

end RandomizedLowerCore

end VIReference.Pilot
