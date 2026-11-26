import MinimaxAudit.Deterministic
import VIReference.Pilot.BorelRunner

/-!
A concrete adapter from the source's list-history scalar policies to the
already-kernel-checked generic Borel early-stopping runner. The adapter proves
measurability from Model's canonical history sigma algebra, and exposes
feasible queries/output, prefix dependence, and exact-answer coupling.
-/
open Set MeasureTheory
namespace MinimaxAudit.MeasurableExecution
open VIReference.Pilot
open VIReference.Pilot.BorelStoppingPolicy

noncomputable section
variable {p dx dy N : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}

abbrev ScalarAnswer := ScalarJet p (SaddleSpace dx dy)
abbrev FiniteHistory (X : Set (Primal dx)) (Y : Set (Dual dy)) (n : ℕ) :=
  OracleHistory (productDomain X Y) (ScalarJet p (SaddleSpace dx dy)) n

/-- Forget subtype feasibility proofs while preserving every returned jet. -/
def finiteHistoryList {n : ℕ} (h : FiniteHistory (p := p) X Y n) : ScalarHistory p dx dy :=
  List.ofFn (fun i => ((h i).1.1, (h i).2))

@[simp] theorem finite_history_list_length {n : ℕ} (h : FiniteHistory (p := p) X Y n) :
    (finiteHistoryList h).length = n := by simp [finiteHistoryList]

/-- The canonical list sigma algebra accepts every fixed-length finite
history map; this is the key bridge from Model to the Borel runner. -/
theorem finite_history_list_measurable (n : ℕ) :
    Measurable (finiteHistoryList (p := p) (X := X) (Y := Y) (n := n)) := by
  change Measurable[_, MeasurableSpace.comap historyEncoding inferInstance] _
  apply measurable_comap_iff.2
  have henc : (historyEncoding ∘ finiteHistoryList (p := p) (X := X) (Y := Y) (n := n)) =
      (fun h => (⟨n, fun i => ((h i).1.1, (h i).2)⟩ :
        Σ n : ℕ, Fin n → SaddleSpace dx dy × ScalarJet p (SaddleSpace dx dy))) := by
    funext h
    simp [historyEncoding, finiteHistoryList]
    apply (Fin.heq_fun_iff (by simp)).2
    intro i
    rfl
  rw [henc]
  have hmk : Measurable (fun h : Fin n → SaddleSpace dx dy × ScalarJet p (SaddleSpace dx dy) =>
      (⟨n, h⟩ : Σ k : ℕ, Fin k → SaddleSpace dx dy × ScalarJet p (SaddleSpace dx dy))) :=
    by
      apply Measurable.of_le_map
      change (⨅ a : ℕ, MeasurableSpace.map (@Sigma.mk ℕ (fun k => Fin k → SaddleSpace dx dy × ScalarJet p (SaddleSpace dx dy)) a)
        (inferInstance : MeasurableSpace (Fin a → SaddleSpace dx dy × ScalarJet p (SaddleSpace dx dy)))) ≤ _
      exact iInf_le _ n
  apply hmk.comp
  apply measurable_pi_lambda
  intro i
  fun_prop

/-- A harmless fixed feasible point is used only when an Option is none. -/
def pickedQuery {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (seed : Seed) (h : ScalarHistory p dx dy) : productDomain X Y :=
  match hq : (A.policy seed).query h with
  | none => fill
  | some z => ⟨z, (A.policy seed).feasible_query h z hq⟩


@[simp] theorem picked_query_coe {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (seed : Seed) (h : ScalarHistory p dx dy) :
    (pickedQuery A fill seed h).1 =
      Sum.elim (fun _ : Unit => (fill : SaddleSpace dx dy)) id
        (optionPointEncoding ((A.policy seed).query h)) := by
  unfold pickedQuery
  split <;> rename_i hq <;> simp [optionPointEncoding, hq]

/-- One source policy action, after translating a fixed-index history. -/
def scalarAction {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (n : ℕ) (state : Seed × FiniteHistory (p := p) X Y n) : OracleAction (productDomain X Y) :=
  let h := finiteHistoryList state.2
  if (A.policy state.1).query h = none then
    Sum.inl ⟨(A.policy state.1).output h, (A.policy state.1).feasible_output h⟩
  else Sum.inr (pickedQuery A fill state.1 h)

/-- The translated action is jointly measurable in seed and history. -/
theorem scalar_action_measurable {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y) (n : ℕ) :
    Measurable (scalarAction A fill n) := by
  let input : Seed × FiniteHistory (p := p) X Y n → Seed × ScalarHistory p dx dy :=
    fun z => (z.1, finiteHistoryList z.2)
  have hinput : Measurable input :=
    measurable_fst.prodMk ((finite_history_list_measurable n).comp measurable_snd)
  have hq := A.measurable_query.comp hinput
  have ho := A.measurable_output.comp hinput
  have henc : Measurable (fun z : Seed × FiniteHistory (p := p) X Y n =>
      optionPointEncoding ((A.policy z.1).query (finiteHistoryList z.2))) :=
    (comap_measurable optionPointEncoding).comp hq
  have hnone : MeasurableSet {z : Seed × FiniteHistory (p := p) X Y n |
      (A.policy z.1).query (finiteHistoryList z.2) = none} := by
    convert henc (measurableSet_range_inl : MeasurableSet (Set.range (Sum.inl : Unit → Unit ⊕ SaddleSpace dx dy))) using 1
    ext z
    cases h : (A.policy z.1).query (finiteHistoryList z.2) <;> simp [optionPointEncoding, h]
  have houtput : Measurable (fun z : Seed × FiniteHistory (p := p) X Y n =>
      (⟨(A.policy z.1).output (finiteHistoryList z.2),
        (A.policy z.1).feasible_output _⟩ : productDomain X Y)) := ho.subtype_mk
  have hquery : Measurable (fun z : Seed × FiniteHistory (p := p) X Y n =>
      pickedQuery A fill z.1 (finiteHistoryList z.2)) := by
    apply Measurable.subtype_mk
    have hpick : Measurable (Sum.elim (fun _ : Unit => (fill : SaddleSpace dx dy)) id) :=
      measurable_fun_sum measurable_const measurable_id
    convert hpick.comp henc using 1
    funext z
    split <;> rename_i hq <;> simp [optionPointEncoding, hq]
  exact Measurable.ite hnone (measurable_inl.comp houtput) (measurable_inr.comp hquery)

/-- Every source randomized policy yields a genuine Borel stopping policy. -/
def toBorelPolicy {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y) :
    BorelStoppingPolicy (Answer := ScalarJet p (SaddleSpace dx dy)) (productDomain X Y) N where
  Seed := Seed
  seedMeasurable := inferInstance
  seedMeasure := mu
  seedProbability := A.probability
  rule n := scalarAction A fill n.1
  rule_measurable n := scalar_action_measurable A fill n.1
  cap_stops state := by
    have hcap := (A.policy state.1).cap (finiteHistoryList state.2) (by simp)
    refine ⟨⟨(A.policy state.1).output (finiteHistoryList state.2),
      (A.policy state.1).feasible_output _⟩, ?_⟩
    simp [scalarAction, hcap]

/-- Query actions of the adapter are exactly source Option queries. -/
theorem scalar_action_inr_iff {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    {n : ℕ} (seed : Seed) (h : FiniteHistory (p := p) X Y n) (q : productDomain X Y) :
    scalarAction A fill n (seed, h) = Sum.inr q ↔
      (A.policy seed).query (finiteHistoryList h) = some q.1 := by
  cases hq : (A.policy seed).query (finiteHistoryList h) <;>
    simp [scalarAction, hq, Subtype.ext_iff, picked_query_coe, optionPointEncoding]

/-- Stop actions preserve the source policy's arbitrary saved output. -/
theorem scalar_action_inl_iff {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    {n : ℕ} (seed : Seed) (h : FiniteHistory (p := p) X Y n) (out : productDomain X Y) :
    scalarAction A fill n (seed, h) = Sum.inl out ↔
      (A.policy seed).query (finiteHistoryList h) = none ∧
      (A.policy seed).output (finiteHistoryList h) = out.1 := by
  cases hq : (A.policy seed).query (finiteHistoryList h) <;>
    simp [scalarAction, hq, Subtype.ext_iff, picked_query_coe, optionPointEncoding]

/-- A finite-history restriction is exactly the corresponding list prefix. -/
theorem finite_history_list_restrict {n k : ℕ} (h : FiniteHistory (p := p) X Y n)
    (hk : k ≤ n) :
    finiteHistoryList (OracleHistory.restrict h hk) = (finiteHistoryList h).take k := by
  apply List.ext_getElem
  · simp [finiteHistoryList, hk]
  · intro i hi1 hi2
    simp only [finiteHistoryList, List.getElem_ofFn, List.getElem_take]
    rfl

/-- Exact Option-query semantics for a recorded list transcript. -/
theorem run_eq_of_recorded_list
    (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (entries : ScalarHistory p dx dy) (initialHist : ScalarHistory p dx dy)
    (out : SaddleSpace dx dy) (fuel : ℕ) (hlen : entries.length ≤ fuel)
    (hqueries : ∀ (i : ℕ) (hi : i < entries.length),
      A.query (initialHist ++ entries.take i) = some entries[i].1 ∧
      entries[i].2 = oracle entries[i].1)
    (hstop : A.query (initialHist ++ entries) = none)
    (hout : A.output (initialHist ++ entries) = out) :
    Deterministic.runScalarPolicy A oracle fuel initialHist = out := by
  induction entries generalizing initialHist fuel with
  | nil =>
    simp only [List.append_nil] at hstop hout
    cases fuel <;> simpa [Deterministic.runScalarPolicy, hstop] using hout
  | cons entry entries ih =>
    cases fuel with
    | zero => simp at hlen
    | succ fuel =>
      have hfirst := hqueries 0 (by simp)
      simp only [List.take_zero, List.append_nil, List.getElem_cons_zero] at hfirst
      simp only [Deterministic.runScalarPolicy, hfirst.1]
      have heq : (entry.1, oracle entry.1) = entry := by
        cases entry
        simp only [Prod.mk.injEq, true_and]
        exact hfirst.2.symm
      rw [heq]
      apply ih (initialHist ++ [entry]) fuel (by simpa using hlen)
      · intro i hi
        have hh := hqueries (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa [List.take_succ_cons, List.append_assoc] using hh
      · simpa [List.append_assoc] using hstop
      · simpa [List.append_assoc] using hout

/-- The generic runner's unpadded relation executes exactly the source
list-history Option policy, with the same saved output and call budget. -/
theorem source_run_eq_of_borel_unpadded
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy)) (seed : Seed)
    (n : ℕ) (hn : n ≤ N) (h : FiniteHistory (p := p) X Y n)
    (out : productDomain X Y)
    (hrun : (toBorelPolicy A fill).IsUnpaddedRun oracle seed n hn h out) :
    Deterministic.runScalarPolicy (A.policy seed) oracle N [] = out.1 := by
  have hlast := (scalar_action_inl_iff A fill seed h out).1 hrun.2
  apply run_eq_of_recorded_list (A.policy seed) oracle (finiteHistoryList h) [] out.1 N
    (by simpa using hn)
  · intro i hi
    have hin : i < n := by simpa using hi
    let j : Fin n := ⟨i, hin⟩
    have hentry := hrun.1 j
    have hq := (scalar_action_inr_iff A fill seed
      (OracleHistory.restrict h (Nat.le_of_lt j.2)) (h j).1).1 hentry.1
    rw [finite_history_list_restrict] at hq
    simpa [finiteHistoryList, j] using And.intro hq hentry.2
  · simpa using hlast.1
  · simpa using hlast.2

section Runner
variable {Omega Seed : Type*} [MeasurableSpace Omega] [MeasurableSpace Seed] {mu : Measure Seed}

/-- Fixed-index virtual query, with public feasible padding after a stop. -/
def scalarRunnerQuery
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (oracle : Omega → Fin N → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (t : Fin N) (z : Omega × Seed) : SaddleSpace dx dy :=
  (runnerQuery (toBorelPolicy A fill) oracle fill 0 t z).1

/-- The genuinely saved output; the runner never consults policy rules after stopping. -/
def scalarRunnerOutput
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (oracle : Omega → Fin N → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (z : Omega × Seed) : SaddleSpace dx dy :=
  (runnerOutput (toBorelPolicy A fill) oracle fill 0 z).1

theorem scalar_runner_query_feasible
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (oracle : Omega → Fin N → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (t : Fin N) (z : Omega × Seed) : scalarRunnerQuery A fill oracle t z ∈ productDomain X Y :=
  (runnerQuery (toBorelPolicy A fill) oracle fill 0 t z).property

theorem scalar_runner_output_feasible
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (oracle : Omega → Fin N → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (z : Omega × Seed) : scalarRunnerOutput A fill oracle z ∈ productDomain X Y :=
  (runnerOutput (toBorelPolicy A fill) oracle fill 0 z).property

/-- Analytic stage-oracle joint measurability implies runner joint
measurability; measurability is not an additional policy hypothesis. -/
theorem scalar_runner_jointly_measurable
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (oracle : Omega → Fin N → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (horacle : ∀ t, Measurable (fun z : Omega × SaddleSpace dx dy => oracle z.1 t z.2)) :
    (∀ t : Fin N, Measurable (scalarRunnerQuery A fill oracle t)) ∧
      Measurable (scalarRunnerOutput A fill oracle) := by
  have ho : JointlyMeasurableStageOracle (toBorelPolicy A fill) oracle := by
    intro t
    exact (horacle t).comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  have hr := jointlyMeasurableRunner_of_stageOracle (toBorelPolicy A fill) oracle fill 0 ho
  exact ⟨fun t => (hr.query_joint t).subtype_coe, hr.output_joint.subtype_coe⟩

/-- Query t depends only on already revealed frame columns <t. -/
theorem scalar_runner_query_prefix {m : ℕ}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (frame : Omega → Fin m → SaddleSpace dx dy)
    (oracle : Omega → Fin N → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (hprefix : StageOracleDependsOnFramePrefix frame oracle) (seed : Seed) (t : Fin N) :
    DependsOnlyOnFramePrefix frame t.1 (fun omega => scalarRunnerQuery A fill oracle t (omega, seed)) :=
  runnerQuery_dependsOnlyOnFramePrefix (toBorelPolicy A fill) frame oracle fill 0 hprefix seed t

/-- Saved output depends only on the N revealed frame columns. -/
theorem scalar_runner_output_prefix {m : ℕ}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (frame : Omega → Fin m → SaddleSpace dx dy)
    (oracle : Omega → Fin N → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (hprefix : StageOracleDependsOnFramePrefix frame oracle) (seed : Seed) :
    DependsOnlyOnFramePrefix frame N (fun omega => scalarRunnerOutput A fill oracle (omega, seed)) :=
  runnerOutput_dependsOnlyOnFramePrefix (toBorelPolicy A fill) frame oracle fill 0 hprefix seed

/-- Exact equality of all on-run scalar-jet responses preserves the saved
output, including outputs that were never themselves queried. -/
theorem scalar_runner_output_eq_of_coupled
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (oracle : Omega → Fin N → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (fixed : Omega → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy)) (z : Omega × Seed)
    (hcouple : ∀ t, oracle z.1 t (scalarRunnerQuery A fill oracle t z) =
      fixed z.1 (scalarRunnerQuery A fill oracle t z)) :
    scalarRunnerOutput A fill oracle z = scalarRunnerOutput A fill (fun omega _ => fixed omega) z := by
  exact congrArg Subtype.val
    (runnerOutput_eq_of_answerAtRunnerQuery (toBorelPolicy A fill) oracle
      (fun omega _ => fixed omega) fill 0 z hcouple)

/-- The fixed-oracle saved output is exactly the pre-existing actual
source evaluator; this rules out a hidden change of algorithm semantics. -/
theorem scalar_runner_fixed_eq_source_run
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (fixed : Omega → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy)) (z : Omega × Seed) :
    scalarRunnerOutput A fill (fun omega _ => fixed omega) z =
      Deterministic.runScalarPolicy (A.policy z.2) (fixed z.1) N [] := by
  obtain ⟨n, hn, hcount, hrun⟩ := runner_executes_fixedOracle_of_coupled
    (toBorelPolicy A fill) (fun omega _ => fixed omega) fixed fill 0 z (fun _ _ => rfl)
  exact (source_run_eq_of_borel_unpadded A fill (fixed z.1) z.2 n hn _ _ hrun).symm

/-- Full transcript coupling to the original source policy evaluator. -/
theorem scalar_runner_coupled_eq_source_run
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu) (fill : productDomain X Y)
    (oracle : Omega → Fin N → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (fixed : Omega → SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy)) (z : Omega × Seed)
    (hcouple : ∀ t, oracle z.1 t (scalarRunnerQuery A fill oracle t z) =
      fixed z.1 (scalarRunnerQuery A fill oracle t z)) :
    scalarRunnerOutput A fill oracle z =
      Deterministic.runScalarPolicy (A.policy z.2) (fixed z.1) N [] := by
  rw [scalar_runner_output_eq_of_coupled A fill oracle fixed z hcouple,
    scalar_runner_fixed_eq_source_run]

end Runner

end
end MinimaxAudit.MeasurableExecution
