import Bilevel.InfiniteBernoulli
import Bilevel.AdaptiveTesting

/-! Expected-query lower bounds for actual small-gap oracles. Private randomness
and all fresh Bernoulli draws carry an explicit countable product law. Causality
of the state-machine recursion proves the independence needed at each call. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.SmallGapStopped

open SmallGapInstance SmallGapLiftSupport SmallGapTesting InfiniteBernoulli

variable {State Seed : Type} [MeasurableSpace State] [MeasurableSpace Seed]
variable (P : Parameters)

def history (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (z : Sample Seed) (n : ℕ) : State :=
  Transcript.run query update (response P p ω) (fun t => z (some t)) (initial (z none)) n

omit [MeasurableSpace State] in
theorem finite_run_eq (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (draws : ℕ → Bool) (initial : State) (n : ℕ) :
    run query update (response P p ω) n initial (fun i => draws i) =
      Transcript.run query update (response P p ω) draws initial n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [run, Transcript.run] using
      (congrArg (fun s => update s (response P p ω (query s) (draws n))) ih)

theorem history_measurable (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (n : ℕ) :
    Measurable (fun z : Sample Seed => history P p ω query update initial z n) := by
  have h := (run_measurable P p ω query update initial hquery hupdate hinitial n).comp
    (pastInput_measurable n)
  convert h using 1
  funext z
  exact (finite_run_eq P p ω query update (fun t => z (some t)) (initial (z none)) n).symm

def historyBlock (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (n : ℕ) (sz : Seed × (Fin n → Bool)) (j : Fin (n + 1)) : State :=
  run query update (response P p ω) j (initial sz.1)
    (fun i => sz.2 ⟨i, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt)⟩)

theorem historyBlock_measurable (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (n : ℕ) :
    Measurable (historyBlock P p ω query update initial n) := by
  apply measurable_pi_lambda
  intro j
  exact (run_measurable P p ω query update initial hquery hupdate hinitial j).comp
    (measurable_fst.prodMk (measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply (⟨i, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt)⟩ : Fin n)).comp measurable_snd)))

omit [MeasurableSpace Seed] [MeasurableSpace State] in
theorem historyBlock_pastInput (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (n : ℕ) (z : Sample Seed) (j : Fin (n + 1)) :
    historyBlock P p ω query update initial n (pastInput n z) j =
      history P p ω query update initial z j :=
  finite_run_eq P p ω query update (fun t => z (some t)) (initial (z none)) j

def pending (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (n : ℕ) : Set (Seed × (Fin n → Bool)) :=
  {sz | ∀ j : Fin (n + 1), halt (historyBlock P p ω query update initial n sz j) = false}

theorem pending_measurable (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hhalt : Measurable halt) (n : ℕ) :
    MeasurableSet (pending P p ω query update initial halt n) := by
  have h := historyBlock_measurable P p ω query update initial hquery hupdate hinitial n
  convert MeasurableSet.iInter (fun j => (MeasurableSet.singleton false).preimage
    (hhalt.comp ((measurable_pi_apply j).comp h))) using 1
  ext sz
  simp [pending]

omit [MeasurableSpace Seed] [MeasurableSpace State] in
theorem query_eq_pending (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (N : Sample Seed → ℕ)
    (first : ∀ z, Transcript.FirstHalt halt (history P p ω query update initial z) (N z)) (n : ℕ) :
    UnboundedStopping.query N n = pastInput n ⁻¹' pending P p ω query update initial halt n := by
  ext z
  simp only [UnboundedStopping.query, Set.mem_setOf_eq, Set.mem_preimage, pending,
    historyBlock_pastInput]
  constructor
  · intro h j
    exact (first z).2 j (lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) h)
  · intro h
    by_contra hn
    have hle : N z ≤ n := Nat.le_of_not_gt hn
    have hf := h ⟨N z, Nat.lt_succ_of_le hle⟩
    rw [(first z).1] at hf
    contradiction

theorem stoppingCount_measurable (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (N : Sample Seed → ℕ)
    (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hhalt : Measurable halt)
    (first : ∀ z, Transcript.FirstHalt halt (history P p ω query update initial z) (N z)) :
    Measurable N := by
  apply measurable_to_countable'
  intro n
  have he : N ⁻¹' {n} =
      {z | halt (history P p ω query update initial z n) = true} ∩
        ⋂ j : Fin n, {z | halt (history P p ω query update initial z j) = false} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_iInter]
    constructor
    · intro hn
      exact ⟨hn ▸ (first z).1, fun j => (first z).2 j (hn ▸ j.isLt)⟩
    · intro h
      apply Transcript.firstHalt_unique halt _ (first z)
      exact ⟨h.1, fun j hj => h.2 ⟨j, hj⟩⟩
  rw [he]
  exact ((MeasurableSet.singleton true).preimage (hhalt.comp
    (history_measurable P p ω query update initial hquery hupdate hinitial n))).inter
    (MeasurableSet.iInter (fun j => (MeasurableSet.singleton false).preimage (hhalt.comp
      (history_measurable P p ω query update initial hquery hupdate hinitial j))))

theorem fresh_independent (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p ω : ℝ) (hp : p ≤ 1) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (N : Sample Seed → ℕ)
    (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hhalt : Measurable halt)
    (first : ∀ z, Transcript.FirstHalt halt (history P p ω query update initial z) (N z)) (n : ℕ) :
    IndepSet (UnboundedStopping.query N n) {z : Sample Seed | z (some n) = true} (law ν p hp) := by
  rw [query_eq_pending P p ω query update initial halt N first n]
  exact (indepFun_iff_indepSet_preimage (pastInput_measurable n) (measurable_pi_apply (some n))).mp
    (prefix_fresh_independent ν p hp n) _ _
      (pending_measurable P p ω query update initial halt hquery hupdate hinitial hhalt n)
      (MeasurableSet.singleton true)

def terminal (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (N : Sample Seed → ℕ) (z : Sample Seed) : ℝ :=
  readout (history P p ω query update initial z (N z))

theorem terminal_measurable (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (N : Sample Seed → ℕ)
    (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hreadout : Measurable readout) (hN : Measurable N) :
    Measurable (terminal P p ω query update initial readout N) := by
  have h : Measurable (fun zn : Sample Seed × ℕ => history P p ω query update initial zn.1 zn.2) :=
    measurable_from_prod_countable (history_measurable P p ω query update initial hquery hupdate hinitial)
  exact hreadout.comp (h.comp (measurable_id.prodMk hN))

theorem terminal_loss_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p ω : ℝ) (hp : p ≤ 1) (hω : |ω| ≤ 1)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (N : Sample Seed → ℕ)
    (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hreadout : Measurable readout) (hN : Measurable N) :
    Integrable (fun z => loss P ω (terminal P p ω query update initial readout N z)) (law ν p hp) := by
  have hm := (loss_continuous P ω).measurable.comp
    (terminal_measurable P p ω query update initial readout N hquery hupdate hinitial hreadout hN)
  apply (integrable_const (P.L + (P.L / P.μ) * C * P.S * (P.R + P.δ))).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (loss_nonneg P ω _)]
    exact loss_bounded P ω _ hω)

def risk (ν : Measure Seed) [IsProbabilityMeasure ν] (p ω : ℝ) (hp : p ≤ 1)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (N : Sample Seed → ℕ) : ℝ :=
  ∫ z, loss P ω (terminal P p ω query update initial readout N z) ∂law ν p hp

theorem expected_query_bound (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : ℝ) (hp0 : 0 < p) (hp : p ≤ 1) (hgeometry : P.Geometry)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (readout : State → ℝ)
    (NPlus NMinus : Sample Seed → ℕ)
    (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hhalt : Measurable halt) (hreadout : Measurable readout)
    (firstPlus : ∀ z, Transcript.FirstHalt halt (history P p 1 query update initial z) (NPlus z))
    (firstMinus : ∀ z, Transcript.FirstHalt halt (history P p (-1) query update initial z) (NMinus z))
    (hNi : Integrable (fun z => (NPlus z : ℝ)) (law ν p hp))
    (accuracy : (risk P ν p 1 hp query update initial readout NPlus +
      risk P ν p (-1) hp query update initial readout NMinus) / 2 ≤ ((P.L / P.μ) * P.S * P.δ) / 8) :
    7 / (8 * p) ≤ ∫ z, (NPlus z : ℝ) ∂law ν p hp := by
  have hNp := stoppingCount_measurable P p 1 query update initial halt NPlus hquery hupdate
    hinitial hhalt firstPlus
  have hNm := stoppingCount_measurable P p (-1) query update initial halt NMinus hquery hupdate
    hinitial hhalt firstMinus
  refine AdaptiveTesting.adaptive_testing_bound query update (response P p 1) (response P p (-1))
    (response_inactive P p) (fun (z : Sample Seed) t => z (some t)) (fun z => initial (z none)) halt readout
    NPlus NMinus firstPlus firstMinus hNp hNi hp0
      (mul_pos (mul_pos (div_pos P.L_pos P.μ_pos) P.S_pos) P.δ_pos)
      ?_ ?_ ?_ (loss P 1) (loss P (-1)) (loss_nonneg P 1) (loss_nonneg P (-1))
      (P.realizedObjective_separation hgeometry) ?_ ?_ accuracy
  · intro t
    exact (MeasurableSet.singleton true).preimage (measurable_pi_apply (some t))
  · exact fresh_independent P ν p 1 hp query update initial halt NPlus hquery hupdate hinitial hhalt firstPlus
  · exact fresh_probability ν p hp0.le hp
  · exact terminal_loss_integrable P ν p 1 hp (by norm_num) query update initial readout NPlus
      hquery hupdate hinitial hreadout hNp
  · exact terminal_loss_integrable P ν p (-1) hp (by norm_num) query update initial readout NMinus
      hquery hupdate hinitial hreadout hNm

end Bilevel.SmallGapStopped
