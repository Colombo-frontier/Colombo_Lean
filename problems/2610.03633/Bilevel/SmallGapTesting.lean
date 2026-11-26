import Bilevel.SmallGapOracle
import Bilevel.SmallGapHyperSmoothness
import Bilevel.StoppedOracle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! Concrete finite adaptive executions driven by independent Bernoulli draws. -/

noncomputable section
open MeasureTheory

namespace Bilevel.SmallGapTesting

open SmallGapInstance SmallGapProfiles SmallGapProfileBounds SmallGapLiftSupport

abbrev Query := ℝ × LowerSpace
abbrev Observation := Query × Query

variable (P : SmallGapInstance.Parameters)

def response (p ω : ℝ) (q : Query) (b : Bool) : Observation :=
  ((P.upperX q.1 q.2, P.upperY q.1 q.2),
    (P.sampleLowerX p ω q.1 q.2 b, P.sampleLowerY p ω q.1 q.2 b))

theorem response_inactive (p : ℝ) (q : Query) :
    response P p 1 q false = response P p (-1) q false := by
  simp [response, Parameters.sampleLowerX, Parameters.inactive_response_common]

theorem response_continuous (p ω : ℝ) (b : Bool) : Continuous (fun q : Query => response P p ω q b) := by
  have hr0 := (r0_contDiff P.S P.R).continuous
  have hr1 := (r1_contDiff P.S P.δ).continuous
  have hdr0 := (r0_contDiff P.S P.R).continuous_deriv (by norm_num)
  have hdr1 := (r1_contDiff P.S P.δ).continuous_deriv (by norm_num)
  have hq0 := (normal_contDiff P.R P.R_pos).continuous
  have hq1 := (normal_contDiff P.δ P.δ_pos).continuous
  have hdq0 := (normal_contDiff P.R P.R_pos).continuous_deriv (by norm_num)
  have hdq1 := (normal_contDiff P.δ P.δ_pos).continuous_deriv (by norm_num)
  have hrPlus := (P.residual_contDiff 1).continuous
  have hrMinus := (P.residual_contDiff (-1)).continuous
  have hdrPlus := (P.residual_contDiff 1).continuous_deriv (by norm_num)
  have hdrMinus := (P.residual_contDiff (-1)).continuous_deriv (by norm_num)
  have hB : Continuous (Bowl.slope P.L) := continuous_iff_continuousAt.mpr
    (fun x => (Bowl.hasDerivAt_slope P.L x).continuousAt)
  unfold response Parameters.upperX Parameters.upperY Parameters.sampleLowerX
    Parameters.sampleLowerY BernoulliOracle.sample Parameters.publicY Parameters.lowerY
    Parameters.lowerU Parameters.lowerS Parameters.lowerX Parameters.signalY
    Parameters.signalU Parameters.signalS pack
  fun_prop

theorem response_measurable (p ω : ℝ) :
    Measurable (fun qb : Query × Bool => response P p ω qb.1 qb.2) :=
  measurable_from_prod_countable (fun b => (response_continuous P p ω b).measurable)

variable {State Seed : Type*}

def run (query : State → Query) (update : State → Observation → State)
    (oracle : Query → Bool → Observation) : (n : ℕ) → State → (Fin n → Bool) → State
  | 0, initial, _ => initial
  | n + 1, initial, draws =>
    let state := run query update oracle n initial (fun i => draws i.castSucc)
    update state (oracle (query state) (draws (Fin.last n)))

theorem run_eq_of_inactive (p : ℝ) (query : State → Query) (update : State → Observation → State)
    (n : ℕ) (initial : State) (draws : Fin n → Bool) (hdraws : ∀ i, draws i = false) :
    run query update (response P p 1) n initial draws =
      run query update (response P p (-1)) n initial draws := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih (fun i => draws i.castSucc) (fun i => hdraws i.castSucc),
      hdraws (Fin.last n), response_inactive]

variable [MeasurableSpace State] [MeasurableSpace Seed]

theorem run_measurable (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (n : ℕ) :
    Measurable (fun sz : Seed × (Fin n → Bool) =>
      run query update (response P p ω) n (initial sz.1) sz.2) := by
  induction n with
  | zero => exact hinitial.comp measurable_fst
  | succ n ih =>
    have hprefix : Measurable (fun sz : Seed × (Fin (n + 1) → Bool) =>
        (sz.1, fun i : Fin n => sz.2 i.castSucc)) :=
      measurable_fst.prodMk (measurable_pi_lambda _
        (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd))
    have hstate := ih.comp hprefix
    have hlast : Measurable (fun sz : Seed × (Fin (n + 1) → Bool) => sz.2 (Fin.last n)) :=
      (measurable_pi_apply (Fin.last n)).comp measurable_snd
    exact hupdate.comp (hstate.prodMk ((response_measurable P p ω).comp
      ((hquery.comp hstate).prodMk hlast)))

def output (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (n : ℕ) (sz : Seed × (Fin n → Bool)) : ℝ :=
  readout (run query update (response P p ω) n (initial sz.1) sz.2)

theorem output_measurable (p ω : ℝ) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hreadout : Measurable readout) (n : ℕ) :
    Measurable (output P p ω query update initial readout n) :=
  hreadout.comp (run_measurable P p ω query update initial hquery hupdate hinitial n)

def drawsLaw (p : ℝ) (hp : p ≤ 1) (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ => BernoulliOracle.law p hp)

instance drawsLaw_probability (p : ℝ) (hp : p ≤ 1) (n : ℕ) :
    IsProbabilityMeasure (drawsLaw p hp n) := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

def experimentLaw (ν : Measure Seed) (p : ℝ) (hp : p ≤ 1) (n : ℕ) :
    Measure (Seed × (Fin n → Bool)) := ν.prod (drawsLaw p hp n)

instance experimentLaw_probability (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : ℝ) (hp : p ≤ 1) (n : ℕ) : IsProbabilityMeasure (experimentLaw ν p hp n) :=
  inferInstanceAs (IsProbabilityMeasure (ν.prod (drawsLaw p hp n)))

def activation {n : ℕ} (i : Fin n) : Set (Seed × (Fin n → Bool)) := {sz | sz.2 i = true}

theorem activation_measurable {n : ℕ} (i : Fin n) : MeasurableSet (activation (Seed := Seed) i) :=
  (MeasurableSet.singleton true).preimage ((measurable_pi_apply i).comp measurable_snd)

theorem bernoulli_true (p : ℝ) (hp : p ≤ 1) :
    BernoulliOracle.law p hp {true} = ENNReal.ofReal p := by
  rw [BernoulliOracle.law, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  rfl

theorem activation_probability (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1) {n : ℕ} (i : Fin n) :
    (experimentLaw ν p hp n).real (activation i) = p := by
  classical
  have he : activation (Seed := Seed) i = Set.univ ×ˢ {z : Fin n → Bool | z i = true} := by
    ext sz
    simp [activation]
  rw [measureReal_def, he, experimentLaw, Measure.prod_prod, measure_univ, one_mul]
  have hp' : drawsLaw p hp n {z : Fin n → Bool | z i = true} = ENNReal.ofReal p := by
    change Measure.pi (fun _ : Fin n => BernoulliOracle.law p hp) ((Function.eval i) ⁻¹' {true}) = _
    rw [← Set.univ_pi_update_univ (α := fun _ : Fin n => Bool) i ({true} : Set Bool), Measure.pi_pi]
    rw [Finset.prod_eq_single i]
    · simp only [Function.update_self, bernoulli_true]
    · intro j _ hji
      simp only [Function.update_of_ne hji, measure_univ]
    · simp
  rw [hp', ENNReal.toReal_ofReal hp0]

theorem no_activation_probability (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1) (n : ℕ) :
    1 - (experimentLaw ν p hp n).real (⋃ i : Fin n, activation i)ᶜ ≤ p * n := by
  have h := measureReal_iUnion_fintype_le (μ := experimentLaw ν p hp n)
    (fun i : Fin n => activation (Seed := Seed) i)
  simp_rw [activation_probability ν p hp0 hp] at h
  rw [measureReal_compl (MeasurableSet.iUnion activation_measurable)]
  simpa [mul_comm] using h

def loss (ω x : ℝ) : ℝ := |deriv (P.realizedObjective ω) x|

theorem loss_nonneg (ω x : ℝ) : 0 ≤ loss P ω x := abs_nonneg _

theorem loss_continuous (ω : ℝ) : Continuous (loss P ω) := by
  have he : deriv (P.realizedObjective ω) = P.realizedGradient ω :=
    funext (fun x => (P.realizedGradient_correct ω x).deriv)
  unfold loss
  rw [he]
  exact continuous_abs.comp (continuous_iff_continuousAt.mpr
    (fun x => (P.realizedGradient_hasDerivAt ω x).continuousAt))

theorem loss_bounded (ω x : ℝ) (hω : |ω| ≤ 1) :
    loss P ω x ≤ P.L + (P.L / P.μ) * C * P.S * (P.R + P.δ) := by
  have hb := Bowl.slope_bound P.L x P.L_pos.le
  have hr := (P.residual_jet_bounds ω (P.L / P.μ * x) hω).2.1
  have hκ := div_pos P.L_pos P.μ_pos
  have hmul := mul_le_mul_of_nonneg_left hr hκ.le
  rw [loss, (P.realizedGradient_correct ω x).deriv, Parameters.realizedGradient]
  have ht := abs_add (Bowl.slope P.L x) ((P.L / P.μ) * deriv (P.residual ω) (P.L / P.μ * x))
  rw [abs_mul, abs_of_pos hκ] at ht
  nlinarith

theorem output_loss_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p ω : ℝ) (hp : p ≤ 1) (hω : |ω| ≤ 1)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hreadout : Measurable readout) (n : ℕ) :
    Integrable (fun sz => loss P ω (output P p ω query update initial readout n sz))
      (experimentLaw ν p hp n) := by
  have hm := (loss_continuous P ω).measurable.comp
    (output_measurable P p ω query update initial readout hquery hupdate hinitial hreadout n)
  apply (integrable_const (P.L + (P.L / P.μ) * C * P.S * (P.R + P.δ))).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun sz => by
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (loss_nonneg P ω _)]
    exact loss_bounded P ω _ hω)

def risk (ν : Measure Seed) (p ω : ℝ) (hp : p ≤ 1)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (n : ℕ) : ℝ :=
  ∫ sz, loss P ω (output P p ω query update initial readout n sz) ∂experimentLaw ν p hp n

theorem risk_from_actual_run (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : ℝ) (hp : p ≤ 1) (hgeometry : P.Geometry)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hreadout : Measurable readout) (n : ℕ) :
    ((P.L / P.μ) * P.S * P.δ) * (experimentLaw ν p hp n).real (⋃ i : Fin n, activation i)ᶜ ≤
      (risk P ν p 1 hp query update initial readout n +
        risk P ν p (-1) hp query update initial readout n) / 2 := by
  apply StoppedOracle.risk_from_coupled_outputs (loss P 1) (loss P (-1))
    (output P p 1 query update initial readout n) (output P p (-1) query update initial readout n)
    (MeasurableSet.iUnion activation_measurable).compl
    (output_loss_integrable P ν p 1 hp (by norm_num) query update initial readout
      hquery hupdate hinitial hreadout n)
    (output_loss_integrable P ν p (-1) hp (by norm_num) query update initial readout
      hquery hupdate hinitial hreadout n)
    (loss_nonneg P 1) (loss_nonneg P (-1)) (P.realizedObjective_separation hgeometry)
  intro sz hsz
  have hdraws : ∀ i, sz.2 i = false := by
    intro i
    cases hb : sz.2 i with
    | false => rfl
    | true => exact False.elim (hsz (Set.mem_iUnion.mpr ⟨i, hb⟩))
  exact congrArg readout (run_eq_of_inactive P p query update n (initial sz.1) sz.2 hdraws)

/-- Every measurable adaptive state machine, with an arbitrary independent seed,
must use the claimed fixed horizon. No common-output premise is supplied. -/
theorem fixed_horizon_query_bound (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : ℝ) (hp0 : 0 < p) (hp : p ≤ 1) (hgeometry : P.Geometry)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hreadout : Measurable readout) (n : ℕ)
    (accuracy : (risk P ν p 1 hp query update initial readout n +
      risk P ν p (-1) hp query update initial readout n) / 2 ≤ ((P.L / P.μ) * P.S * P.δ) / 8) :
    7 / (8 * p) ≤ (n : ℝ) := by
  have hγ : 0 < (P.L / P.μ) * P.S * P.δ :=
    mul_pos (mul_pos (div_pos P.L_pos P.μ_pos) P.S_pos) P.δ_pos
  exact BernoulliOracle.expected_queries_from_testing hp0 hγ
    (risk_from_actual_run P ν p hp hgeometry query update initial readout hquery hupdate hinitial hreadout n)
    (no_activation_probability ν p hp0.le hp n) accuracy

theorem fixed_horizon_statistical_bound (ν : Measure Seed) [IsProbabilityMeasure ν]
    (σ : ℝ) (hgeometry : P.Geometry)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (readout : State → ℝ) (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hreadout : Measurable readout) (n : ℕ)
    (accuracy : (risk P ν (P.activationProbability σ) 1 (P.activationProbability_le_one σ)
      query update initial readout n +
      risk P ν (P.activationProbability σ) (-1) (P.activationProbability_le_one σ)
        query update initial readout n) / 2 ≤ ((P.L / P.μ) * P.S * P.δ) / 8) :
    (7 / 8 : ℝ) * (1 + σ ^ 2 / P.signalBound ^ 2) ≤ (n : ℝ) := by
  have h := fixed_horizon_query_bound P ν (P.activationProbability σ) (P.activationProbability_pos σ)
    (P.activationProbability_le_one σ) hgeometry query update initial readout
    hquery hupdate hinitial hreadout n accuracy
  have he : 7 / (8 * P.activationProbability σ) = (7 / 8 : ℝ) * (P.activationProbability σ)⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [he, P.inverse_activationProbability σ] at h
  exact h

end Bilevel.SmallGapTesting
