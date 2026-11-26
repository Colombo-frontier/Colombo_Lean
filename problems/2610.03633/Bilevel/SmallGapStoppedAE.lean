import Bilevel.SmallGapStopped
import Bilevel.SmallGapScaledTesting

/-! The stopped lower bound with almost-sure termination, including the exact
manuscript scaling. Null exceptional executions need not halt. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.SmallGapStopped

open SmallGapInstance SmallGapLiftSupport SmallGapTesting InfiniteBernoulli

variable {State Seed : Type} [MeasurableSpace State] [MeasurableSpace Seed]
variable (P : Parameters)

omit [MeasurableSpace State] in
theorem query_ae_pending (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p ω : ℝ) (hp : p ≤ 1) (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (N : Sample Seed → ℕ)
    (first : ∀ᵐ z ∂law ν p hp,
      Transcript.FirstHalt halt (history P p ω query update initial z) (N z)) (n : ℕ) :
    UnboundedStopping.query N n =ᵐ[law ν p hp]
      pastInput n ⁻¹' pending P p ω query update initial halt n := by
  classical
  filter_upwards [first] with z hz
  apply propext
  change n < N z ↔ ∀ j : Fin (n + 1),
    halt (historyBlock P p ω query update initial n (pastInput n z) j) = false
  simp only [historyBlock_pastInput]
  constructor
  · intro h j
    exact hz.2 j (lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) h)
  · intro h
    by_contra hn
    have hf := h ⟨N z, Nat.lt_succ_of_le (Nat.le_of_not_gt hn)⟩
    rw [hz.1] at hf
    contradiction

theorem fresh_factorization_ae (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p ω : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (N : Sample Seed → ℕ)
    (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hhalt : Measurable halt)
    (first : ∀ᵐ z ∂law ν p hp,
      Transcript.FirstHalt halt (history P p ω query update initial z) (N z)) (n : ℕ) :
    (law ν p hp).real (UnboundedStopping.query N n ∩ {z : Sample Seed | z (some n) = true}) =
      p * (law ν p hp).real (UnboundedStopping.query N n) := by
  have he := query_ae_pending P ν p ω hp query update initial halt N first n
  have hi := (indepFun_iff_indepSet_preimage (pastInput_measurable n) (measurable_pi_apply (some n))).mp
    (prefix_fresh_independent ν p hp n) _ ({true} : Set Bool)
      (pending_measurable P p ω query update initial halt hquery hupdate hinitial hhalt n)
      (MeasurableSet.singleton true)
  rw [measureReal_congr (he.inter (Filter.EventuallyEq.rfl)), measureReal_congr he]
  exact StoppedOracle.fresh_factorization _ _ p hi (fresh_probability ν p hp0 hp n)

theorem risk_from_common_event_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {event : Set Ω} (hevent : MeasurableSet event)
    {plus minus : Ω → ℝ} (hplus : Integrable plus μ) (hminus : Integrable minus μ)
    (plus_nonneg : ∀ z, 0 ≤ plus z) (minus_nonneg : ∀ z, 0 ≤ minus z)
    {γ : ℝ} (separation : ∀ᵐ z ∂μ, z ∈ event → 2 * γ ≤ plus z + minus z) :
    γ * μ.real event ≤ ((∫ z, plus z ∂μ) + ∫ z, minus z ∂μ) / 2 := by
  have hb : ∀ᵐ z ∂μ, event.indicator (fun _ => 2 * γ) z ≤ plus z + minus z := by
    filter_upwards [separation] with z hz
    by_cases he : z ∈ event
    · simpa [Set.indicator_of_mem he] using hz he
    · simp only [Set.indicator_of_not_mem he]
      exact add_nonneg (plus_nonneg z) (minus_nonneg z)
  have hi := integral_mono_ae ((integrable_const (2 * γ)).indicator hevent) (hplus.add hminus) hb
  simp only [Pi.add_apply] at hi
  rw [integral_indicator_const _ hevent, integral_add hplus hminus] at hi
  simp only [smul_eq_mul] at hi
  nlinarith

/-- Actual adaptive executions with almost-sure finite first halting times.
Fresh-bit factorization, common outputs, and integrability of losses are proved. -/
theorem expected_query_bound_ae (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : ℝ) (hp0 : 0 < p) (hp : p ≤ 1) (hgeometry : P.Geometry)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (readout : State → ℝ)
    (NPlus NMinus : Sample Seed → ℕ)
    (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hhalt : Measurable halt) (hreadout : Measurable readout)
    (hNp : Measurable NPlus) (hNm : Measurable NMinus)
    (firstPlus : ∀ᵐ z ∂law ν p hp,
      Transcript.FirstHalt halt (history P p 1 query update initial z) (NPlus z))
    (firstMinus : ∀ᵐ z ∂law ν p hp,
      Transcript.FirstHalt halt (history P p (-1) query update initial z) (NMinus z))
    (hNi : Integrable (fun z => (NPlus z : ℝ)) (law ν p hp))
    (accuracy : (risk P ν p 1 hp query update initial readout NPlus +
      risk P ν p (-1) hp query update initial readout NMinus) / 2 ≤ ((P.L / P.μ) * P.S * P.δ) / 8) :
    7 / (8 * p) ≤ ∫ z, (NPlus z : ℝ) ∂law ν p hp := by
  let activation : ℕ → Set (Sample Seed) := fun n =>
    UnboundedStopping.query NPlus n ∩ {z | z (some n) = true}
  have hm : ∀ n, MeasurableSet (activation n) := fun n =>
    (UnboundedStopping.query_measurable hNp n).inter
      ((MeasurableSet.singleton true).preimage (measurable_pi_apply (some n)))
  have hf : ∀ n, (law ν p hp).real (activation n) = p * (law ν p hp).real (UnboundedStopping.query NPlus n) :=
    fresh_factorization_ae P ν p 1 hp0.le hp query update initial halt NPlus
      hquery hupdate hinitial hhalt firstPlus
  have hsep : ∀ᵐ z ∂law ν p hp, z ∈ (⋃ n, activation n)ᶜ →
      2 * ((P.L / P.μ) * P.S * P.δ) ≤
        loss P 1 (terminal P p 1 query update initial readout NPlus z) +
        loss P (-1) (terminal P p (-1) query update initial readout NMinus z) := by
    filter_upwards [firstPlus, firstMinus] with z hplus hminus
    intro hz
    have hinactive : ∀ t < NPlus z, z (some t) = false := by
      intro t ht
      cases hb : z (some t) with
      | false => rfl
      | true => exact False.elim (hz (Set.mem_iUnion.mpr ⟨t, ht, hb⟩))
    have he := (Transcript.stopped_outputs_equal query update (response P p 1) (response P p (-1))
      (response_inactive P p) (fun t => z (some t)) (initial (z none)) halt readout hplus hminus hinactive).2
    change terminal P p 1 query update initial readout NPlus z =
      terminal P p (-1) query update initial readout NMinus z at he
    rw [he]
    exact P.realizedObjective_separation hgeometry _
  exact BernoulliOracle.expected_queries_from_testing hp0
    (mul_pos (mul_pos (div_pos P.L_pos P.μ_pos) P.S_pos) P.δ_pos)
    (risk_from_common_event_ae (MeasurableSet.iUnion hm).compl
      (terminal_loss_integrable P ν p 1 hp (by norm_num) query update initial readout NPlus
        hquery hupdate hinitial hreadout hNp)
      (terminal_loss_integrable P ν p (-1) hp (by norm_num) query update initial readout NMinus
        hquery hupdate hinitial hreadout hNm)
      (fun z => loss_nonneg P 1 _) (fun z => loss_nonneg P (-1) _) hsep)
    (UnboundedStopping.no_activation_probability hNp hNi activation hm hp0.le hf) accuracy

end Bilevel.SmallGapStopped

namespace Bilevel.SmallGapStopped

theorem extended_count_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (N : Ω → ℕ) (hN : Measurable N) (c : ℝ)
    (h : Integrable (fun z => (N z : ℝ)) μ → c ≤ ∫ z, (N z : ℝ) ∂μ) :
    ENNReal.ofReal c ≤ ∫⁻ z, ENNReal.ofReal (N z : ℝ) ∂μ := by
  have hn : 0 ≤ᵐ[μ] (fun z => (N z : ℝ)) := Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  by_cases hi : Integrable (fun z => (N z : ℝ)) μ
  · rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
    exact ENNReal.ofReal_le_ofReal (h hi)
  · have ht : (∫⁻ z, ENNReal.ofReal (N z : ℝ) ∂μ) = ⊤ := by
      by_contra hf
      exact hi ⟨((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hN).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal hn).mpr (lt_top_iff_ne_top.mpr hf)⟩
    rw [ht]
    exact le_top

end Bilevel.SmallGapStopped

namespace Bilevel.SmallGapScaling.Input

open SmallGapInstance SmallGapLiftSupport SmallGapTesting SmallGapStopped InfiniteBernoulli

variable (Q : SmallGapScaling.Input)
variable {State Seed : Type} [MeasurableSpace State] [MeasurableSpace Seed]

/-- The manuscript's `κ^6 L² θ² σ² / ε^4` expected-query lower rate, with
universal explicit constants and almost-sure termination of the actual runs. -/
theorem scaled_expected_query_bound (ν : Measure Seed) [IsProbabilityMeasure ν] (σ : ℝ)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (readout : State → ℝ)
    (NPlus NMinus : Sample Seed → ℕ)
    (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hhalt : Measurable halt) (hreadout : Measurable readout)
    (hNp : Measurable NPlus) (hNm : Measurable NMinus)
    (firstPlus : ∀ᵐ z ∂law ν (Q.parameters.activationProbability σ) (Q.parameters.activationProbability_le_one σ),
      Transcript.FirstHalt halt (history Q.parameters (Q.parameters.activationProbability σ) 1 query update initial z) (NPlus z))
    (firstMinus : ∀ᵐ z ∂law ν (Q.parameters.activationProbability σ) (Q.parameters.activationProbability_le_one σ),
      Transcript.FirstHalt halt (history Q.parameters (Q.parameters.activationProbability σ) (-1) query update initial z) (NMinus z))
    (hNi : Integrable (fun z => (NPlus z : ℝ))
      (law ν (Q.parameters.activationProbability σ) (Q.parameters.activationProbability_le_one σ)))
    (accuracy : (SmallGapStopped.risk Q.parameters ν (Q.parameters.activationProbability σ) 1
        (Q.parameters.activationProbability_le_one σ) query update initial readout NPlus +
      SmallGapStopped.risk Q.parameters ν (Q.parameters.activationProbability σ) (-1)
        (Q.parameters.activationProbability_le_one σ) query update initial readout NMinus) / 2 ≤ Q.ε) :
    (7 / 8 : ℝ) * (1 + Q.κ ^ 6 * Q.L ^ 2 * Q.θ ^ 2 * σ ^ 2 /
      ((39296 * C ^ 2) ^ 2 * Q.ε ^ 4)) ≤
        ∫ z, (NPlus z : ℝ) ∂law ν (Q.parameters.activationProbability σ) (Q.parameters.activationProbability_le_one σ) := by
  have hacc : (SmallGapStopped.risk Q.parameters ν (Q.parameters.activationProbability σ) 1
        (Q.parameters.activationProbability_le_one σ) query update initial readout NPlus +
      SmallGapStopped.risk Q.parameters ν (Q.parameters.activationProbability σ) (-1)
        (Q.parameters.activationProbability_le_one σ) query update initial readout NMinus) / 2 ≤
      ((Q.parameters.L / Q.parameters.μ) * Q.parameters.S * Q.parameters.δ) / 8 := by
    rw [Q.gamma]
    simpa using accuracy
  have h := expected_query_bound_ae Q.parameters ν (Q.parameters.activationProbability σ)
    (Q.parameters.activationProbability_pos σ) (Q.parameters.activationProbability_le_one σ)
    Q.geometry query update initial halt readout NPlus NMinus hquery hupdate hinitial hhalt
    hreadout hNp hNm firstPlus firstMinus hNi hacc
  have he : 7 / (8 * Q.parameters.activationProbability σ) =
      (7 / 8 : ℝ) * (Q.parameters.activationProbability σ)⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [he, Q.parameters.inverse_activationProbability σ, Q.noise_scale σ] at h
  exact h

/-- The same source rate in extended expectation: no finite-mean assumption
is imposed on the algorithm's query count. -/
theorem scaled_extended_expected_query_bound (ν : Measure Seed) [IsProbabilityMeasure ν] (σ : ℝ)
    (query : State → Query) (update : State → Observation → State)
    (initial : Seed → State) (halt : State → Bool) (readout : State → ℝ)
    (NPlus NMinus : Sample Seed → ℕ)
    (hquery : Measurable query)
    (hupdate : Measurable (fun so : State × Observation => update so.1 so.2))
    (hinitial : Measurable initial) (hhalt : Measurable halt) (hreadout : Measurable readout)
    (hNp : Measurable NPlus) (hNm : Measurable NMinus)
    (firstPlus : ∀ᵐ z ∂law ν (Q.parameters.activationProbability σ) (Q.parameters.activationProbability_le_one σ),
      Transcript.FirstHalt halt (history Q.parameters (Q.parameters.activationProbability σ) 1 query update initial z) (NPlus z))
    (firstMinus : ∀ᵐ z ∂law ν (Q.parameters.activationProbability σ) (Q.parameters.activationProbability_le_one σ),
      Transcript.FirstHalt halt (history Q.parameters (Q.parameters.activationProbability σ) (-1) query update initial z) (NMinus z))
    (accuracy : (SmallGapStopped.risk Q.parameters ν (Q.parameters.activationProbability σ) 1
        (Q.parameters.activationProbability_le_one σ) query update initial readout NPlus +
      SmallGapStopped.risk Q.parameters ν (Q.parameters.activationProbability σ) (-1)
        (Q.parameters.activationProbability_le_one σ) query update initial readout NMinus) / 2 ≤ Q.ε) :
    ENNReal.ofReal ((7 / 8 : ℝ) * (1 + Q.κ ^ 6 * Q.L ^ 2 * Q.θ ^ 2 * σ ^ 2 /
      ((39296 * C ^ 2) ^ 2 * Q.ε ^ 4))) ≤
        ∫⁻ z, ENNReal.ofReal (NPlus z : ℝ)
          ∂law ν (Q.parameters.activationProbability σ) (Q.parameters.activationProbability_le_one σ) := by
  apply extended_count_bound NPlus hNp
  intro hNi
  exact Q.scaled_expected_query_bound ν σ query update initial halt readout NPlus NMinus
    hquery hupdate hinitial hhalt hreadout hNp hNm firstPlus firstMinus hNi accuracy

end Bilevel.SmallGapScaling.Input
