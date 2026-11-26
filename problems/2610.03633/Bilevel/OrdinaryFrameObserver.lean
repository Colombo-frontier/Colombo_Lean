import Bilevel.OrdinaryFrameEnergy
import Bilevel.OrdinaryFrameMeasurable

/-! Same-run, all-call ordinary-frame observation. No supplied Regular,
concentration-event, or zero-respecting premise occurs. The observations
include both precoin raw insertions and the arbitrary terminal output. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.OrdinaryFrame
open EuclideanGaussian ProjectionPosterior TransportControllerMachine RawGenieBorel

open Classical in
def Observed {d T : ℕ} {H : Memory.{u}} (L : Rules H d T) (cap : ℝ) :
    (Q R t : ℕ) → State H d T → Frame d T → Prop
  | 0,R,t,s,U => GenieProtocol.BoundedEnergy (run L 0 R t s U).2.1 (run L 0 R t s U).2.2 U cap
  | Q+1,0,t,s,U =>
    let a := precoin L t s U
    GenieProtocol.BoundedEnergy a.2.1 a.2.2 U cap ∧ Observed L cap Q 0 (t+1) a U
  | Q+1,R+1,t,s,U =>
    let a := precoin L t s U
    GenieProtocol.BoundedEnergy a.2.1 a.2.2 U cap ∧
      if a.1∈L.success t then Observed L cap Q R (t+1) (revealStep (L.column t) (L.afterReveal t) a U) U
      else Observed L cap Q (R+1) (t+1) a U

theorem safe_observed {d T : ℕ} {H : Memory.{u}} (L : Rules H d T) (cap : ℝ) :
    ∀ Q R t (s : State H d T) (U : Frame d T),
    RawGenieProtocol.Safe cap (compile (policy L Q R t) s.1) s.2.1 s.2.2 U →
      Observed L cap Q R t s U := by
  classical
  intro Q
  induction Q with
  | zero => exact fun R t s U h => safe_run L cap 0 R t s U h
  | succ Q ih =>
    intro R t s U h
    have hp := safe_precoin L cap Q R t s U h
    cases R with
    | zero => exact ⟨hp,ih 0 (t+1) _ U h.2.2⟩
    | succ R =>
      refine ⟨hp,?_⟩
      have hn := h.2.2
      change RawGenieProtocol.Safe cap
        (if (precoin L t s U).1∈L.success t then
          compile (.reveal (L.column t) (L.column_measurable t) (L.afterReveal t)
            (L.afterReveal_measurable t) (policy L Q R (t+1))) (precoin L t s U).1
        else compile (policy L Q (R+1) (t+1)) (precoin L t s U).1)
        (precoin L t s U).2.1 (precoin L t s U).2.2 U at hn
      by_cases ha : (precoin L t s U).1∈L.success t
      · rw [if_pos ha] at hn ⊢
        exact ih R (t+1) _ U hn.2
      · rw [if_neg ha] at hn ⊢
        exact ih (R+1) (t+1) _ U hn

theorem observed_mono {d T : ℕ} {H : Memory.{u}} (L : Rules H d T) {a b : ℝ} (hab : a≤b) :
    ∀ Q R t (s : State H d T) (U : Frame d T),Observed L a Q R t s U → Observed L b Q R t s U := by
  classical
  have hm : ∀ (V : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T),
      GenieProtocol.BoundedEnergy V S U a → GenieProtocol.BoundedEnergy V S U b :=
    fun _ _ _ h i hi => (h i hi).trans hab
  intro Q
  induction Q with
  | zero => exact fun _ _ _ _ h => hm _ _ _ h
  | succ Q ih =>
    intro R t s U h
    cases R with
    | zero => exact ⟨hm _ _ _ h.1,ih 0 (t+1) _ U h.2⟩
    | succ R =>
      refine ⟨hm _ _ _ h.1,?_⟩
      have hn := h.2
      by_cases ha : (precoin L t s U).1∈L.success t
      · rw [if_pos ha] at hn ⊢
        exact ih R (t+1) _ U hn
      · rw [if_neg ha] at hn ⊢
        exact ih (R+1) (t+1) _ U hn

theorem observed_measurable {d T : ℕ} {H : Memory.{u}} {Ω : Type v} [MeasurableSpace Ω]
    (L : Rules H d T) (cap : ℝ) : ∀ Q R t (s : Ω → State H d T), BorelState s →
    ∀ (U : Ω → Frame d T),Measurable U → MeasurableSet {ω | Observed L cap Q R t (s ω) (U ω)} := by
  classical
  have hb : ∀ (s : Ω → State H d T),BorelState s → ∀ (U : Ω → Frame d T),Measurable U →
      MeasurableSet {ω | GenieProtocol.BoundedEnergy (s ω).2.1 (s ω).2.2 (U ω) cap} :=
    fun s hs U hU => boundedEnergy_measurable d T cap _ hs.projector _ hs.known U hU
  intro Q
  induction Q with
  | zero =>
    intro R t s hs U hU
    exact hb _ (run_borel L 0 R t s hs U hU) U hU
  | succ Q ih =>
    intro R t s hs U hU
    have hp := precoin_borel L t hs U hU
    have he := hb _ hp U hU
    cases R with
    | zero => exact he.inter (ih 0 (t+1) _ hp U hU)
    | succ R =>
      have hr := hp.reveal U hU (L.column t) (L.column_measurable t)
        (L.afterReveal t) (L.afterReveal_measurable t)
      have hy := ih R (t+1) _ hr U hU
      have hn := ih (R+1) (t+1) _ hp U hU
      have ha := hp.memory (L.success_measurable t)
      convert he.inter ((ha.inter hy).union (ha.compl.inter hn)) using 1
      ext ω
      by_cases h : (precoin L t (s ω) (U ω)).1∈L.success t <;> simp [Observed,h]

theorem actual_observer {d T Q R n : ℕ} {H : Memory.{u}} {C : Type*} [MeasurableSpace C]
    (hT : T≤d) (L : Rules H d T) (initial : C → H) (hi : Measurable initial)
    (ρ : Measure C) [IsProbabilityMeasure ρ] (t : ℕ) (b : ℝ) (hb : 0<b) (hb2 : b≤2)
    (hd : (2*Q+1)+R+(n+1)≤d) (hcap : (R:ℝ)*(((2*Q+1:ℕ):ℝ)*b)≤1/2) :
    (ρ.prod (HaarFrame.frameLaw d T hT)) {p | ¬Observed L
      (2*((2*Q+1:ℕ):ℝ)*b) Q R t (initial p.1,(⊥,∅)) p.2} ≤
      ((2*Q+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery T n b := by
  have hd' : queryCount Q+R+(n+1)≤d := by simpa only [queryCount_eq] using hd
  have hc' : (R:ℝ)*((queryCount Q:ℝ)*b)≤1/2 := by simpa only [queryCount_eq] using hcap
  have he := GenieProtocol.envelope_twice (queryCount Q) R b hb.le hc'
  have hp := randomized_unsafe_probability hT (policy L Q R t) initial hi ρ b hb hb2 hd' hc'
  have hh : (ρ.prod (HaarFrame.frameLaw d T hT)) {p | ¬Observed L
      (2*(queryCount Q:ℝ)*b) Q R t (initial p.1,(⊥,∅)) p.2} ≤
      (queryCount Q:ℝ≥0∞)*GenieProtocol.failurePerQuery T n b := by
    refine (measure_mono ?_).trans hp
    intro p hbad hsafe
    exact hbad (observed_mono L he Q R t _ _ (safe_observed L _ Q R t _ _ hsafe))
  simpa only [queryCount_eq] using hh

theorem logarithmic_observer {d T Q n : ℕ} {H : Memory.{u}} {C : Type*} [MeasurableSpace C]
    (hT : T≤d) (hTpos : 0<T) (hnpos : 0<n) (L : Rules H d T)
    (initial : C → H) (hi : Measurable initial) (ρ : Measure C) [IsProbabilityMeasure ρ]
    (t : ℕ) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hd : (2*Q+1)+T+(n+1)≤d)
    (hcap : (T:ℝ)*(((2*Q+1:ℕ):ℝ)*GenieProtocol.logarithmicIncrement (2*Q+1) T n δ)≤1/2) :
    (ρ.prod (HaarFrame.frameLaw d T hT)) {p | ¬Observed L
      (2*((2*Q+1:ℕ):ℝ)*GenieProtocol.logarithmicIncrement (2*Q+1) T n δ)
      Q T t (initial p.1,(⊥,∅)) p.2} ≤ ENNReal.ofReal (δ/2) := by
  have hd' : queryCount Q+T+(n+1)≤d := by simpa only [queryCount_eq] using hd
  have hc' : (T:ℝ)*((queryCount Q:ℝ)*GenieProtocol.logarithmicIncrement (queryCount Q) T n δ)≤1/2 := by
    simpa only [queryCount_eq] using hcap
  have hm : 0<queryCount Q := by rw [queryCount_eq];omega
  have hp := randomized_logarithmic_energy_bound hT hm hTpos hnpos
    (policy L Q T t) initial hi ρ δ hδ hδ1 hd' hc'
  have hb := GenieProtocol.logarithmic_increment_pos (queryCount Q) T n hm hTpos hnpos δ hδ hδ1
  have he := GenieProtocol.envelope_twice (queryCount Q) T _ hb.le hc'
  have hh : (ρ.prod (HaarFrame.frameLaw d T hT)) {p | ¬Observed L
      (2*(queryCount Q:ℝ)*GenieProtocol.logarithmicIncrement (queryCount Q) T n δ)
      Q T t (initial p.1,(⊥,∅)) p.2} ≤ ENNReal.ofReal (δ/2) := by
    refine (measure_mono ?_).trans hp
    intro p hbad hsafe
    exact hbad (observed_mono L he Q T t _ _ (safe_observed L _ Q T t _ _ hsafe))
  simpa only [queryCount_eq] using hh

end Bilevel.OrdinaryFrame
