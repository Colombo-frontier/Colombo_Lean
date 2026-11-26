import Bilevel.PolishedHierarchicalActivation
import Bilevel.BorelAdaptiveExpectedInformation

/-! Probability and extended expected-cost consequences of the two-level
protocol. Local full-reply equality and the deterministic prefix barrier
are explicit obligations. They are not replaced by an assumed final risk
or probability estimate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PolishedHierarchicalActivation
open BorelAdaptive
variable {S Q O Y I Private : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSpace Private]

theorem fixed_horizon_probability (A : Program S Q O Y) (T : ℕ)
    (evaluate : I → Q → ℕ → Bool → O)
    (he : Measurable (fun p : I × (Q × (ℕ × Bool)) => evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (original : I → Q → Bool → O) (s : Private → S) (hi : Measurable s)
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (p : ℝ) (hp : 0<p) (hp1 : p≤1) (n : ℕ) (hT : 0<T)
    (hn : (n:ℝ)≤(T:ℝ)/(16*p))
    (bad : Set (Sample I Private Bool)) (hb : MeasurableSet bad)
    (hbad : (ν.prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real bad≤1/8)
    (loss : I × Y → ℝ) (ε : ℝ)
    (hlocal : ∀ z,z∉bad → ∀ t<n, A.halt (run A T evaluate s t z).1=false →
      original z.1 (A.query (run A T evaluate s t z).1) (z.2.2 t)=
        evaluate z.1 (A.query (run A T evaluate s t z).1)
          (min T (run A T evaluate s t z).2) (z.2.2 t))
    (hbarrier : ∀ z,z∉bad → (run A T evaluate s n z).2<T →
      8*ε≤loss (z.1,A.output (run A T evaluate s n z).1)) :
    13/16≤(ν.prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real
      {z | 8*ε≤loss (seededCapped A original s n z)} := by
  let μ := ν.prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))
  let act : Set (Sample I Private Bool) := {z | T≤(run A T evaluate s n z).2}
  have ha : MeasurableSet act := by
    simp only [act,run_count]
    exact (successes_measurable (instrument A) (response T evaluate)
      (response_measurable T evaluate he) (initial s) (hi.prodMk measurable_const) n)
      (measurableSet_Ici (a:=T))
  have hact := activation_sixteenth A T evaluate s ν ρ p hp hp1 n hT hn
  have hg := MultiscaleRisk.good_probability μ bad act hb ha hbad hact
  apply hg.trans
  apply measureReal_mono
  intro z hz
  have hnb : z∉bad := fun h => hz (Or.inl h)
  have hna : ¬T≤(run A T evaluate s n z).2 := fun h => hz (Or.inr h)
  exact capped_margin_on_good A T evaluate original s n z loss ε (hlocal z hnb) hna
    (hbarrier z hnb)
  all_goals exact measure_ne_top _ _

theorem fixed_instance_expected_calls (A : Program S Q O Y) (T : ℕ)
    (evaluate : I → Q → ℕ → Bool → O)
    (he : Measurable (fun p : I × (Q × (ℕ × Bool)) => evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))
    (original : I → Q → Bool → O)
    (hr : Measurable (fun p : I × (Q × Bool) => original p.1 p.2.1 p.2.2))
    (s : Private → S) (hi : Measurable s)
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (p ε : ℝ) (hp : 0<p) (hp1 : p≤1) (hε : 0<ε) (hT : 0<T)
    (valid : I → Prop) (hvalid : ∀ᵐ a ∂ν,valid a)
    (loss : I × Y → ℝ)
    (hloss : Measurable (fun z => loss (seededStopped A original s z)))
    (hpos : ∀ z,0≤loss z)
    (bad : ℕ → Set (Sample I Private Bool)) (hb : ∀ n,MeasurableSet (bad n))
    (hbad : ∀ n : ℕ,(n:ℝ)≤(T:ℝ)/(16*p) →
      (ν.prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real (bad n)≤1/8)
    (hlocal : ∀ n : ℕ,(n:ℝ)≤(T:ℝ)/(16*p) → ∀ z,z∉bad n → ∀ t<n,
      A.halt (run A T evaluate s t z).1=false →
      original z.1 (A.query (run A T evaluate s t z).1) (z.2.2 t)=
        evaluate z.1 (A.query (run A T evaluate s t z).1)
          (min T (run A T evaluate s t z).2) (z.2.2 t))
    (hbarrier : ∀ n : ℕ,(n:ℝ)≤(T:ℝ)/(16*p) → ∀ z,z∉bad n →
      (run A T evaluate s n z).2<T → 8*ε≤loss (z.1,A.output (run A T evaluate s n z).1))
    (haccuracy : ∀ a,valid a →
      (∫⁻ z,ENNReal.ofReal (loss (seededStopped A original s (a,z)))
        ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))≤ENNReal.ofReal ε) :
    ∃ a,valid a ∧ ENNReal.ofReal ((T:ℝ)/(512*p))≤
      ∫⁻ z,seededCalls A original s (a,z) ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)) := by
  let act : ℕ → Set (Sample I Private Bool) := fun n => {z | T≤(run A T evaluate s n z).2}
  apply BorelAdaptive.fixed_instance_expected_seededCalls A original hr s hi ν
    (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))) valid hvalid
    loss hloss hpos T hT p ε hp hε bad act ?_ haccuracy
  intro n hn
  have ha : MeasurableSet (act n) := by
    simp only [act,run_count]
    exact (successes_measurable (instrument A) (response T evaluate)
      (response_measurable T evaluate he) (initial s) (hi.prodMk measurable_const) n)
      (measurableSet_Ici (a:=T))
  refine ⟨hb n,ha,hbad n hn,activation_sixteenth A T evaluate s ν ρ p hp hp1 n hT hn,?_⟩
  exact Filter.Eventually.of_forall (fun z hnb hna =>
    capped_margin_on_good A T evaluate original s n z loss ε (hlocal n hn z hnb) hna
      (hbarrier n hn z hnb))

end Bilevel.PolishedHierarchicalActivation
