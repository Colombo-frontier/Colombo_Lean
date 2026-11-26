import Bilevel.BorelAdaptiveProductFreshness
import Bilevel.MultiscaleActivation

/-! The same actual iid Bernoulli stream controls live successful calls.
Halting may suppress successes, and never increases the activation count. -/
noncomputable section
open MeasureTheory
namespace Bilevel.BorelAdaptive

variable {S Q O Y I Private : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSpace Private]

def successes (A : Program S Q O Y) (response : I → Q → Bool → O)
    (initial : Private → S) : ℕ → Sample I Private Bool → ℕ
  | 0,_ => 0
  | n+1,p => successes A response initial n p +
      if A.halt (seededState A response initial n p)=false ∧ p.2.2 n=true then 1 else 0

theorem seededState_measurable {C : Type*} [MeasurableSpace C]
    (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial) (n : ℕ) :
    Measurable (seededState A response initial n) :=
  (run_measurable A response hr n).comp (seedInput_measurable initial hi)

theorem successes_measurable (A : Program S Q O Y) (response : I → Q → Bool → O)
    (hr : Measurable (fun p : I × (Q × Bool) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial) (n : ℕ) :
    Measurable (successes A response initial n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hl : MeasurableSet {p : Sample I Private Bool | A.halt (seededState A response initial n p)=false} :=
      (A.halt_measurable.comp (seededState_measurable A response hr initial hi n)) (measurableSet_singleton false)
    have hc : MeasurableSet {p : Sample I Private Bool | p.2.2 n=true} := by
      have hc' : Measurable (fun p : Sample I Private Bool => p.2.2 n) :=
        (measurable_pi_apply n).comp (measurable_snd.comp measurable_snd)
      exact hc' (measurableSet_singleton true)
    exact ih.add (measurable_const.ite (hl.inter hc) measurable_const)

omit [MeasurableSpace I] [MeasurableSpace Private] in
theorem successes_le_count (A : Program S Q O Y) (response : I → Q → Bool → O)
    (initial : Private → S) (n : ℕ) (p : Sample I Private Bool) :
    (successes A response initial n p : ℝ) ≤
      MultiscaleActivation.count n (IndependentStream.project n p.2.2) := by
  induction n with
  | zero => simp [successes,MultiscaleActivation.count]
  | succ n ih =>
    have hb : ((if A.halt (seededState A response initial n p)=false ∧ p.2.2 n=true then 1 else 0 : ℕ) : ℝ) ≤
        if p.2.2 n then 1 else 0 := by
      cases h : p.2.2 n <;> simp only [h,Bool.false_eq_true,and_false,if_false,if_true]
      · norm_num
      · split_ifs <;> norm_num
    simpa only [successes,Nat.cast_add,IndependentStream.project_succ,MultiscaleActivation.count]
      using add_le_add ih hb

theorem draws_preserving (νI : Measure I) [IsProbabilityMeasure νI]
    (ρ : Measure Private) [IsProbabilityMeasure ρ] (p : ℝ) (hp1 : p ≤ 1) (n : ℕ) :
    MeasurePreserving (fun z : Sample I Private Bool => IndependentStream.project n z.2.2)
      (νI.prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))))
      (IndependentDraws.law (BernoulliOracle.law p hp1) n) := by
  have h₁ : MeasurePreserving Prod.snd
      (νI.prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))))
      (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))) :=
    ⟨measurable_snd,by simp only [Measure.map_snd_prod,measure_univ,one_smul]⟩
  have h₂ : MeasurePreserving Prod.snd
      (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))
      (IndependentStream.law (BernoulliOracle.law p hp1)) :=
    ⟨measurable_snd,by simp only [Measure.map_snd_prod,measure_univ,one_smul]⟩
  exact (IndependentStream.project_preserves (BernoulliOracle.law p hp1) n).comp (h₂.comp h₁)

theorem activation_sixteenth (A : Program S Q O Y) (response : I → Q → Bool → O)
    (initial : Private → S) (νI : Measure I) [IsProbabilityMeasure νI]
    (ρ : Measure Private) [IsProbabilityMeasure ρ] (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (n T : ℕ) (hT : 0 < T) (hn : (n : ℝ) ≤ (T : ℝ)/(16*p)) :
    (νI.prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))).real
      {z | T ≤ successes A response initial n z} ≤ 1/16 := by
  let μ := νI.prod (ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))
  have hm : MeasurableSet {z : IndependentDraws.Draws Bool n | (T : ℝ) ≤ MultiscaleActivation.count n z} :=
    measurableSet_le measurable_const (MultiscaleActivation.count_measurable n)
  have he := (draws_preserving νI ρ p hp1 n).measure_preimage hm.nullMeasurableSet
  have hs : {z : Sample I Private Bool | T ≤ successes A response initial n z} ⊆
      {z | (T : ℝ) ≤ MultiscaleActivation.count n (IndependentStream.project n z.2.2)} := by
    intro z hz
    exact (Nat.cast_le.mpr hz).trans (successes_le_count A response initial n z)
  apply (measureReal_mono hs).trans
  change μ.real ((fun z : Sample I Private Bool => IndependentStream.project n z.2.2) ⁻¹'
    {z | (T : ℝ) ≤ MultiscaleActivation.count n z}) ≤ _
  rw [measureReal_def,he]
  exact MultiscaleActivation.revelation_sixteenth n T hT p hp hp1 hn

end Bilevel.BorelAdaptive
