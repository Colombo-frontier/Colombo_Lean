import Bilevel.TransportControllerPolicy

/-! Query-injection theorem for an actual Borel round policy under the
original hard-instance law, including the free initial source observation
and arbitrary independent algorithm-private randomness. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

theorem initialGenerators_measurable (n D : ℕ) : Measurable (initialGenerators n D) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro i
  by_cases hv : v=0
  · simpa only [initialGenerators,if_pos hv] using (measurable_id : Measurable (fun y : Space D => y))
  · simp only [initialGenerators,if_neg hv]
    exact measurable_const

theorem prior_policy_query_failure {H : Type*} [MeasurableSpace H] {n D p c T h : ℕ}
    (hT : T≤D) (hpos : 0<T) (a : ℝ) (ha : 0<a) (r : ℕ) (hr : 0<r)
    (P : Policy H n D p c T 1 h) (memory : H) (hD : queryCap n p c 1 h+r≤D) :
    (TransportNetwork.law n D) {z | policyBad hT a P (memory,seed T hT z) z} ≤
      (h:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a)) := by
  let o := namedObservation T hT (0 : Vertex n) ⟨0,hpos⟩
  let b := fun y z => policyBad hT a P (memory,initialGenerators n D y) z
  have hb : MeasurableSet {p : Space D × Latent n D | b p.1 p.2} :=
    (((measurable_const.prodMk ((initialGenerators_measurable n D).comp measurable_fst)).prodMk
      measurable_snd) (policyBad_measurable hT a P))
  have he : {z | policyBad hT a P (memory,seed T hT z) z} = {z | b (o z) z} := by
    ext z
    simp only [Set.mem_setOf_eq,b,o,namedObservation,seed_eq_initial T hT hpos z]
  rw [he]
  apply observation_tail_bound (TransportNetwork.law n D) o (named_measurable T hT 0 ⟨0,hpos⟩) b hb
  filter_upwards [initial_posterior T hT hpos] with y hy
  exact policy_query_failure hT a ha r hr P (memory,initialGenerators n D y) hD _ hy

theorem randomized_policy_query_failure {H : Type*} [MeasurableSpace H] {n D p c T h : ℕ}
    (hT : T≤D) (hpos : 0<T) (a : ℝ) (ha : 0<a) (r : ℕ) (hr : 0<r)
    (P : Policy H n D p c T 1 h) (ρ : Measure H) [IsProbabilityMeasure ρ]
    (hD : queryCap n p c 1 h+r≤D) :
    (ρ.prod (TransportNetwork.law n D))
      {p | policyBad hT a P (p.1,seed T hT p.2) p.2} ≤
      (h:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a)) := by
  have hb : MeasurableSet {p : H × Latent n D | policyBad hT a P (p.1,seed T hT p.2) p.2} :=
    (((measurable_fst.prodMk ((seed_measurable T hT).comp measurable_snd)).prodMk measurable_snd)
      (policyBad_measurable hT a P))
  rw [Measure.prod_apply hb]
  calc
    _ ≤ ∫⁻ _memory, (h:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a)) ∂ρ := by
      apply lintegral_mono
      intro memory
      exact prior_policy_query_failure hT hpos a ha r hr P memory hD
    _ = _ := by simp

end Bilevel.TransportRound
