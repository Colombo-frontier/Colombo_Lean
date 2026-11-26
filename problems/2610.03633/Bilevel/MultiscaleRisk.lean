import Bilevel.MultiscaleActivation
import Bilevel.ProjectionGenie

/-! Probability-to-risk and hard-instance extraction for the actual multiscale experiment. -/
noncomputable section
open MeasureTheory
namespace Bilevel.MultiscaleRisk

theorem good_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad activation : Set Ω) (hb : MeasurableSet bad) (ha : MeasurableSet activation)
    (hbad : μ.real bad ≤ 1/8) (hactivation : μ.real activation ≤ 1/16) :
    (13:ℝ)/16 ≤ μ.real (bad ∪ activation)ᶜ := by
  rw [measureReal_compl (hb.union ha)]
  rw [measureReal_univ_eq_one]
  have hu := measureReal_union_le bad activation (μ := μ)
  linarith

theorem risk_from_good_event {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad activation : Set Ω) (hb : MeasurableSet bad) (ha : MeasurableSet activation)
    (hbad : μ.real bad ≤ 1/8) (hactivation : μ.real activation ≤ 1/16)
    (loss : Ω → ℝ) (hloss : Integrable loss μ) (hpos : ∀ ω, 0 ≤ loss ω)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ᵐ ω ∂μ, ω ∉ bad → ω ∉ activation → 8*ε ≤ loss ω) :
    13*ε/2 ≤ ∫ ω, loss ω ∂μ := by
  let good := (bad ∪ activation)ᶜ
  have hgood : MeasurableSet good := (hb.union ha).compl
  have hle : good.indicator (fun _ => 8*ε) ≤ᵐ[μ] loss := by
    filter_upwards [hmargin] with ω hω
    by_cases hg : ω ∈ good
    · rw [Set.indicator_of_mem hg]
      exact hω (fun h => hg (Or.inl h)) (fun h => hg (Or.inr h))
    · rw [Set.indicator_of_not_mem hg]
      exact hpos ω
  have hi := integral_mono_ae ((integrable_const (8*ε)).indicator hgood) hloss hle
  rw [integral_indicator_const _ hgood] at hi
  simp only [smul_eq_mul] at hi
  have hp := good_probability μ bad activation hb ha hbad hactivation
  change (13:ℝ)/16 ≤ μ.real good at hp
  nlinarith [mul_le_mul_of_nonneg_right hp (show 0 ≤ 8*ε by positivity)]

theorem hard_instance {Frame Seed : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
    (μ : Measure Frame) (ν : Measure Seed) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (valid : Frame → Prop) (hvalid : ∀ᵐ U ∂μ, valid U) (loss : Frame × Seed → ℝ)
    (hloss : Integrable loss (μ.prod ν)) (ε : ℝ)
    (hrisk : ε < ∫ p, loss p ∂μ.prod ν) :
    ∃ U, valid U ∧ ε < ∫ s, loss (U,s) ∂ν := by
  by_contra h
  push_neg at h
  have hi : (∫ U, ∫ s, loss (U,s) ∂ν ∂μ) ≤ ε := by
    have hmono := integral_mono_ae hloss.integral_prod_left (integrable_const ε)
      (hvalid.mono (fun U hU => h U hU))
    simpa using hmono
  rw [integral_prod _ hloss] at hrisk
  linarith

/-! The final averaging step in the multiscale lower-bound proof.  The
product experiment has a good-event margin, and the product risk is then
converted into one fixed valid frame with a large conditional seed risk. -/
theorem hard_instance_from_good_event
    {Frame Seed : Type*} [MeasurableSpace Frame] [MeasurableSpace Seed]
    (μ : Measure Frame) (ν : Measure Seed) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (valid : Frame → Prop)
    (hvalid : ∀ᵐ U ∂μ, valid U) (bad activation : Set (Frame × Seed))
    (hb : MeasurableSet bad) (ha : MeasurableSet activation)
    (hbad : (μ.prod ν).real bad ≤ 1/8)
    (hactivation : (μ.prod ν).real activation ≤ 1/16)
    (loss : Frame × Seed → ℝ) (hloss : Integrable loss (μ.prod ν))
    (hpos : ∀ p, 0 ≤ loss p) (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ᵐ p ∂μ.prod ν,
      p ∉ bad → p ∉ activation → 8*ε ≤ loss p) :
    ∃ U, valid U ∧ 6*ε < ∫ s, loss (U,s) ∂ν := by
  have hprod : 13*ε/2 ≤ ∫ p, loss p ∂μ.prod ν :=
    risk_from_good_event (μ.prod ν) bad activation hb ha hbad hactivation
      loss hloss hpos ε hε hmargin
  have hstrict : 6*ε < ∫ p, loss p ∂μ.prod ν := by
    linarith
  exact hard_instance μ ν valid hvalid loss hloss (6*ε) hstrict

/-! The Bernoulli revelation estimate lifted to a product experiment with an
arbitrary random frame.  The activation event depends only on the finite
Bernoulli stream, so its product probability is the one-dimensional bound. -/
theorem product_revelation_sixteenth
    {Frame : Type*} [MeasurableSpace Frame]
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (N T : ℕ) (hT : 0 < T) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hN : (N : ℝ) ≤ (T : ℝ)/(16*p)) :
    (μ.prod (IndependentDraws.law (BernoulliOracle.law p hp1) N)).real
      ((Set.univ : Set Frame) ×ˢ
        {z | (T : ℝ) ≤ MultiscaleActivation.count N z}) ≤ 1/16 := by
  have hrev := MultiscaleActivation.revelation_sixteenth N T hT p hp0 hp1 hN
  have hset : MeasurableSet ((Set.univ : Set Frame) ×ˢ
      {z | (T : ℝ) ≤ MultiscaleActivation.count N z}) :=
    MeasurableSet.univ.prod
      (measurableSet_le measurable_const (MultiscaleActivation.count_measurable N))
  change ENNReal.toReal ((μ.prod (IndependentDraws.law (BernoulliOracle.law p hp1) N))
    ((Set.univ : Set Frame) ×ˢ
      {z | (T : ℝ) ≤ MultiscaleActivation.count N z})) ≤ 1/16
  rw [Measure.prod_apply hset]
  simp only [Set.preimage, Set.mem_prod, Set.mem_univ, true_and]
  simp
  simpa [div_eq_mul_inv] using hrev

/-! The fixed-horizon version of the product-to-fixed-frame bridge.  The
only remaining premises are the concrete bad-event and margin obligations
for the adaptive transcript; the Bernoulli revelation probability is now
discharged by `hN`. -/
theorem hard_instance_after_revelation
    {Frame : Type*} [MeasurableSpace Frame]
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (N T : ℕ) (hT : 0 < T) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hN : (N : ℝ) ≤ (T : ℝ)/(16*p))
    (valid : Frame → Prop) (hvalid : ∀ᵐ U ∂μ, valid U)
    (bad : Set (Frame × IndependentDraws.Draws Bool N))
    (hb : MeasurableSet bad)
    (hbad : (μ.prod (IndependentDraws.law (BernoulliOracle.law p hp1) N)).real bad ≤ 1/8)
    (loss : Frame × IndependentDraws.Draws Bool N → ℝ)
    (hloss : Integrable loss (μ.prod (IndependentDraws.law (BernoulliOracle.law p hp1) N)))
    (hpos : ∀ q, 0 ≤ loss q) (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ᵐ q ∂μ.prod (IndependentDraws.law (BernoulliOracle.law p hp1) N),
      q ∉ bad →
      q ∉ ((Set.univ : Set Frame) ×ˢ
        {z | (T : ℝ) ≤ MultiscaleActivation.count N z}) →
      8*ε ≤ loss q) :
    ∃ U, valid U ∧
      6*ε < ∫ z, loss (U,z) ∂IndependentDraws.law (BernoulliOracle.law p hp1) N := by
  let activation : Set (Frame × IndependentDraws.Draws Bool N) :=
    (Set.univ : Set Frame) ×ˢ
      {z | (T : ℝ) ≤ MultiscaleActivation.count N z}
  have ha : MeasurableSet activation := by
    dsimp [activation]
    exact MeasurableSet.univ.prod
      (measurableSet_le measurable_const (MultiscaleActivation.count_measurable N))
  have hactivation :
      (μ.prod (IndependentDraws.law (BernoulliOracle.law p hp1) N)).real activation ≤ 1/16 := by
    dsimp [activation]
    exact product_revelation_sixteenth μ N T hT p hp0 hp1 hN
  apply hard_instance_from_good_event μ
    (IndependentDraws.law (BernoulliOracle.law p hp1) N) valid hvalid bad activation
    hb ha hbad hactivation loss hloss hpos ε hε
  simpa [activation] using hmargin

/-! Contrapositive form of the fixed-horizon reduction.  If every valid
frame has conditional loss at most `6*ε`, then the Bernoulli revelation
budget cannot satisfy `N ≤ T/(16p)`. -/
theorem fixed_horizon_query_lower
    {Frame : Type*} [MeasurableSpace Frame]
    (μ : Measure Frame) [IsProbabilityMeasure μ]
    (N T : ℕ) (hT : 0 < T) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (valid : Frame → Prop) (hvalid : ∀ᵐ U ∂μ, valid U)
    (bad : Set (Frame × IndependentDraws.Draws Bool N))
    (hb : MeasurableSet bad)
    (hbad : (μ.prod (IndependentDraws.law (BernoulliOracle.law p hp1) N)).real bad ≤ 1/8)
    (loss : Frame × IndependentDraws.Draws Bool N → ℝ)
    (hloss : Integrable loss (μ.prod (IndependentDraws.law (BernoulliOracle.law p hp1) N)))
    (hpos : ∀ q, 0 ≤ loss q) (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ᵐ q ∂μ.prod (IndependentDraws.law (BernoulliOracle.law p hp1) N),
      q ∉ bad →
      q ∉ ((Set.univ : Set Frame) ×ˢ
        {z | (T : ℝ) ≤ MultiscaleActivation.count N z}) →
      8*ε ≤ loss q)
    (hsolver : ∀ U, valid U →
      (∫ z, loss (U,z) ∂IndependentDraws.law (BernoulliOracle.law p hp1) N) ≤ 6*ε) :
    (T : ℝ)/(16*p) < N := by
  by_contra hnot
  have hN : (N : ℝ) ≤ (T : ℝ)/(16*p) := le_of_not_gt hnot
  obtain ⟨U, hU, hlarge⟩ := hard_instance_after_revelation μ N T hT p hp0 hp1 hN
    valid hvalid bad hb hbad loss hloss hpos ε hε hmargin
  have hsmall := hsolver U hU
  linarith

theorem bounded_loss_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (loss : Ω → ℝ) (hloss : Measurable loss) (B : ℝ)
    (hbound : ∀ ω, ‖loss ω‖ ≤ B) : Integrable loss μ :=
  (integrable_const B).mono' hloss.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

end Bilevel.MultiscaleRisk
