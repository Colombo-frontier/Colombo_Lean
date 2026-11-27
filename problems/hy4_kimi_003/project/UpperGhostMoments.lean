import UpperGhostSampleLaw
import SphereSmoothingSharpMoments
import UpperGhostClosedBasis

/-! Sharp moments under the actual normalized-good whole-block law used by the
adaptive ghost kernel. Its associated noise keeps the original product law. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open Task006.HaarRebalancing
namespace Task006.Full

attribute [local irreducible] SampleInstance.goodRebalancedBasis SampleInstance.rebalancedDirectionalMoment SampleInstance.sourceGoodRebalancedBasis

theorem upperBlock_good_conditional_moments {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
    {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) (x grad : Space d)
    (G : Set (OrthogonalGroup d)) (hG : MeasurableSet G) (hpos : orthogonalHaarProbability d G ≠ 0)
    {a v : ℝ}
    (hgoodbias : ∀ Q ∈ G,
      ‖(∫ z : UpperRoundNoise d Ω, upperBlockDirection P F x ((Q, z.1), z.2)
        ∂upperRoundNoiseLaw d μ) - grad‖ ≤ a)
    (hgoodsecond : ∀ Q ∈ G,
      (∫ z : UpperRoundNoise d Ω, ‖upperBlockDirection P F x ((Q, z.1), z.2)‖ ^ 2
        ∂upperRoundNoiseLaw d μ) ≤ v) :
    let ν := goodRestrictedLaw (upperSampleBlockLaw d μ) {b | b.1.1 ∈ G}
    Integrable (upperBlockDirection (d := d) (Ω := Ω) P F x) ν ∧
      Integrable (fun b => ‖upperBlockDirection (d := d) (Ω := Ω) P F x b‖ ^ 2) ν ∧
      ‖(∫ b, upperBlockDirection (d := d) (Ω := Ω) P F x b ∂ν) - grad‖ ≤ a ∧
      (∫ b, ‖upperBlockDirection (d := d) (Ω := Ω) P F x b‖ ^ 2 ∂ν) ≤ v := by
  let ν := goodRestrictedLaw (upperSampleBlockLaw d μ) {b | b.1.1 ∈ G}
  let νQ := goodRestrictedLaw (orthogonalHaarProbability d) G
  let e : UpperSampleBlock d Ω ≃ᵐ OrthogonalGroup d × UpperRoundNoise d Ω := MeasurableEquiv.prodAssoc
  letI : IsProbabilityMeasure νQ := goodRestrictedLaw_probability _ _ hpos
  have hmap : ν.map e = νQ.prod (upperRoundNoiseLaw d μ) := upperSampleBlock_good_conditioning μ G hG
  letI : IsProbabilityMeasure (ν.map e) := by rw [hmap]; infer_instance
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_of_map e
  have hmp : MeasurePreserving e ν (νQ.prod (upperRoundNoiseLaw d μ)) := ⟨e.measurable, hmap⟩
  have hm : Measurable (upperBlockDirection (d := d) (Ω := Ω) P F x) :=
    (upperBlockDirection_measurable P hF).of_uncurry_left
  have hg : Integrable (upperBlockDirection (d := d) (Ω := Ω) P F x) ν :=
    Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ (upperBlockDirection_norm_le P F x))
  have hg2 : Integrable (fun b => ‖upperBlockDirection (d := d) (Ω := Ω) P F x b‖ ^ 2) ν := by
    apply Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable ((Real.sqrt d * P.b) ^ 2)
    filter_upwards [] with b
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (upperBlockDirection_norm_le P F x b) 2
  have hprod : Integrable (fun p : OrthogonalGroup d × UpperRoundNoise d Ω =>
      upperBlockDirection P F x ((p.1, p.2.1), p.2.2)) (νQ.prod (upperRoundNoiseLaw d μ)) := by
    convert! hmp.symm.integrable_comp_of_integrable hg using 1
  have hprod2 : Integrable (fun p : OrthogonalGroup d × UpperRoundNoise d Ω =>
      ‖upperBlockDirection P F x ((p.1, p.2.1), p.2.2)‖ ^ 2) (νQ.prod (upperRoundNoiseLaw d μ)) := by
    convert! hmp.symm.integrable_comp_of_integrable hg2 using 1
  have hmean : (∫ b, upperBlockDirection (d := d) (Ω := Ω) P F x b ∂ν) =
      ∫ Q, (∫ z : UpperRoundNoise d Ω, upperBlockDirection P F x ((Q, z.1), z.2)
        ∂upperRoundNoiseLaw d μ) ∂νQ := by
    exact (hmp.symm.integral_comp' _).symm.trans (integral_prod _ hprod)
  have hsecond : (∫ b, ‖upperBlockDirection (d := d) (Ω := Ω) P F x b‖ ^ 2 ∂ν) =
      ∫ Q, (∫ z : UpperRoundNoise d Ω, ‖upperBlockDirection P F x ((Q, z.1), z.2)‖ ^ 2
        ∂upperRoundNoiseLaw d μ) ∂νQ := by
    exact (hmp.symm.integral_comp' _).symm.trans (integral_prod _ hprod2)
  have hsupp : ∀ᵐ Q ∂νQ, Q ∈ G := goodRestrictedLaw_mem _ _ hG
  refine ⟨hg, hg2, ?_, ?_⟩
  · rw [hmean]
    have hn := norm_integral_le_of_norm_le_const (hsupp.mono hgoodbias)
    have heq := integral_sub hprod.integral_prod_left (integrable_const grad)
    simp only [Function.comp_apply, Function.uncurry, integral_const, probReal_univ, one_smul] at heq
    rw [heq] at hn
    simpa only [probReal_univ, mul_one] using hn
  · rw [hsecond]
    have hi := integral_mono_ae hprod2.integral_prod_left (integrable_const v) (hsupp.mono hgoodsecond)
    simpa only [integral_const, probReal_univ, one_smul] using hi

namespace SampleInstance
variable {d : ℕ} {L : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
  (I : SampleInstance d L P.R Ω μ)

theorem upperGhost_direction_moments_sharp (hR : 0 ≤ P.R) (hL : 0 < L)
    (hd : 0 < d) (hρ : 0 < P.ρ) (hb : 0 < P.b) {s : ℝ} (hs : 1 ≤ s)
    (hq : (d : ℝ) * Real.exp (-s) < 1) {x : Space d} (hx : ‖x‖ ≤ P.R - (P.ρ + P.δ)) :
    let G : Set (OrthogonalGroup d) := {Q | I.sourceGoodRebalancedBasis P hR P.ρ P.δ s x Q}
    let ν := goodRestrictedLaw (upperSampleBlockLaw d μ) {b | b.1.1 ∈ G}
    Integrable (upperBlockDirection (d := d) (Ω := Ω) P (I.rebalancedSample hR) x) ν ∧
      Integrable (fun b => ‖upperBlockDirection (d := d) (Ω := Ω) P (I.rebalancedSample hR) x b‖ ^ 2) ν ∧
      ‖(∫ b, upperBlockDirection (d := d) (Ω := Ω) P (I.rebalancedSample hR) x b ∂ν) -
        I.smoothedGradient hL.le hR P.ρ x‖ ≤
        Real.sqrt d * rebalancingThreshold L d s * P.b ^ (-1/2:ℝ) +
          Real.sqrt d * ((d:ℝ)*L*P.δ/(2*P.ρ)) ∧
      (∫ b, ‖upperBlockDirection (d := d) (Ω := Ω) P (I.rebalancedSample hR) x b‖ ^ 2 ∂ν) ≤
        (d:ℝ)*rebalancingThreshold L d s*P.b ^ (1/2:ℝ) := by
  let G : Set (OrthogonalGroup d) := {Q | I.sourceGoodRebalancedBasis P hR P.ρ P.δ s x Q}
  have hG : MeasurableSet G := (I.measurableSet_sourceGoodRebalancedBasis P hR P.ρ P.δ s).preimage measurable_prodMk_left
  have hpos : orthogonalHaarProbability d G ≠ 0 :=
    good_measure_ne_zero_of_bad_lt_one _ _ hG
      ((I.bad_sourceGoodRebalancedBasis_probability_le P hR hd hL P.delta_pos hs x).trans_lt hq)
  apply upperBlock_good_conditional_moments P (I.rebalancedSample_measurable hR) x
    (I.smoothedGradient hL.le hR P.ρ x) G hG hpos
  · intro Q hQ
    exact (I.upperFixedBasisDirection_source_good_moments_sharp P hR hL hd hρ hb hs hx Q hQ).2.2.1
  · intro Q hQ
    exact (I.upperFixedBasisDirection_source_good_moments_sharp P hR hL hd hρ hb hs hx Q hQ).2.2.2

end SampleInstance
#print axioms SampleInstance.upperGhost_direction_moments_sharp
end Task006.Full
