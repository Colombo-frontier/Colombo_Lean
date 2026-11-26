import UpperGhostKernel
import HaarRebalancingBlockIntegration

/-! Basis-only conditioning of whole proposal blocks preserves exactly the
original smoothing-vector and fresh-handle law. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open Task006.HaarRebalancing

namespace Task006.Full

theorem goodRestrictedLaw_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (f : A → B) (hf : Measurable f) (G : Set B) (hG : MeasurableSet G) :
    (goodRestrictedLaw μ (f ⁻¹' G)).map f = goodRestrictedLaw (μ.map f) G := by
  unfold goodRestrictedLaw
  rw [Measure.map_smul, ← Measure.restrict_map hf hG, Measure.map_apply hf hG]

theorem upperSampleBlock_good_conditioning {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Set (OrthogonalGroup d)) (hG : MeasurableSet G) :
    (goodRestrictedLaw (upperSampleBlockLaw d μ) {b | b.1.1 ∈ G}).map
        (MeasurableEquiv.prodAssoc : UpperSampleBlock d Ω ≃ᵐ OrthogonalGroup d × UpperRoundNoise d Ω) =
      (goodRestrictedLaw (orthogonalHaarProbability d) G).prod (upperRoundNoiseLaw d μ) := by
  have h := goodRestrictedLaw_map (upperSampleBlockLaw d μ)
    (MeasurableEquiv.prodAssoc : UpperSampleBlock d Ω ≃ᵐ OrthogonalGroup d × UpperRoundNoise d Ω)
    MeasurableEquiv.prodAssoc.measurable (G ×ˢ univ) (hG.prod MeasurableSet.univ)
  have heq : (MeasurableEquiv.prodAssoc : UpperSampleBlock d Ω ≃ᵐ
      OrthogonalGroup d × UpperRoundNoise d Ω) ⁻¹' (G ×ˢ univ) = {b | b.1.1 ∈ G} := by
    ext b
    change (b.1.1 ∈ G ∧ True) ↔ b.1.1 ∈ G
    tauto
  rw [heq, (upperSampleBlockLaw_assoc (d := d) μ).map_eq, goodRestrictedLaw_prod_right] at h
  exact h

theorem upperSampleBlock_basis_bad_probability {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Set (OrthogonalGroup d)) (hG : MeasurableSet G) :
    (upperSampleBlockLaw d μ) {b | b.1.1 ∉ G} = (orthogonalHaarProbability d) Gᶜ := by
  have heq : {b : UpperSampleBlock d Ω | b.1.1 ∉ G} = ((Gᶜ ×ˢ univ) ×ˢ univ) := by
    ext b
    simp
  unfold upperSampleBlockLaw upperBlockSeedLaw
  rw [heq, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one, mul_one]

theorem good_measure_ne_zero_of_bad_lt_one {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (G : Set A) (hG : MeasurableSet G)
    (hbad : μ.real Gᶜ < 1) : μ G ≠ 0 := by
  intro hz
  have hc : μ Gᶜ = 1 := by rw [measure_compl hG (measure_ne_top μ G), hz]; simp
  rw [measureReal_def, hc, ENNReal.toReal_one] at hbad
  exact lt_irrefl _ hbad

#print axioms upperSampleBlock_good_conditioning
#print axioms upperSampleBlock_basis_bad_probability
end Task006.Full
