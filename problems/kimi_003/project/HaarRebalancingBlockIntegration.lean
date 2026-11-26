import HaarRebalancingUpperMarginal
set_option maxHeartbeats 10000000
open MeasureTheory Set
open Task006.HaarRebalancing
namespace Task006.Full
noncomputable section

/-- Exact regrouping of the original public seed and fresh sample block law. -/
theorem upperSampleBlockLaw_assoc {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : UpperSampleBlock d Ω ≃ᵐ
      OrthogonalGroup d × UpperRoundNoise d Ω)
      (upperSampleBlockLaw d μ) ((orthogonalHaarProbability d).prod (upperRoundNoiseLaw d μ)) :=
  measurePreserving_prodAssoc _ _ _

/-- Deterministic clipping gives genuine integrability on every block. -/
theorem upperBlockDirection_integrable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
    {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) (x : Space d) :
    Integrable (upperBlockDirection P F x) (upperSampleBlockLaw d μ) ∧
      Integrable (fun block => ‖upperBlockDirection P F x block‖ ^ 2) (upperSampleBlockLaw d μ) := by
  have hm : Measurable (upperBlockDirection P F x) :=
    (upperBlockDirection_measurable P hF).of_uncurry_left
  have hb := upperBlockDirection_norm_le P F x
  refine ⟨Integrable.of_bound hm.aestronglyMeasurable (Real.sqrt d * P.b) (ae_of_all _ hb), ?_⟩
  apply Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable ((Real.sqrt d * P.b) ^ 2)
  exact ae_of_all _ (fun block => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb block) 2)

/-- The integral under the actual block law is the iterated Haar/fresh-noise
integral, by a proved measure-preserving regrouping and Fubini. -/
theorem upperBlockDirection_integral_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
    {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) (x : Space d) :
    (∫ block, upperBlockDirection P F x block ∂upperSampleBlockLaw d μ) =
      ∫ Q, (∫ z : UpperRoundNoise d Ω, upperBlockDirection P F x ((Q,z.1),z.2)
        ∂upperRoundNoiseLaw d μ) ∂orthogonalHaarProbability d := by
  have hi := (upperBlockDirection_integrable P hF x (μ := μ)).1
  have hmp := (upperSampleBlockLaw_assoc (d := d) μ).symm
  have hp := hmp.integrable_comp_of_integrable hi
  have heq := hmp.integral_comp' (upperBlockDirection P F x)
  exact heq.symm.trans (integral_prod _ hp)

theorem upperBlockDirection_second_integral_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
    {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) (x : Space d) :
    (∫ block, ‖upperBlockDirection P F x block‖ ^ 2 ∂upperSampleBlockLaw d μ) =
      ∫ Q, (∫ z : UpperRoundNoise d Ω, ‖upperBlockDirection P F x ((Q,z.1),z.2)‖ ^ 2
        ∂upperRoundNoiseLaw d μ) ∂orthogonalHaarProbability d := by
  have hi := (upperBlockDirection_integrable P hF x (μ := μ)).2
  have hmp := (upperSampleBlockLaw_assoc (d := d) μ).symm
  have hp := hmp.integrable_comp_of_integrable hi
  have heq := hmp.integral_comp' (fun block => ‖upperBlockDirection P F x block‖ ^ 2)
  exact heq.symm.trans (integral_prod _ hp)

/-- Parameter-integrated second moments are integrable in the actual Haar
basis, established by bounded product integrability. -/
theorem upperBlockDirection_second_mean_integrable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
    {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) (x : Space d) :
    Integrable (fun Q => ∫ z : UpperRoundNoise d Ω,
      ‖upperBlockDirection P F x ((Q,z.1),z.2)‖ ^ 2 ∂upperRoundNoiseLaw d μ)
      (orthogonalHaarProbability d) := by
  have hi := (upperBlockDirection_integrable P hF x (μ := μ)).2
  have hmp := (upperSampleBlockLaw_assoc (d := d) μ).symm
  exact (hmp.integrable_comp_of_integrable hi).integral_prod_left

theorem upperBlockDirection_mean_integrable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
    {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) (x : Space d) :
    Integrable (fun Q => ∫ z : UpperRoundNoise d Ω,
      upperBlockDirection P F x ((Q,z.1),z.2) ∂upperRoundNoiseLaw d μ)
      (orthogonalHaarProbability d) := by
  have hi := (upperBlockDirection_integrable P hF x (μ := μ)).1
  have hmp := (upperSampleBlockLaw_assoc (d := d) μ).symm
  exact (hmp.integrable_comp_of_integrable hi).integral_prod_left

/-- Generic integration of actual fixed-basis estimates. Keeping the oracle
function abstract prevents irrelevant expansion of its chosen representative. -/
theorem upperBlockDirection_mixture {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (P : UpperProgramParameters)
    {F : Space d → Ω → ℝ} (hF : Measurable (Function.uncurry F)) (x grad : Space d)
    (G : Set (OrthogonalGroup d)) (hG : MeasurableSet G) {a v l q : ℝ}
    (ha : 0 ≤ a) (hv : 0 ≤ v) (hl : 0 ≤ l) (hgrad : ‖grad‖ ≤ l)
    (hbad : (orthogonalHaarProbability d).real Gᶜ ≤ q)
    (hgoodbias : ∀ Q ∈ G,
      ‖(∫ z : UpperRoundNoise d Ω, upperBlockDirection P F x ((Q,z.1),z.2)
        ∂upperRoundNoiseLaw d μ) - grad‖ ≤ a)
    (hgoodsecond : ∀ Q ∈ G,
      (∫ z : UpperRoundNoise d Ω, ‖upperBlockDirection P F x ((Q,z.1),z.2)‖ ^ 2
        ∂upperRoundNoiseLaw d μ) ≤ v) :
    Integrable (upperBlockDirection P F x) (upperSampleBlockLaw d μ) ∧
    Integrable (fun block => ‖upperBlockDirection P F x block‖ ^ 2) (upperSampleBlockLaw d μ) ∧
    ‖(∫ block, upperBlockDirection P F x block ∂upperSampleBlockLaw d μ) - grad‖ ≤
      a + (Real.sqrt d * P.b + l) * q ∧
    (∫ block, ‖upperBlockDirection P F x block‖ ^ 2 ∂upperSampleBlockLaw d μ) ≤
      v + (d * P.b ^ 2) * q := by
  have hint := upperBlockDirection_integrable P hF x (μ := μ)
  have hnorm (Q : OrthogonalGroup d) (z : UpperRoundNoise d Ω) :
      ‖upperBlockDirection P F x ((Q,z.1),z.2)‖ ≤ Real.sqrt d * P.b :=
    upperBlockDirection_norm_le P F x ((Q,z.1),z.2)
  have hnormsq (Q : OrthogonalGroup d) (z : UpperRoundNoise d Ω) :
      ‖upperBlockDirection P F x ((Q,z.1),z.2)‖ ^ 2 ≤ d * P.b ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hnorm Q z) 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] at hh
    exact hh
  have hmeanint := upperBlockDirection_mean_integrable P hF x (μ := μ)
  have hsecondint := upperBlockDirection_second_mean_integrable P hF x (μ := μ)
  refine ⟨hint.1, hint.2, ?_, ?_⟩
  · rw [upperBlockDirection_integral_eq P hF x]
    have hm := norm_integral_le_good_bad (μ := orthogonalHaarProbability d) (G := G)
      (f := fun Q : OrthogonalGroup d =>
        (∫ z : UpperRoundNoise d Ω, upperBlockDirection P F x ((Q,z.1),z.2)
          ∂upperRoundNoiseLaw d μ) - grad) hG ha
      (c := Real.sqrt d * P.b + l)
        (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) P.clip_nonneg) hl) hbad
      (ae_of_all _ hgoodbias)
      (ae_of_all _ (fun Q => by
        have hmn : ‖∫ z : UpperRoundNoise d Ω,
            upperBlockDirection P F x ((Q,z.1),z.2) ∂upperRoundNoiseLaw d μ‖ ≤
              Real.sqrt d * P.b := by
          simpa only [probReal_univ, mul_one] using
            norm_integral_le_of_norm_le_const (ae_of_all (upperRoundNoiseLaw d μ) (hnorm Q))
        exact (norm_sub_le _ _).trans (add_le_add hmn hgrad)))
    simpa only [integral_sub hmeanint (integrable_const _), integral_const,
      probReal_univ, one_smul] using hm
  · rw [upperBlockDirection_second_integral_eq P hF x]
    exact integral_le_good_bad (G := G)
      (f := fun Q : OrthogonalGroup d => ∫ z : UpperRoundNoise d Ω,
        ‖upperBlockDirection P F x ((Q,z.1),z.2)‖ ^ 2 ∂upperRoundNoiseLaw d μ)
      hsecondint hG hv (c := (d : ℝ) * P.b ^ 2) (by positivity) hbad
      (ae_of_all _ hgoodsecond)
      (ae_of_all _ (fun Q => by
        simpa only [integral_const, probReal_univ, one_smul] using
          integral_mono_of_nonneg (ae_of_all _ (fun _ => sq_nonneg _))
            (integrable_const ((d : ℝ) * P.b ^ 2) (μ := upperRoundNoiseLaw d μ))
            (ae_of_all _ (hnormsq Q))))

end
end Task006.Full
