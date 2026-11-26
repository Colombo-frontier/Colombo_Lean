import NCBall.MainUpper

/-! # The common full-measure sample assumption

Removing a measurable null set produces the pointwise sample model used in
the analytic proof. The subtype inclusion preserves the original probability
law, including every finite iid prefix. No test for membership in this set is
part of the algorithm.
-/

noncomputable section
open MeasureTheory Set Metric
namespace NCBall

structure AELipschitzSampleModel {E Ξ : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSpace Ξ]
    (μ : Measure Ξ) (f : E → ℝ) (F : Ξ → E → ℝ) (ℓ : Ξ → ℝ) (L : ℝ) : Prop where
  jointly_measurable : Measurable (fun p : E × Ξ => F p.2 p.1)
  sample_integrable : ∀ x, Integrable (fun ξ => F ξ x) μ
  sample_mean : ∀ x, (∫ ξ, F ξ x ∂μ) = f x
  modulus_measurable : Measurable ℓ
  sample_lipschitz : ∀ᵐ ξ ∂μ, 0 ≤ ℓ ξ ∧ LipschitzWith (Real.toNNReal (ℓ ξ)) (F ξ)
  modulus_square_integrable : Integrable (fun ξ => ℓ ξ ^ 2) μ
  modulus_square_moment : (∫ ξ, ℓ ξ ^ 2 ∂μ) ≤ L ^ 2

theorem measurable_full_subset {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    {p : Ξ → Prop} (hp : ∀ᵐ ξ ∂μ, p ξ) :
    ∃ s : Set Ξ, MeasurableSet s ∧ (∀ᵐ ξ ∂μ, ξ ∈ s) ∧ ∀ ξ ∈ s, p ξ := by
  obtain ⟨t, hsub, ht, hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  refine ⟨tᶜ, ht.compl, ?_, ?_⟩
  · simpa only [ae_iff, mem_compl_iff, not_not] using hnull
  · intro ξ hξ
    by_contra hnot
    exact hξ (hsub hnot)

theorem full_sample_law_preserving {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) {s : Set Ξ} (hs : MeasurableSet s) (hfull : ∀ᵐ ξ ∂μ, ξ ∈ s) :
    MeasurePreserving (Subtype.val : s → Ξ) (μ.comap Subtype.val) μ := by
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [map_comap_subtype_coe hs, Measure.restrict_eq_self_of_ae_mem hfull]

theorem full_sample_law_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] {s : Set Ξ}
    (hs : MeasurableSet s) (hfull : ∀ᵐ ξ ∂μ, ξ ∈ s) :
    IsProbabilityMeasure (μ.comap (Subtype.val : s → Ξ)) :=
  (MeasurableEmbedding.subtype_coe hs).isProbabilityMeasure_comap (by simpa only [Subtype.range_coe] using hfull)

theorem AELipschitzSampleModel.full_model {E Ξ : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSpace Ξ] {μ : Measure Ξ}
    {f : E → ℝ} {F : Ξ → E → ℝ} {ℓ : Ξ → ℝ} {L : ℝ}
    (hm : AELipschitzSampleModel μ f F ℓ L) :
    ∃ s : Set Ξ, MeasurableSet s ∧ (∀ᵐ ξ ∂μ, ξ ∈ s) ∧
      LipschitzSampleModel (μ.comap (Subtype.val : s → Ξ)) f
        (fun ξ : s => F ξ.val) (fun ξ : s => ℓ ξ.val) L := by
  obtain ⟨s, hs, hfull, hlip⟩ := measurable_full_subset hm.sample_lipschitz
  have hmp := full_sample_law_preserving μ hs hfull
  have he := MeasurableEmbedding.subtype_coe hs
  refine ⟨s, hs, hfull, ⟨?_, ?_, ?_, hm.modulus_measurable.comp measurable_subtype_coe,
    (fun ξ => (hlip ξ.val ξ.property).1), (fun ξ => (hlip ξ.val ξ.property).2), ?_, ?_⟩⟩
  · exact hm.jointly_measurable.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  · intro x
    exact (hmp.integrable_comp_emb he).2 (hm.sample_integrable x)
  · intro x
    rw [hmp.integral_comp he (fun ξ => F ξ x)]
    exact hm.sample_mean x
  · exact (hmp.integrable_comp_emb he).2 hm.modulus_square_integrable
  · rw [hmp.integral_comp he (fun ξ => ℓ ξ ^ 2)]
    exact hm.modulus_square_moment

theorem full_sample_prefix_law {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] {s : Set Ξ}
    (hs : MeasurableSet s) (hfull : ∀ᵐ ξ ∂μ, ξ ∈ s) (K : ℕ) :
    letI := full_sample_law_probability μ hs hfull
    MeasurePreserving (fun w : ℕ → s => fun i : Fin K => (w i.val).val)
      (Measure.infinitePi (fun _ : ℕ => μ.comap (Subtype.val : s → Ξ)))
      (Measure.pi (fun _ : Fin K => μ)) := by
  letI := full_sample_law_probability μ hs hfull
  exact (measurePreserving_pi (fun _ : Fin K => μ.comap (Subtype.val : s → Ξ))
    (fun _ : Fin K => μ) (fun _ => full_sample_law_preserving μ hs hfull)).comp
      (poolPrefix_law (μ.comap (Subtype.val : s → Ξ)) K)

theorem ae_zeroth_order_local_success {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ] {f : CoordSpace (n + 1) → ℝ}
    {F : Ξ → CoordSpace (n + 1) → ℝ} {ℓ : Ξ → ℝ} {δ Δ L ε R : ℝ}
    (hm : AELipschitzSampleModel μ f F ℓ L)
    (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hεL : ε ≤ L)
    (hRpos : 0 < R) (hR : 11 * Δ / ε ≤ R) (x₀ : CoordSpace (n + 1))
    (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    let c := zerothConfig n δ Δ L ε hδ hε hεL
    (2 * (c.K * c.m) : ℕ) ≤ 5800 * (1 + (n + 1 : ℝ) * L ^ 2 * Δ / (δ * ε ^ 3)) ∧
    ∃ (s : Set Ξ) (hs : MeasurableSet s) (hfull : ∀ᵐ ξ ∂μ, ξ ∈ s),
      letI := full_sample_law_probability μ hs hfull
      MeasurePreserving (Subtype.val : s → Ξ) (μ.comap Subtype.val) μ ∧
      ZerothGuarantee (μ.comap Subtype.val) f (fun ξ : s => F ξ.val) x₀ δ ε R
        (zerothRadius δ Δ L R) (zerothRadius_pos hδ hΔ hε hεL hRpos) c := by
  refine ⟨zerothConfig_scalar_bound n hδ hΔ hε hεL, ?_⟩
  obtain ⟨s, hs, hfull, hmodel⟩ := hm.full_model
  refine ⟨s, hs, hfull, ?_⟩
  letI := full_sample_law_probability μ hs hfull
  exact ⟨full_sample_law_preserving μ hs hfull,
    (zeroth_order_local_success hmodel hδ hΔ hε hεL hRpos hR x₀ hgap).2⟩

end NCBall
