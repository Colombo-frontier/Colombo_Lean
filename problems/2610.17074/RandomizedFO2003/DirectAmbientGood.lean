import RandomizedFO2003.DirectAmbient

namespace RandomizedFO2003.Rotations

open MeasureTheory

universe u

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem embedding_family_ae_nonzero {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [Nontrivial S] [MeasurableSpace S] [BorelSpace S]
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (L : Ω → S →ₗᵢ[ℝ] E)
    (hL : Measurable (fun ω => (L ω).toContinuousLinearMap)) :
    ∀ᵐ p ∂μ.prod (Spherical.sphereLaw E), (L p.1).toContinuousLinearMap.adjoint p.2 ≠ 0 := by
  have hm : Measurable (fun p : Ω × E => (L p.1).toContinuousLinearMap.adjoint p.2) :=
    measurable_operator_apply ((measurable_operator_adjoint hL).comp measurable_fst) measurable_snd
  apply (Measure.ae_prod_iff_ae_ae (hm (measurableSet_singleton 0)).compl).mpr
  exact Filter.Eventually.of_forall (fun ω => Spherical.ae_adjoint_ne_zero (L ω))

theorem ambientPair_ae_nonzero {m : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (kind : ExposureKind)
    (F : Ω → ExposureFrame (Coordinates (m + 1)) E) (hF : ExposureFrame.MeasurableFamily F) :
    ∀ᵐ p ∂(μ.prod (Spherical.sphereLaw E)).prod (Spherical.sphereLaw E),
      (F p.1.1).latent.toContinuousLinearMap.adjoint p.1.2 ≠ 0 ∧
      ((F p.1.1).innovationEmbedding kind).toContinuousLinearMap.adjoint p.2 ≠ 0 := by
  letI : Nontrivial (Coordinates (m + 1)) := ⟨⟨firstDirection m, 0, firstDirection_ne_zero m⟩⟩
  haveI : SFinite (μ.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
  have haux := embedding_family_ae_nonzero μ (fun ω => (F ω).latent) hF.latent
  have hf : MeasurePreserving (Prod.fst : (Ω × E) × E → Ω × E)
      ((μ.prod (Spherical.sphereLaw E)).prod (Spherical.sphereLaw E)) (μ.prod (Spherical.sphereLaw E)) :=
    ⟨measurable_fst, by simp⟩
  have hg := embedding_family_ae_nonzero (μ.prod (Spherical.sphereLaw E))
    (fun p : Ω × E => (F p.1).innovationEmbedding kind)
    ((hF.innovationEmbedding kind).comp measurable_fst)
  filter_upwards [hf.quasiMeasurePreserving.ae haux, hg] with p ha hg
  exact ⟨ha, hg⟩

/-- Every finite padded execution is nondegenerate almost surely under the
actual independent ambient-pair law, despite the adaptive frame updates. -/
theorem ActionProgram.directAmbientGood_ae (d n : ℕ) {H Ω : Type u}
    [MeasurableSpace H] [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (plan : ActionProgram E n H) (F : Ω → ExposureFrame (Coordinates (d + n)) E)
    (hF : ExposureFrame.MeasurableFamily F) (history : Ω → H) (hh : Measurable history) :
    ∀ᵐ p ∂ambientPairHistoryLaw E n μ, plan.directAmbientGood d n F history p := by
  induction n generalizing H Ω with
  | zero => exact Filter.Eventually.of_forall (fun _ => trivial)
  | succ n ih =>
    let ν := (μ.prod (Spherical.sphereLaw E)).prod (Spherical.sphereLaw E)
    haveI : SFinite (μ.prod (Spherical.sphereLaw E)) := Measure.prod.instSFinite
    haveI : SFinite ν := Measure.prod.instSFinite
    have hhead := (AmbientPairHistory.seed_preserving (E := E) n ν).quasiMeasurePreserving.ae
      (ambientPair_ae_nonzero μ plan.1.kind F hF)
    have htail := ih ν plan.2 _
      (measurable_ambientFrameNext plan.1.kind F hF _ (plan.1.measurable_vector.comp hh))
      _ (measurable_ambientObservedHistory plan.1 F hF history hh)
    filter_upwards [hhead, htail] with p hp ht
    exact ⟨hp.1, hp.2, ht⟩

end RandomizedFO2003.Rotations
