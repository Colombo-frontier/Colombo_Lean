import RandomizedFO2003.ExposureFrame

namespace RandomizedFO2003.Rotations

open MeasureTheory

variable {Ω E S T : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]

omit [FiniteDimensional ℝ E] in
theorem measurable_operator_comp {P : Ω → S →L[ℝ] E} {Q : Ω → T →L[ℝ] S}
    (hP : Measurable P) (hQ : Measurable Q) : Measurable (fun ω => (P ω).comp (Q ω)) := by
  have hc : Continuous (fun p : (S →L[ℝ] E) × (T →L[ℝ] S) => p.1.comp p.2) := by
    change Continuous (fun p : (S →L[ℝ] E) × (T →L[ℝ] S) =>
      ContinuousLinearMap.compSL T S E (RingHom.id ℝ) (RingHom.id ℝ) p.1 p.2)
    fun_prop
  exact hc.measurable.comp (hP.prodMk hQ)

theorem measurable_operator_adjoint {P : Ω → S →L[ℝ] E} (hP : Measurable P) :
    Measurable (fun ω => (P ω).adjoint) :=
  ContinuousLinearMap.adjoint.continuous.measurable.comp hP

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] [BorelSpace S]

omit [FiniteDimensional ℝ E] in
theorem measurable_operator_apply {P : Ω → S →L[ℝ] E} {x : Ω → S}
    (hP : Measurable P) (hx : Measurable x) : Measurable (fun ω => P ω (x ω)) := by
  have hc : Continuous (fun p : (S →L[ℝ] E) × S => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact hc.measurable.comp (hP.prodMk hx)

omit [MeasurableSpace S] [BorelSpace S] in
theorem measurable_rankOne {a b : Ω → E} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => rankOne (a ω) (b ω)) := by
  have hc : Continuous (fun p : E × E => rankOne p.1 p.2) := by
    change Continuous (fun p : E × E => ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ p.2) p.1)
    fun_prop
  exact hc.measurable.comp (ha.prodMk hb)

/-- Measurability of the three concrete operator fields; no measurable-space
structure on the type of isometric embeddings is postulated. -/
structure ExposureFrame.MeasurableFamily (F : Ω → ExposureFrame S E) : Prop where
  physical : Measurable (fun ω => (F ω).physical.toContinuousLinearMap)
  latent : Measurable (fun ω => (F ω).latent.toContinuousLinearMap)
  known : Measurable (fun ω => (F ω).known)

theorem ExposureFrame.MeasurableFamily.refine {F : Ω → ExposureFrame S E}
    (hF : ExposureFrame.MeasurableFamily F) (e : S) {A B : Ω → Rotation S}
    (hA : Measurable A) (hB : Measurable B) :
    ExposureFrame.MeasurableFamily (fun ω => (F ω).refine e (A ω) (B ω)) := by
  have hAc : Measurable (fun ω => (complementEmbedding e (A ω)).toContinuousLinearMap) := by
    change Measurable (fun ω => (A ω : S →L[ℝ] S).comp (Submodule.span ℝ {e})ᗮ.subtypeL)
    exact measurable_operator_comp (measurable_subtype_coe.comp hA) measurable_const
  have hBc : Measurable (fun ω => (complementEmbedding e (B ω)).toContinuousLinearMap) := by
    change Measurable (fun ω => (B ω : S →L[ℝ] S).comp (Submodule.span ℝ {e})ᗮ.subtypeL)
    exact measurable_operator_comp (measurable_subtype_coe.comp hB) measurable_const
  refine ⟨measurable_operator_comp hF.physical hAc, measurable_operator_comp hF.latent hBc, ?_⟩
  exact hF.known.add (measurable_rankOne
    (measurable_operator_apply hF.physical ((measurable_orbit S e).comp hA))
    (measurable_operator_apply hF.latent ((measurable_orbit S e).comp hB)))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace S] [BorelSpace S] in
theorem ExposureFrame.MeasurableFamily.comp {F : Ω → ExposureFrame S E}
    (hF : ExposureFrame.MeasurableFamily F) {Ω' : Type*} [MeasurableSpace Ω']
    {f : Ω' → Ω} (hf : Measurable f) : ExposureFrame.MeasurableFamily (F ∘ f) :=
  ⟨hF.physical.comp hf, hF.latent.comp hf, hF.known.comp hf⟩

end RandomizedFO2003.Rotations
