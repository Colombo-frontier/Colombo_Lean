import RandomizedFO2003.CascadePublicOracle

namespace RandomizedFO2003.Cascade

open Primitives MeasureTheory

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def decoderCoefficients (p : Coefficients N E) (i : Fin (N + 1)) (b : E) : Coefficients N E :=
  (Function.update p.1 i 0, Function.update p.2.1 i 0, Function.update p.2.2 i b)

theorem continuous_decoderCoefficients (i : Fin (N + 1)) :
    Continuous (fun p : Coefficients N E × E => decoderCoefficients p.1 i p.2) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [decoderCoefficients, Function.update_self] using
        (continuous_const : Continuous (fun _ : Coefficients N E × E => (0 : E →L[ℝ] E)))
    · simpa only [decoderCoefficients, Function.update_of_ne hji] using
        (continuous_apply j).comp continuous_fst.fst
  · apply Continuous.prodMk
    · apply continuous_pi
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [decoderCoefficients, Function.update_self] using
          (continuous_const : Continuous (fun _ : Coefficients N E × E => (0 : E)))
      · simpa only [decoderCoefficients, Function.update_of_ne hji] using
          (continuous_apply j).comp continuous_fst.snd.fst
    · apply continuous_pi
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [decoderCoefficients, Function.update_self] using
          (continuous_snd : Continuous (fun p : Coefficients N E × E => p.2))
      · simpa only [decoderCoefficients, Function.update_of_ne hji] using
          (continuous_apply j).comp continuous_fst.snd.snd

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

attribute [local instance] blockProductMeasurableSpace blockProductBorelSpace

/-- Joint measurability in public coefficients, both answers, and the full
query. This also covers zero answers and degenerate coefficient arrays. -/
theorem coefficients_reconstruct_measurable (i : Fin (N + 1)) (B α D C₀ K : ℝ) :
    Measurable (fun p : ((Coefficients N E × E) × E) × BlockProduct (N + 1) E =>
      (coefficientsData N E p.1.1.1 B α D C₀ K).reconstruct i p.1.1.2 p.1.2 p.2) := by
  letI : BorelSpace (Coefficients N E) := Prod.borelSpace
  have hp : Measurable (fun p : ((Coefficients N E × E) × E) × BlockProduct (N + 1) E =>
      (decoderCoefficients p.1.1.1 i p.1.1.2, p.2)) :=
    (((continuous_decoderCoefficients i).measurable.comp measurable_fst.fst).prodMk measurable_snd)
  have he := (coefficients_energy_continuous (N := N) (E := E) B α D C₀ K).measurable.comp hp
  have hg := (coefficients_gradient_measurable (N := N) (E := E) B α D C₀ K).comp hp
  have hx : Measurable (fun p : ((Coefficients N E × E) × E) × BlockProduct (N + 1) E => p.2 i) :=
    (blockProjection (E := E) (N + 1) i).continuous.measurable.comp measurable_snd
  have hi : Measurable (fun p : ((Coefficients N E × E) × E) × BlockProduct (N + 1) E =>
      (1 / 2 : ℝ) * inner (𝕜 := ℝ) (p.2 i) p.1.2) :=
    measurable_const.mul ((continuous_inner.measurable).comp (hx.prodMk measurable_fst.snd))
  have hb : Measurable (fun p : ((Coefficients N E × E) × E) × BlockProduct (N + 1) E =>
      blockEmbed i p.1.2) := by
    simpa only [Function.comp_def, blockProjection_adjoint] using
      (blockProjection (E := E) (N + 1) i).adjoint.continuous.measurable.comp
        (measurable_fst.snd : Measurable (fun p : ((Coefficients N E × E) × E) × BlockProduct (N + 1) E => p.1.2))
  exact (he.add hi).prodMk (hg.add hb)

theorem coefficients_oracleAuthorized_measurable (i : Fin (N + 1)) (B α D C₀ K : ℝ) :
    Measurable (fun p : Coefficients N E × BlockProduct (N + 1) E =>
      (coefficientsData N E p.1 B α D C₀ K).oracleAuthorized i p.2) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · apply measurable_to_bool
    have ha : Continuous (fun p : Coefficients N E × BlockProduct (N + 1) E => p.1.2.1 j.castSucc) :=
      (continuous_apply j.castSucc).comp continuous_fst.snd.fst
    have hx : Continuous (fun p : Coefficients N E × BlockProduct (N + 1) E => p.2 j.castSucc) :=
      (blockProjection (E := E) (N + 1) j.castSucc).continuous.comp continuous_snd
    have hr : Continuous (fun p : Coefficients N E × BlockProduct (N + 1) E =>
        |radialReadout (p.1.2.1 j.castSucc) B α (p.2 j.castSucc)|) :=
      ((ha.inner ((radialSquash_contDiff B 0).continuous.comp hx)).div_const α).abs
    have hs : MeasurableSet {p : Coefficients N E × BlockProduct (N + 1) E |
        (1 / 4 : ℝ) < |radialReadout (p.1.2.1 j.castSucc) B α (p.2 j.castSucc)|} :=
      measurableSet_lt measurable_const hr.measurable
    convert hs using 1
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Data.oracleAuthorized_succ, Set.mem_setOf_eq]
    rfl

end RandomizedFO2003.Cascade
