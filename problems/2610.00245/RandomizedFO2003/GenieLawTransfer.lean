import RandomizedFO2003.RefreshGenie

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations Spherical
open scoped BigOperators

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))

noncomputable def publicCascadeLaw (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ) (i : Fin (N + 1)) :
    Measure (Coefficients N (BlockSpace K)) :=
  (S.cascadeParameterLaw K N).map (S.publicCascadeCoefficients K N h i)

instance publicCascadeLaw_probability (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ) (i : Fin (N + 1)) :
    IsProbabilityMeasure (S.publicCascadeLaw K N h i) :=
  isProbabilityMeasure_map (S.measurable_publicCascadeCoefficients K N h i).aemeasurable

variable {Seed : Type} [MeasurableSpace Seed]

theorem publicGenieInput_preserving (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ) (i : Fin (N + 1))
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving
      (fun p : (BlockSpace K × (Sample K N × Seed)) × Rotation (BlockSpace K) =>
        ((p.1.1, S.publicCascadeCoefficients K N h i p.1.2.1, p.1.2.2), p.2))
      (((sphereLaw (BlockSpace K)).prod ((S.cascadeParameterLaw K N).prod ν)).prod (haarLaw (BlockSpace K)))
      (((sphereLaw (BlockSpace K)).prod ((S.publicCascadeLaw K N h i).prod ν)).prod (haarLaw (BlockSpace K))) := by
  have hp : MeasurePreserving (S.publicCascadeCoefficients K N h i) (S.cascadeParameterLaw K N)
      (S.publicCascadeLaw K N h i) := ⟨S.measurable_publicCascadeCoefficients K N h i, rfl⟩
  exact ((MeasurePreserving.id (sphereLaw (BlockSpace K))).prod
    (hp.prod (MeasurePreserving.id ν))).prod (MeasurePreserving.id (haarLaw (BlockSpace K)))

/-- Exact equality of the original multi-block event probability with the
independent input probability to which the single-block Haar theorem
applies. No conditioning or replacement of the original hard distribution
is hidden in this step. -/
theorem censoredGenieGoodEvent_probability_eq (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1)) :
    ((S.cascadeParameterLaw K N).prod ν) (S.censoredGenieGoodEvent K N h A T i) =
      ((((sphereLaw (BlockSpace K)).prod ((S.publicCascadeLaw K N h i).prod ν)).prod (haarLaw (BlockSpace K))).map
        (fun p => ((S.censoredGenieProgram K N h A T i).compile (continuousDiagonal K S.node) (T + 1)
          Prod.fst measurable_fst).run (markedActionCount (T + 1))
            (p.2 : BlockSpace K →L[ℝ] BlockSpace K) p.1))
      (historyWeightEvent K S.weight (T + 1) Prod.fst (1 / 32) ∩
        (S.censoredGenieProgram K N h A T i).prefixFlatEvent K S.residual m (T + 1) Prod.fst
          (radiusCoefficient * h / γ) (h / (64 * γ))) := by
  let plan := S.censoredGenieProgram K N h A T i
  let run := fun p : (BlockSpace K × (Coefficients N (BlockSpace K) × Seed)) × Rotation (BlockSpace K) =>
    (plan.compile (continuousDiagonal K S.node) (T + 1) Prod.fst measurable_fst).run
      (markedActionCount (T + 1)) (p.2 : BlockSpace K →L[ℝ] BlockSpace K) p.1
  let good := historyWeightEvent K S.weight (T + 1) Prod.fst (1 / 32) ∩
    plan.prefixFlatEvent K S.residual m (T + 1) Prod.fst (radiusCoefficient * h / γ) (h / (64 * γ))
  have hgood : MeasurableSet good :=
    (measurableSet_historyWeightEvent K S.weight (T + 1) Prod.fst measurable_fst (1 / 32)).inter
      (plan.measurableSet_prefixFlatEvent K S.residual m (T + 1) Prod.fst measurable_fst _ _)
  have hrun : Measurable run := (plan.compile (continuousDiagonal K S.node) (T + 1) Prod.fst measurable_fst).run_family_measurable
    (markedActionCount (T + 1)) _ (measurable_subtype_coe.comp measurable_snd) _ measurable_fst
  let refresh := fun p : (BlockSpace K × (Sample K N × Seed)) × Rotation (BlockSpace K) =>
    (refreshSample K N i p.1.2.1 p.1.1 p.2, p.1.2.2)
  let input := fun p : (BlockSpace K × (Sample K N × Seed)) × Rotation (BlockSpace K) =>
    ((p.1.1, S.publicCascadeCoefficients K N h i p.1.2.1, p.1.2.2), p.2)
  have hpre : refresh ⁻¹' S.censoredGenieGoodEvent K N h A T i = input ⁻¹' (run ⁻¹' good) := by
    ext p
    change S.censoredGenieHistory K N h A T i
        (refreshSample K N i p.1.2.1 p.1.1 p.2).1 (refreshSample K N i p.1.2.1 p.1.1 p.2).2 p.1.2.2 ∈ good ↔ _
    rw [S.censoredGenieHistory_refresh]
    rfl
  calc
    _ = (((sphereLaw (BlockSpace K)).prod ((S.cascadeParameterLaw K N).prod ν)).prod (haarLaw (BlockSpace K)))
        (refresh ⁻¹' S.censoredGenieGoodEvent K N h A T i) :=
      ((S.refreshSample_seed_preserving K N ν i).measure_preimage
        (S.measurableSet_censoredGenieGoodEvent K N h A T i).nullMeasurableSet).symm
    _ = (((sphereLaw (BlockSpace K)).prod ((S.cascadeParameterLaw K N).prod ν)).prod (haarLaw (BlockSpace K)))
        (input ⁻¹' (run ⁻¹' good)) := by rw [hpre]
    _ = (((sphereLaw (BlockSpace K)).prod ((S.publicCascadeLaw K N h i).prod ν)).prod (haarLaw (BlockSpace K)))
        (run ⁻¹' good) :=
      (S.publicGenieInput_preserving K N h i ν).measure_preimage (hgood.preimage hrun).nullMeasurableSet
    _ = _ := (Measure.map_apply hrun hgood).symm

end RandomizedFO2003.FiniteSpectralDesign
