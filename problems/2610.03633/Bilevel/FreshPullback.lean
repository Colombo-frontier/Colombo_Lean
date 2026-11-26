import Bilevel.FreshOracle

/-! Transport actual centered errors to a larger random-seed space. -/

noncomputable section
open MeasureTheory

namespace Bilevel.FreshPullback

variable {Ω Ω' E : Type*} {pastΩ : MeasurableSpace Ω} {pastΩ' : MeasurableSpace Ω'}
  [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {ν : Measure Ω'}

omit [CompleteSpace E] in
theorem integral_pullback {T : Ω → Ω'} (hT : MeasurePreserving T μ ν)
    (f : Ω' → E) (hf : StronglyMeasurable f) :
    (∫ z, f (T z) ∂μ) = ∫ z, f z ∂ν := by
  have h := integral_map_of_stronglyMeasurable (μ := μ) hT.measurable hf
  rw [hT.map_eq] at h
  exact h.symm

omit [CompleteSpace E] in
theorem setIntegral_pullback {T : Ω → Ω'} (hT : MeasurePreserving T μ ν)
    (f : Ω' → E) (hf : StronglyMeasurable f) (s : Set Ω') (hs : MeasurableSet s) :
    (∫ z in T ⁻¹' s, f (T z) ∂μ) = ∫ z in s, f z ∂ν := by
  rw [← integral_indicator (hs.preimage hT.measurable), ← integral_indicator hs]
  have he : (fun z => (T ⁻¹' s).indicator (fun z => f (T z)) z) = fun z => s.indicator f (T z) := by
    funext z
    by_cases hz : T z ∈ s <;> simp [hz]
  rw [he]
  exact integral_pullback hT _ (hf.indicator hs)

theorem condExpL2_toLp_eq_zero (hm : pastΩ ≤ mΩ)
    (f : Ω → E) (hf : MemLp f 2 μ)
    (hzero : ∀ s, MeasurableSet[pastΩ] s → (∫ z in s, f z ∂μ) = 0) :
    (condExpL2 E ℝ hm (hf.toLp f) : Lp E 2 μ) = 0 := by
  apply Lp.ext
  refine Lp.ae_eq_of_forall_setIntegral_eq' ℝ hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hs => integrableOn_condExpL2_of_measure_ne_top hm hs.ne _)
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne) ?_
    (lpMeas.aestronglyMeasurable _) ?_
  · intro s hs hμs
    rw [integral_condExpL2_eq hm _ hs hμs.ne]
    rw [integral_congr_ae (ae_restrict_of_ae (s := s) hf.coeFn_toLp), hzero s hs]
    have hz := integral_congr_ae (ae_restrict_of_ae (s := s) (Lp.coeFn_zero E 2 μ))
    simpa only [Pi.zero_apply, integral_zero] using hz.symm
  · exact aestronglyMeasurable_zero.congr (Lp.coeFn_zero E 2 μ).symm

def pulledSpace {T : Ω → Ω'} (m : MeasurableSpace Ω') : MeasurableSpace Ω := m.comap T

theorem pulledSpace_le {T : Ω → Ω'} (hT : Measurable T)
    (hm : pastΩ' ≤ mΩ') : pulledSpace (T := T) pastΩ' ≤ mΩ :=
  (MeasurableSpace.comap_mono hm).trans hT.comap_le

theorem pullback_centered {T : Ω → Ω'} (hT : MeasurePreserving T μ ν)
    (hm : pastΩ' ≤ mΩ')
    (f : Ω' → E) (hf : MemLp f 2 ν) (hfm : StronglyMeasurable[mΩ'] f)
    (hzero : ∀ s, MeasurableSet[pastΩ'] s → (∫ z in s, f z ∂ν) = 0) :
    (condExpL2 E ℝ (pulledSpace_le hT.measurable hm)
      ((hf.comp_measurePreserving hT).toLp (f ∘ T)) : Lp E 2 μ) = 0 := by
  apply condExpL2_toLp_eq_zero
  intro s hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  change (∫ z in T ⁻¹' t, f (T z) ∂μ) = 0
  rw [setIntegral_pullback hT f hfm t (hm t ht)]
  exact hzero t ht

end Bilevel.FreshPullback
