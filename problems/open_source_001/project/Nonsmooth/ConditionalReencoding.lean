import Nonsmooth.ObservedBayes

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {α β γ Ω : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace Ω] [StandardBorelSpace β] [Nonempty β]

/-- Reversible measurable encodings of an observation yield the same conditional law. -/
theorem condDistrib_reencoding (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (hX : Measurable X) (Y : Ω → β) (hY : Measurable Y)
    (Z : Ω → γ) (hZ : Measurable Z)
    (f : α → γ) (hf : Measurable f) (g : γ → α) (hg : Measurable g)
    (hZX : ∀ a, Z a = f (X a)) (hXZ : ∀ a, g (Z a) = X a) :
    ∀ᵐ z ∂μ.map Z, condDistrib Y X μ (g z) = condDistrib Y Z μ z := by
  let κ := Kernel.comap (condDistrib Y X μ) g hg
  have hpair : Measurable (fun a : Ω => (Z a, Y a)) := hZ.prodMk hY
  have he : μ.map (fun a => (Z a, Y a)) = (μ.map Z) ⊗ₘ κ := by
    apply ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod
    · rintro _ ⟨S, hS, B, hB, rfl⟩
      change MeasurableSet S at hS
      change MeasurableSet B at hB
      rw [Measure.map_apply hpair (hS.prod hB), Measure.compProd_apply_prod hS hB]
      have hk : Measurable (fun z => κ z B) := κ.measurable_coe hB
      rw [setLIntegral_map hS hk hZ]
      change μ (Z ⁻¹' S ∩ Y ⁻¹' B) = ∫⁻ a in Z ⁻¹' S, condDistrib Y X μ (g (Z a)) B ∂μ
      have hpre : Z ⁻¹' S = X ⁻¹' (f ⁻¹' S) := by
        ext a
        change Z a ∈ S ↔ f (X a) ∈ S
        rw [hZX]
      rw [hpre]
      simp_rw [hXZ]
      exact (setLIntegral_preimage_condDistrib hX hY.aemeasurable hB (hf hS)).symm
    · rw [Measure.map_apply hpair MeasurableSet.univ, preimage_univ,
        Measure.compProd_apply_univ, Measure.map_apply hZ MeasurableSet.univ, preimage_univ]
  exact (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hZ hY he).symm

/-- Any almost-sure property of the posterior transfers across a reversible observation encoding. -/
theorem condDistrib_property_reencoding (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (hX : Measurable X) (Y : Ω → β) (hY : Measurable Y)
    (Z : Ω → γ) (hZ : Measurable Z)
    (f : α → γ) (hf : Measurable f) (g : γ → α) (hg : Measurable g)
    (hZX : ∀ a, Z a = f (X a)) (hXZ : ∀ a, g (Z a) = X a)
    (P : Measure β → Prop) (hP : ∀ᵐ x ∂μ.map X, P (condDistrib Y X μ x)) :
    ∀ᵐ z ∂μ.map Z, P (condDistrib Y Z μ z) := by
  have hgmap : (μ.map Z).map g = μ.map X := by
    rw [Measure.map_map hg hZ]
    congr 1
    funext a
    exact hXZ a
  rw [← hgmap] at hP
  have hpull := ae_of_ae_map hg.aemeasurable hP
  filter_upwards [hpull, condDistrib_reencoding μ X hX Y hY Z hZ f hf g hg hZX hXZ] with z hz he
  rw [← he]
  exact hz

end
end Nonsmooth
