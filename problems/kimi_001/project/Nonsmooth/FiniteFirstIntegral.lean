import Nonsmooth.SelectionMeasure

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Function
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {β : Type} [MeasurableSpace β] {k : ℕ}

theorem finite_first_lintegral (ν : Measure (Fin k × β))
    (f : Fin k × β → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂ν) = ∑' w : Fin k, ∫⁻ y, f (w, y)
      ∂((ν.restrict (Prod.fst ⁻¹' {w})).map Prod.snd) := by
  let H : Fin k → Set (Fin k × β) := fun w => Prod.fst ⁻¹' {w}
  have hH (w : Fin k) : MeasurableSet (H w) := measurable_fst (measurableSet_singleton w)
  have hd : Pairwise (Disjoint on H) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.symm.trans hj)
  have hu : (⋃ w, H w) = Set.univ := by
    ext x
    exact ⟨fun _ => mem_univ x, fun _ => mem_iUnion.mpr ⟨x.1, rfl⟩⟩
  have he := lintegral_iUnion hH hd (f := f) (μ := ν)
  rw [hu, setLIntegral_univ] at he
  rw [he]
  apply tsum_congr
  intro w
  have hfw : Measurable (fun y : β => f (w, y)) := hf.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map hfw measurable_snd]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (hH w)] with x hx
  change x.1 = w at hx
  rw [← hx]

theorem finite_first_setLIntegral (ν : Measure (Fin k × β))
    {S : Set (Fin k × β)} (hS : MeasurableSet S)
    (f : Fin k × β → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in S, f x ∂ν) = ∑' w : Fin k, ∫⁻ y in Prod.mk w ⁻¹' S, f (w, y)
      ∂((ν.restrict (Prod.fst ⁻¹' {w})).map Prod.snd) := by
  rw [← lintegral_indicator hS, finite_first_lintegral ν _ (hf.indicator hS)]
  apply tsum_congr
  intro w
  rw [← lintegral_indicator (measurable_prodMk_left hS)]
  apply lintegral_congr
  intro y
  by_cases hy : (w, y) ∈ S
  · simp [hy]
  · simp [hy]

end
end Nonsmooth
