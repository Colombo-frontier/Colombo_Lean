import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod

/-! # Exact measurable-selector factorization of a genuine invariant law

A measurable representative of each observed right coset, followed by an
independent Haar stabilizer element, has exactly the original invariant law.
This is the generative one-reveal identity used in lazy completions.
-/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableMul₂ G]
  (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulRightInvariant μ]
  (H : Subgroup G) (ν : Measure H) [IsProbabilityMeasure ν] [Measure.IsMulLeftInvariant ν]

theorem coset_selector_completion_preserving (select : G → G) (hs : Measurable select)
    (hcoset : ∀ Q, Q⁻¹ * select Q ∈ H) :
    MeasurePreserving (fun p : G × H ↦ select p.1 * p.2.val) (μ.prod ν) μ := by
  letI : MeasurableMul₂ H := ⟨by
    apply Measurable.subtype_mk
    exact (measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)⟩
  have hm : Measurable (fun p : G × H ↦ select p.1 * p.2.val) :=
    (hs.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hm hE, Measure.prod_apply (hE.preimage hm)]
  change (∫⁻ Q, ν {h : H | select Q * h.val ∈ E} ∂μ) = μ E
  have hpoint (Q : G) :
      ν {h : H | select Q * h.val ∈ E} = ν {h : H | Q * h.val ∈ E} := by
    let h₀ : H := ⟨Q⁻¹ * select Q, hcoset Q⟩
    let F : Set H := {h | Q * h.val ∈ E}
    have hF : MeasurableSet F := hE.preimage (measurable_const.mul measurable_subtype_coe)
    have he : {h : H | select Q * h.val ∈ E} = (fun h : H ↦ h₀ * h) ⁻¹' F := by
      ext h
      simp only [mem_preimage, F, mem_setOf_eq, Subgroup.coe_mul, h₀]
      simp only [mul_inv_cancel_left, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [he, ← Measure.map_apply (measurable_const_mul h₀) hF,
      (measurePreserving_mul_left ν h₀).map_eq]
  simp_rw [hpoint]
  have hmul : Measurable (fun p : G × H ↦ p.1 * p.2.val) :=
    measurable_fst.mul (measurable_subtype_coe.comp measurable_snd)
  have hME : MeasurableSet {p : G × H | p.1 * p.2.val ∈ E} := hE.preimage hmul
  have hp : (μ.prod ν) {p : G × H | p.1 * p.2.val ∈ E} =
      ∫⁻ Q, ν {h : H | Q * h.val ∈ E} ∂μ := Measure.prod_apply hME
  rw [← hp, Measure.prod_apply_symm hME]
  change (∫⁻ h : H, μ {Q : G | Q * h.val ∈ E} ∂ν) = μ E
  have hright (h : H) : μ {Q : G | Q * h.val ∈ E} = μ E := by
    change μ ((fun Q : G ↦ Q * h.val) ⁻¹' E) = μ E
    rw [← Measure.map_apply (measurable_mul_const h.val) hE,
      (measurePreserving_mul_right μ h.val).map_eq]
  simp_rw [hright]
  simp

end NCConcave16991.MixedHaar
