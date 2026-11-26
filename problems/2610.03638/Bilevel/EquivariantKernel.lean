import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Group.LIntegral

/-! Haar averaging of a measurable Markov kernel under two group actions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Bilevel.EquivariantKernel

variable {G X Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MeasurableSpace X] [MeasurableSpace Y] [MulAction G X] [MulAction G Y]
  [MeasurableSMul₂ G X] [MeasurableSMul₂ G Y]

def shifted (κ : Kernel Y X) : Kernel (G × Y) X :=
  κ.comap (fun p => p.1⁻¹ • p.2) (measurable_fst.inv.smul measurable_snd)

def rotated (κ : Kernel Y X) : Kernel (G × Y) X :=
  ((Kernel.deterministic Prod.fst measurable_fst) ×ₖ shifted κ).map
    (fun p : G × X => p.1 • p.2)

instance shifted_markov (κ : Kernel Y X) [IsMarkovKernel κ] : IsMarkovKernel (shifted (G := G) κ) :=
  inferInstanceAs (IsMarkovKernel (κ.comap _ _))

instance rotated_markov (κ : Kernel Y X) [IsMarkovKernel κ] : IsMarkovKernel (rotated (G := G) κ) :=
  Kernel.IsMarkovKernel.map _ (measurable_fst.smul measurable_snd)

def average (ν : Measure G) (κ : Kernel Y X) : Kernel Y X :=
  rotated κ ∘ₖ ((Kernel.const Y ν) ×ₖ Kernel.id)

instance average_markov (ν : Measure G) [IsProbabilityMeasure ν]
    (κ : Kernel Y X) [IsMarkovKernel κ] : IsMarkovKernel (average ν κ) :=
  inferInstanceAs (IsMarkovKernel (rotated κ ∘ₖ ((Kernel.const Y ν) ×ₖ Kernel.id)))

omit [MeasurableMul₂ G] in
theorem rotated_lintegral (κ : Kernel Y X) [IsMarkovKernel κ]
    (g : G) (y : Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂rotated κ (g,y)) = ∫⁻ x, f (g • x) ∂κ (g⁻¹ • y) := by
  rw [rotated, Kernel.lintegral_map _ (measurable_fst.smul measurable_snd) _ hf]
  have hm : Measurable (fun p : G × X => f (p.1 • p.2)) :=
    hf.comp (measurable_fst.smul measurable_snd)
  exact Kernel.lintegral_deterministic_prod (f := (Prod.fst : G × Y → G))
    measurable_fst (shifted κ) (g,y) hm

omit [MeasurableMul₂ G] in
theorem average_lintegral (ν : Measure G) [IsProbabilityMeasure ν]
    (κ : Kernel Y X) [IsMarkovKernel κ] (y : Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂average ν κ y) = ∫⁻ g, ∫⁻ x, f (g • x) ∂κ (g⁻¹ • y) ∂ν := by
  rw [average, Kernel.lintegral_comp _ _ _ hf]
  rw [Kernel.lintegral_prod_id hf.lintegral_kernel _ _]
  simp only [Kernel.const_apply, rotated_lintegral κ _ _ f hf]

theorem average_lintegral_equivariant (ν : Measure G) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (a : G) (y : Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂average ν κ (a • y)) = ∫⁻ x, f (a • x) ∂average ν κ y := by
  rw [average_lintegral ν κ (a • y) f hf]
  have hm : Measurable (fun x : X => f (a • x)) := hf.comp (measurable_const.smul measurable_id)
  calc
    _ = ∫⁻ g, ∫⁻ x, f ((a*g) • x) ∂κ ((a*g)⁻¹ • (a • y)) ∂ν :=
      (lintegral_mul_left_eq_self
        (fun g : G => ∫⁻ x, f (g • x) ∂κ (g⁻¹ • (a • y))) a).symm
    _ = ∫⁻ g, ∫⁻ x, f (a • (g • x)) ∂κ (g⁻¹ • y) ∂ν := by
      simp only [mul_smul, mul_inv_rev, inv_smul_smul]
    _ = _ := (average_lintegral ν κ y (fun x => f (a • x)) hm).symm

theorem average_equivariant (ν : Measure G) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (a : G) (y : Y) :
    average ν κ (a • y) = (average ν κ y).map (fun x : X => a • x) := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hm : Measurable (fun x : X => a • x) := measurable_const.smul measurable_id
  rw [MeasureTheory.lintegral_map hf hm]
  exact average_lintegral_equivariant ν κ a y f hf

theorem isotropy_preserving (ν : Measure G) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (a : G) (y : Y) (hy : a • y = y) :
    MeasurePreserving (fun x : X => a • x) (average ν κ y) (average ν κ y) := by
  refine ⟨measurable_const.smul measurable_id, ?_⟩
  have h := average_equivariant ν κ a y
  rw [hy] at h
  exact h.symm

end Bilevel.EquivariantKernel
