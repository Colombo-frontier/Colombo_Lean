import Bilevel.EquivariantKernel
import Mathlib.Probability.Kernel.CondDistrib

/-! Haar symmetrization retains the joint law while enforcing pointwise equivariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Bilevel.EquivariantDisintegration
open EquivariantKernel

variable {G X Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MeasurableSpace X] [MeasurableSpace Y] [MulAction G X] [MulAction G Y]
  [MeasurableSMul₂ G X] [MeasurableSMul₂ G Y]
  (ν : Measure G) [IsProbabilityMeasure ν]
  (ρ : Measure Y) [IsProbabilityMeasure ρ] (κ : Kernel Y X) [IsMarkovKernel κ]

omit [MeasurableMul₂ G] in
theorem joint_law_preserved
    (hp : ∀ g : G, MeasurePreserving (fun y : Y => g • y) ρ ρ)
    (hj : ∀ g : G, MeasurePreserving (fun p : Y × X => (g • p.1, g • p.2)) (ρ ⊗ₘ κ) (ρ ⊗ₘ κ)) :
    ρ ⊗ₘ average ν κ = ρ ⊗ₘ κ := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro F hF
  have hm : Measurable (fun p : G × Y => ∫⁻ x, F (p.2, p.1 • x) ∂κ (p.1⁻¹ • p.2)) := by
    have hh : Measurable (fun p : (G × Y) × X => F (p.1.2, p.1.1 • p.2)) :=
      hF.comp (measurable_fst.snd.prodMk (measurable_fst.fst.smul measurable_snd))
    exact hh.lintegral_kernel_prod_right' (κ := shifted κ)
  calc
    _ = ∫⁻ y, ∫⁻ x, F (y,x) ∂average ν κ y ∂ρ := Measure.lintegral_compProd hF
    _ = ∫⁻ y, ∫⁻ g, ∫⁻ x, F (y,g • x) ∂κ (g⁻¹ • y) ∂ν ∂ρ := by
      apply lintegral_congr
      intro y
      exact average_lintegral ν κ y _ (hF.comp measurable_prodMk_left)
    _ = ∫⁻ g, ∫⁻ y, ∫⁻ x, F (y,g • x) ∂κ (g⁻¹ • y) ∂ρ ∂ν :=
      lintegral_lintegral_swap (hm.comp measurable_swap).aemeasurable
    _ = ∫⁻ _g : G, (∫⁻ p, F p ∂ρ ⊗ₘ κ) ∂ν := by
      apply lintegral_congr
      intro g
      have hmg : Measurable (fun y : Y => ∫⁻ x, F (y,g • x) ∂κ (g⁻¹ • y)) :=
        hm.comp measurable_prodMk_left
      calc
        _ = ∫⁻ y, ∫⁻ x, F (g • y,g • x) ∂κ (g⁻¹ • (g • y)) ∂ρ :=
          ((hp g).lintegral_comp hmg).symm
        _ = ∫⁻ y, ∫⁻ x, F (g • y,g • x) ∂κ y ∂ρ := by simp only [inv_smul_smul]
        _ = ∫⁻ p, F (g • p.1,g • p.2) ∂ρ ⊗ₘ κ :=
          (Measure.lintegral_compProd
            (hF.comp ((measurable_const.smul measurable_fst).prodMk
              (measurable_const.smul measurable_snd)))).symm
        _ = _ := (hj g).lintegral_comp hF
    _ = _ := by simp

end Bilevel.EquivariantDisintegration
