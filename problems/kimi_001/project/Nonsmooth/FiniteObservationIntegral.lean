import Nonsmooth.RankTailEntropy

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Function
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem finite_first_integral {β F : Type} [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (ν : Measure (Fin k × β)) (f : Fin k × β → F)
    (hfm : StronglyMeasurable f) (hf : Integrable f ν) :
    (∫ h, f h ∂ν) = ∑ w : Fin k, ∫ y, f (w, y)
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
  have he := integral_iUnion_fintype hH hd (fun _ => hf.restrict)
  rw [hu, setIntegral_univ] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro w hw
  have hfw : StronglyMeasurable (fun y : β => f (w, y)) :=
    hfm.comp_measurable (measurable_const.prodMk measurable_id)
  rw [integral_map_of_stronglyMeasurable measurable_snd hfw]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := ν) (hH w)] with x hx
  change x.1 = w at hx
  rw [← hx]

theorem finiteProductKernel_sum_integral {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] {k : ℕ}
    (κ : Fin k → Kernel α E) [∀ i, IsMarkovKernel (κ i)] (x : α)
    (hi : ∀ i, Integrable (fun z : E => z) (κ i x)) :
    (∫ a : Fin k → E, ∑ i, a i ∂finiteProductKernel κ x) = ∑ i, ∫ z, z ∂κ i x := by
  have hco (i : Fin k) : Integrable (fun a : Fin k → E => a i) (finiteProductKernel κ x) := by
    apply (integrable_map_measure
      (stronglyMeasurable_id.aestronglyMeasurable : AEStronglyMeasurable (fun z : E => z)
        ((finiteProductKernel κ x).map (fun a : Fin k → E => a i)))
      (measurable_pi_apply i).aemeasurable).mp
    rw [finiteProductKernel_coordinate]
    exact hi i
  rw [integral_finsetSum _ (fun i _ => hco i)]
  apply Finset.sum_congr rfl
  intro i hi
  have he := integral_map_of_stronglyMeasurable (μ := finiteProductKernel κ x)
    (measurable_pi_apply i) (stronglyMeasurable_id : StronglyMeasurable (fun z : E => z))
  rw [finiteProductKernel_coordinate] at he
  exact he.symm

end
end Nonsmooth
