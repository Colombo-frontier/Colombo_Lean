import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! # Measurable and equivariant Gram-Schmidt for the actual nuisance reservoir -/

noncomputable section

open Set MeasureTheory InnerProductSpace
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 1000000

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]
  {m : ℕ}

theorem gramSchmidt_measurable (i : Fin m) :
    Measurable (fun f : Fin m → E ↦ gramSchmidt ℝ f i) := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    have hs : Measurable (fun f : Fin m → E ↦
        ∑ j ∈ Finset.Iio i,
          (⟪gramSchmidt ℝ f j, f i⟫_ℝ / ‖gramSchmidt ℝ f j‖ ^ 2) • gramSchmidt ℝ f j) := by
      apply Finset.measurable_sum
      intro j hj
      have hg := ih j (Finset.mem_Iio.mp hj)
      exact ((hg.inner (measurable_pi_apply i)).div (hg.norm.pow_const 2)).smul hg
    convert (measurable_pi_apply i).sub hs using 1
    funext f
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton, Pi.sub_apply, RCLike.ofReal_real_eq_id, id_eq]

theorem gramSchmidtNormed_measurable (i : Fin m) :
    Measurable (fun f : Fin m → E ↦ gramSchmidtNormed ℝ f i) := by
  have hg := gramSchmidt_measurable (E := E) i
  exact hg.norm.inv.smul hg

theorem gramSchmidt_isometry (U : E ≃ₗᵢ[ℝ] F) (f : Fin m → E) (i : Fin m) :
    gramSchmidt ℝ (fun j ↦ U (f j)) i = U (gramSchmidt ℝ f i) := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    rw [gramSchmidt_def, gramSchmidt_def, map_sub, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j (Finset.mem_Iio.mp hj)]
    simp only [Submodule.starProjection_singleton, U.inner_map_map, U.norm_map, map_smul]

theorem gramSchmidtNormed_isometry (U : E ≃ₗᵢ[ℝ] F) (f : Fin m → E) (i : Fin m) :
    gramSchmidtNormed ℝ (fun j ↦ U (f j)) i = U (gramSchmidtNormed ℝ f i) := by
  simp only [gramSchmidtNormed, gramSchmidt_isometry, U.norm_map, map_smul]

theorem gramSchmidtNormed_norm_le (f : Fin m → E) (i : Fin m) :
    ‖gramSchmidtNormed ℝ f i‖ ≤ 1 := by
  by_cases h : gramSchmidtNormed ℝ f i = 0
  · simp only [h, norm_zero]
    norm_num
  · exact (gramSchmidtNormed_unit_length' h).le

def reservoirScore (f : Fin m → E) (e : E) : ℝ :=
  ∑ i, ⟪gramSchmidtNormed ℝ f i,e⟫_ℝ ^ 2

theorem reservoirScore_nonneg (f : Fin m → E) (e : E) : 0 ≤ reservoirScore f e :=
  Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)

theorem reservoirScore_measurable (e : E) : Measurable (fun f : Fin m → E ↦ reservoirScore f e) := by
  apply Finset.measurable_sum
  intro i _
  exact ((gramSchmidtNormed_measurable i).inner measurable_const).pow_const 2

end NCConcave16991.MixedHaar
