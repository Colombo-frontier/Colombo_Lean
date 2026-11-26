import NCConcave16991.MixedHaarGaussianReservoir
import NCConcave16991.ConditionalHaarColumns
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # The measurable reservoir score is the actual orthogonal projection -/

noncomputable section

open Set MeasureTheory InnerProductSpace
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {m : ℕ}

def reservoirSpan (f : Fin m → E) : Submodule ℝ E := Submodule.span ℝ (Set.range f)

def reservoirProjection (f : Fin m → E) (e : E) : E :=
  ∑ i, ⟪gramSchmidtNormed ℝ f i,e⟫_ℝ • gramSchmidtNormed ℝ f i

theorem normalized_span_eq (f : Fin m → E) :
    Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ f)) = reservoirSpan f :=
  (span_gramSchmidtNormed_range (𝕜 := ℝ) f).trans (span_gramSchmidt ℝ f)

theorem normalized_mem_span (f : Fin m → E) (i : Fin m) :
    gramSchmidtNormed ℝ f i ∈ reservoirSpan f := by
  rw [← normalized_span_eq]
  exact Submodule.subset_span (Set.mem_range_self i)

theorem normalized_pairwise_orthogonal (f : Fin m → E) {i j : Fin m} (hij : i ≠ j) :
    ⟪gramSchmidtNormed ℝ f i, gramSchmidtNormed ℝ f j⟫_ℝ = 0 := by
  simp only [gramSchmidtNormed, real_inner_smul_left, real_inner_smul_right,
    RCLike.ofReal_real_eq_id, id_eq, gramSchmidt_orthogonal ℝ f hij, mul_zero]

theorem normalized_inner_projection (f : Fin m → E) (e : E) (i : Fin m) :
    ⟪gramSchmidtNormed ℝ f i,reservoirProjection f e⟫_ℝ = ⟪gramSchmidtNormed ℝ f i,e⟫_ℝ := by
  unfold reservoirProjection
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_right]
    by_cases hz : gramSchmidtNormed ℝ f i = 0
    · simp only [hz, inner_zero_left, mul_zero]
    · rw [real_inner_self_eq_norm_sq, gramSchmidtNormed_unit_length' hz]
      norm_num
  · intro j _ hji
    rw [real_inner_smul_right, normalized_pairwise_orthogonal f hji.symm, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem reservoirProjection_eq_starProjection (f : Fin m → E) (e : E) :
    (reservoirSpan f).starProjection e = reservoirProjection f e := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _ (normalized_mem_span f i))
  · intro w hw
    rw [← normalized_span_eq] at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i,rfl⟩ := hw
      rw [inner_sub_left]
      rw [show ⟪e,gramSchmidtNormed ℝ f i⟫_ℝ = ⟪gramSchmidtNormed ℝ f i,e⟫_ℝ from real_inner_comm _ _,
        show ⟪reservoirProjection f e,gramSchmidtNormed ℝ f i⟫_ℝ =
          ⟪gramSchmidtNormed ℝ f i,reservoirProjection f e⟫_ℝ from real_inner_comm _ _,
        normalized_inner_projection, sub_self]
    | zero => simp
    | add a b ha hb iha ihb => simp only [inner_add_right, iha, ihb, add_zero]
    | smul a w hw ih => simp only [real_inner_smul_right, ih, mul_zero]

theorem reservoirScore_eq_projection_norm_sq (f : Fin m → E) (e : E) :
    reservoirScore f e = ‖(reservoirSpan f).orthogonalProjectionOnto e‖ ^ 2 := by
  have he : ⟪reservoirProjection f e,e⟫_ℝ = reservoirScore f e := by
    simp only [reservoirProjection, sum_inner, real_inner_smul_left, reservoirScore, pow_two]
  have hh := (reservoirSpan f).re_inner_starProjection_eq_normSq e
  rw [reservoirProjection_eq_starProjection, he] at hh
  simpa only [RCLike.re_to_real] using hh

theorem coordinateScore_eq_projection_norm_sq {D : ℕ} (f : Reservoir m D) (i : Fin D) :
    coordinateScore f i = ‖(reservoirSpan f).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2 := by
  rw [← reservoirScore_eq_projection_norm_sq]
  simp only [reservoirScore, coordinateScore, Haar.basisVector, EuclideanSpace.inner_single_right,
    RCLike.conj_to_real, mul_one, one_mul]

theorem gaussian_projection_expectation_le {D : ℕ} (hD : 0 < D) (i : Fin D) :
    (∫ f : Reservoir m D, ‖(reservoirSpan f).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2
      ∂gaussianReservoirLaw m D) ≤ (m : ℝ) / D := by
  simp_rw [← coordinateScore_eq_projection_norm_sq]
  exact coordinateScore_expectation_le hD i

end NCConcave16991.MixedHaar
