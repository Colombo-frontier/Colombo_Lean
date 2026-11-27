import Nonsmooth.MaximalDeterminantBasis
import Nonsmooth.OrthonormalBallSandwich

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- A symmetric full-dimensional compact convex body has a polynomial ball sandwich. -/
theorem exists_symmetric_body_normalization {S : Set E} (hconv : Convex ℝ S)
    (hcompact : IsCompact S) (hzero : (0 : E) ∈ S) (hsym : ∀ x ∈ S, -x ∈ S)
    {r : ℝ} (hr : 0 < r) (hinner : Metric.closedBall (0 : E) r ⊆ S) :
    ∃ L : E ≃L[ℝ] E,
      Metric.closedBall (0 : E) (1 / (Module.finrank ℝ E : ℝ)) ⊆ L '' S ∧
      L '' S ⊆ Metric.closedBall (0 : E) (Module.finrank ℝ E : ℝ) := by
  obtain ⟨b, hb, hcoords⟩ := exists_maximal_determinant_basis hcompact hr hinner
  let e := stdOrthonormalBasis ℝ E
  let L : E ≃L[ℝ] E := (b.equiv e.toBasis (Equiv.refl _)).toContinuousLinearEquiv
  refine ⟨L, ?_, ?_⟩
  · have hconv' : Convex ℝ (L '' S) := hconv.linear_image L.toLinearMap
    have hzero' : (0 : E) ∈ L '' S := ⟨0, hzero, map_zero L⟩
    have hsym' : ∀ x ∈ L '' S, -x ∈ L '' S := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨-y, hsym y hy, map_neg L y⟩
    have he : ∀ i, e i ∈ L '' S := by
      intro i
      refine ⟨b i, hb i, ?_⟩
      change b.equiv e.toBasis (Equiv.refl _) (b i) = e i
      simp
    simpa only [Fintype.card_fin] using symmetric_convex_contains_small_ball e
      (by simpa only [Fintype.card_fin] using (Module.finrank_pos : 0 < Module.finrank ℝ E))
      hconv' hzero' hsym' he
  · rintro z ⟨x, hx, rfl⟩
    have h := basis_change_norm_bound b e (hcoords x hx)
    simp only [Metric.mem_closedBall, dist_zero_right]
    convert! h using 1 <;> simp only [Fintype.card_fin]

end
end Nonsmooth
