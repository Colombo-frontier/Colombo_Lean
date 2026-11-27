import Nonsmooth.C2GaussianPlaneBase
import Nonsmooth.OrthogonalPairReduction
import Nonsmooth.ActualOrthogonalPotentialMarginal

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem c2_gaussian_regular_images_by_dimension (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
      Module.finrank ℝ E = n →
      ∀ {U : E → ℝ} {ρ : ℝ}, C2StrongQuadraticPotential U ρ → 1 < ρ →
      ∀ {u v : E}, ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 →
      Nonempty (RegularProjectionImage (gaussianPotentialLaw U) u v) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ _ _ _ hdim U ρ hU hρ u v hu hv ho
    by_cases hn : n = 2
    · exact c2_gaussian_plane_regular_image hU hρ (hdim.trans hn) hu hv ho
    · have hthree : 3 ≤ Module.finrank ℝ E := by
        have ht := finrank_two_le_of_orthonormal_pair hu hv ho
        omega
      obtain ⟨w, hw, huw, hvw⟩ := exists_unit_orthogonal_to_pair hu hv ho hthree
      let K : Submodule ℝ E := (ℝ ∙ w)ᗮ
      letI : BorelSpace K := Subtype.borelSpace _
      let uK : K := ⟨u, Submodule.mem_orthogonal_singleton_iff_inner_left.mpr huw⟩
      let vK : K := ⟨v, Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hvw⟩
      have huK : ‖uK‖ = 1 := hu
      have hvK : ‖vK‖ = 1 := hv
      have hoK : ⟪uK, vK⟫_ℝ = 0 := ho
      have hnK : uK ≠ 0 := by intro h; simp [h] at huK
      letI : Nontrivial K := nontrivial_of_ne uK 0 hnK
      have hdimK : Module.finrank ℝ K < n := by
        have h := unit_complement_finrank_drop hw
        dsimp only [K]
        omega
      let V : K → ℝ := fun t => -Real.log (∫ x : ℝ, Real.exp (-U ((t : E) + x • w)))
      have hV : C2StrongQuadraticPotential V ρ ∧
          (gaussianPotentialLaw U).map K.orthogonalProjection = gaussianPotentialLaw V :=
        c2StrongQuadraticPotential_actual_complement_marginal hU hρ hw
      obtain ⟨H⟩ := ih (Module.finrank ℝ K) hdimK rfl hV.1 hρ huK hvK hoK
      refine ⟨{
        potential := H.potential
        forward := H.forward
        backward := H.backward
        moments := H.moments
        law := ?_ }⟩
      have hcoord : (fun z : K => (⟪z, uK⟫_ℝ, ⟪vK, z⟫_ℝ)) ∘ K.orthogonalProjection =
          fun z : E => (⟪z, u⟫_ℝ, ⟪v, z⟫_ℝ) := by
        funext z
        exact Prod.ext (Submodule.inner_orthogonalProjection_eq_of_mem_right (K := K) uK z)
          (Submodule.inner_orthogonalProjection_eq_of_mem_left (K := K) vK z)
      rw [← hcoord, ← Measure.map_map (by fun_prop) K.orthogonalProjection.measurable, hV.2]
      exact H.law

/-- Actual regular two-dimensional projection images exist in every
finite dimension, with no projection-density hypothesis. -/
theorem c2StrongQuadraticPotential_regular_images
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {U : E → ℝ} {ρ : ℝ} (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : ⟪u, v⟫_ℝ = 0) :
    Nonempty (RegularProjectionImage (gaussianPotentialLaw U) u v) :=
  c2_gaussian_regular_images_by_dimension (Module.finrank ℝ E) rfl hU hρ hu hv ho

end
end Nonsmooth
