import Nonsmooth.ActualOrthogonalPotentialMarginal
import Nonsmooth.SpanningGaussianPotentialLaw
import Nonsmooth.OrthogonalPlaneBounds

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem c2_gaussian_unit_marginal_by_dimension (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
      Module.finrank ℝ E = n →
      ∀ {U : E → ℝ} {ρ : ℝ}, C2StrongQuadraticPotential U ρ → 1 < ρ →
      ∀ {v : E}, ‖v‖ = 1 →
      ∃ W : ℝ → ℝ, C2StrongQuadraticPotential W ρ ∧
        (gaussianPotentialLaw U).map (fun z : E => ⟪v, z⟫_ℝ) =
          realDensityLaw (fun x => Real.exp (-W x)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ _ _ _ hdim U ρ hU hρ v hv
    by_cases hn : n = 1
    · let W : ℝ → ℝ := fun x => U (x • v)
      refine ⟨W, ?_, ?_⟩
      · exact c2StrongQuadraticPotential_isometry_pullback hU
          (LinearIsometry.toSpanSingleton ℝ E hv)
      · exact gaussianPotentialLaw_spanning_unit_marginal U hU.smooth.continuous.measurable hv
          (unit_spans_of_finrank_one hv (hdim.trans hn))
    · have htwo : 2 ≤ Module.finrank ℝ E := by
        have hp : 0 < Module.finrank ℝ E := Module.finrank_pos
        omega
      obtain ⟨u, hu, hvu⟩ := exists_unit_orthogonal_direction hv htwo
      let K : Submodule ℝ E := (ℝ ∙ u)ᗮ
      letI : BorelSpace K := Subtype.borelSpace _
      let vK : K := ⟨v, Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hvu⟩
      have hvK : ‖vK‖ = 1 := hv
      have hvK0 : vK ≠ 0 := by intro h; simp [h] at hvK
      letI : Nontrivial K := nontrivial_of_ne vK 0 hvK0
      have hu0 : u ≠ 0 := by intro h; simp [h] at hu
      have hline : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu0
      have hsum := (ℝ ∙ u).finrank_add_finrank_orthogonal
      have hdimK : Module.finrank ℝ K < n := by dsimp only [K]; omega
      let V : K → ℝ := fun t => -Real.log (∫ x : ℝ, Real.exp (-U ((t : E) + x • u)))
      have hV : C2StrongQuadraticPotential V ρ ∧
          (gaussianPotentialLaw U).map K.orthogonalProjectionOnto = gaussianPotentialLaw V :=
        c2StrongQuadraticPotential_actual_complement_marginal hU hρ hu
      obtain ⟨W, hW, hLaw⟩ := ih (Module.finrank ℝ K) hdimK rfl hV.1 hρ hvK
      refine ⟨W, hW, ?_⟩
      have hinner : (fun t : K => ⟪vK, t⟫_ℝ) ∘ K.orthogonalProjectionOnto =
          fun z : E => ⟪v, z⟫_ℝ := by
        funext z
        exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K := K) vK z
      rw [← hinner, ← Measure.map_map (by fun_prop) K.orthogonalProjectionOnto.measurable,
        hV.2]
      exact hLaw

theorem c2StrongQuadraticPotential_unit_marginal_exists
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {U : E → ℝ} {ρ : ℝ} (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ)
    {v : E} (hv : ‖v‖ = 1) :
    ∃ W : ℝ → ℝ, C2StrongQuadraticPotential W ρ ∧
      (gaussianPotentialLaw U).map (fun z : E => ⟪v, z⟫_ℝ) =
        realDensityLaw (fun x => Real.exp (-W x)) :=
  c2_gaussian_unit_marginal_by_dimension (Module.finrank ℝ E) rfl hU hρ hv

end
end Nonsmooth
