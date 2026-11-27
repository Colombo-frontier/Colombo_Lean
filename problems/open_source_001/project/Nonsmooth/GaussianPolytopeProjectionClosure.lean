import Nonsmooth.GaussianPolytopeWinnerModel
import Nonsmooth.DeterminedScalarPosterior
import Nonsmooth.ConstantObservationAE

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
local instance (M : GaussianPolytopeModel E) (K : Submodule ℝ M.Space) : BorelSpace K :=
  Subtype.borelSpace _

def gaussianPolytopeQueryVector (M : GaussianPolytopeModel E) (q : E) : M.Space :=
  M.embedding.toContinuousLinearMap.adjoint q

theorem gaussianPolytopeModelMap_inner (s : ℝ) (M : GaussianPolytopeModel E) (q : E) (z : M.Space) :
    ⟪gaussianPolytopeModelMap s M z, q⟫_ℝ =
      ⟪M.origin, q⟫_ℝ + s * ⟪z, gaussianPolytopeQueryVector M q⟫_ℝ := by
  unfold gaussianPolytopeModelMap
  rw [inner_add_left, real_inner_smul_left]
  congr 2
  exact (M.embedding.toContinuousLinearMap.adjoint_inner_right z q).symm

theorem gaussianPolytopeModel_projection_closed {s : ℝ} (hs : 0 < s)
    (M : GaussianPolytopeModel E) (q : E) :
    ∀ᵐ y ∂(gaussianPolytopeModelLaw s M).map (fun z : E => ⟪z, q⟫_ℝ),
      GaussianPolytopeRow s
        (condDistrib id (fun z : E => ⟪z, q⟫_ℝ) (gaussianPolytopeModelLaw s M) y) := by
  let v := gaussianPolytopeQueryVector M q
  let f := gaussianPolytopeModelMap s M
  let μ := (euclideanGaussianLaw M.Space)[|gaussianBallPolytope M.radius M.normal M.bound]
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure M.positive
  have hf : Measurable f := gaussianPolytopeModelMap_measurable s M
  have hX : Measurable (fun z : E => ⟪z, q⟫_ℝ) := by fun_prop
  by_cases hv : v = 0
  · have hconst : ∀ᵐ z ∂gaussianPolytopeModelLaw s M, ⟪z, q⟫_ℝ = ⟪M.origin, q⟫_ℝ := by
      apply (ae_map_iff hf.aemeasurable (measurableSet_eq_fun hX measurable_const)).mpr
      apply Eventually.of_forall
      intro z
      change ⟪gaussianPolytopeModelMap s M z, q⟫_ℝ = _
      rw [gaussianPolytopeModelMap_inner]
      change ⟪M.origin, q⟫_ℝ + s * ⟪z, v⟫_ℝ = _
      simp [hv]
    filter_upwards [ae_constant_observation_posterior (gaussianPolytopeModelLaw s M)
      _ hX ⟪M.origin, q⟫_ℝ hconst] with y hy
    rw [hy]
    exact Or.inr ⟨M, rfl⟩
  · let u := normalizedDirection v
    have hu : ‖u‖ = 1 := normalizedDirection_norm hv
    have hnv : ‖v‖ • u = v := by
      simp only [u, normalizedDirection, smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
    have hc : s * ‖v‖ ≠ 0 := (mul_pos hs (norm_pos_iff.mpr hv)).ne'
    have hXf (z : M.Space) : ⟪f z, q⟫_ℝ = ⟪M.origin, q⟫_ℝ + (s * ‖v‖) * ⟪z, u⟫_ℝ := by
      rw [gaussianPolytopeModelMap_inner]
      change ⟪M.origin, q⟫_ℝ + s * ⟪z, v⟫_ℝ = _
      have hi : ⟪z, v⟫_ℝ = ‖v‖ * ⟪z, u⟫_ℝ := by
        rw [← real_inner_smul_right, hnv]
      rw [hi]
      ring
    rcases subsingleton_or_nontrivial (ℝ ∙ u)ᗮ with hdim | hdim
    · letI := hdim
      have horth : (ℝ ∙ u)ᗮ = (⊥ : Submodule ℝ M.Space) := by
        apply (Submodule.eq_bot_iff _).mpr
        intro z hz
        exact congrArg (fun w : (ℝ ∙ u)ᗮ => (w : M.Space)) (Subsingleton.elim ⟨z, hz⟩ 0)
      have hspan : (ℝ ∙ u : Submodule ℝ M.Space) = ⊤ := Submodule.orthogonal_eq_bot_iff.mp horth
      have hr : Measurable (fun z : M.Space => ⟪z, u⟫_ℝ) := by fun_prop
      apply affine_observation_posterior_property μ f hf _ hr _ hX hc ⟪M.origin, q⟫_ℝ hXf
        (fun _ ν => GaussianPolytopeRow s ν)
      filter_upwards [spanning_unit_observation_posterior μ hu hspan] with t ht
      rw [ht, Measure.map_dirac' hf]
      exact Or.inl ⟨f (t • u), rfl⟩
    · letI := hdim
      exact gaussianPolytopeModel_normalized_projection_closed s M hu _ hX hc ⟪M.origin, q⟫_ℝ hXf

theorem gaussianPolytopeRow_projection_closed {s : ℝ} (hs : 0 < s)
    (ν : Measure E) [IsProbabilityMeasure ν] (hν : GaussianPolytopeRow s ν) (q : E) :
    ∀ᵐ y ∂ν.map (fun z : E => ⟪z, q⟫_ℝ),
      GaussianPolytopeRow s (condDistrib id (fun z : E => ⟪z, q⟫_ℝ) ν y) := by
  rcases hν with ⟨x, rfl⟩ | ⟨M, rfl⟩
  · have hm : Measurable (fun z : E => ⟪z, q⟫_ℝ) := by fun_prop
    filter_upwards [ae_constant_observation_posterior (Measure.dirac x) _ hm ⟪x, q⟫_ℝ
      (ae_eq_dirac (fun z => ⟪z, q⟫_ℝ))] with y hy
    rw [hy]
    exact Or.inl ⟨x, rfl⟩
  · exact gaussianPolytopeModel_projection_closed hs M q

end
end Nonsmooth
