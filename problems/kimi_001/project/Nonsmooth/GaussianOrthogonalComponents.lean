import Nonsmooth.GaussianRowCentering

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nonsmooth
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem orthogonal_components_energy (K : Submodule ℝ E) (z : E) :
    ‖(K.orthogonalProjectionOnto z : E)‖ ^ 2 +
      ‖z - (K.orthogonalProjectionOnto z : E)‖ ^ 2 = ‖z‖ ^ 2 := by
  simpa only [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply, Submodule.starProjection_apply] using
    (K.norm_sq_eq_add_norm_sq_starProjection z).symm

/-- Replacing the unobserved orthogonal component by an independent Gaussian
preserves the actual Gaussian law. -/
theorem euclideanGaussian_orthogonal_recombine (K : Submodule ℝ E) :
    ((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map
      (fun zw : E × E => (K.orthogonalProjectionOnto zw.1 : E) +
        (zw.2 - (K.orthogonalProjectionOnto zw.2 : E))) = euclideanGaussianLaw E := by
  let P : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjectionOnto
  let R : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P
  have hP (z : E) : P z = (K.orthogonalProjectionOnto z : E) := rfl
  have hR (z : E) : R z = z - (K.orthogonalProjectionOnto z : E) := rfl
  change ((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map
    (fun zw : E × E => P zw.1 + R zw.2) = _
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply]
  have hm : Measurable (fun zw : E × E => P zw.1 + R zw.2) := by fun_prop
  have hf : StronglyMeasurable (fun z : E => Complex.exp ((⟪z, t⟫_ℝ : ℂ) * Complex.I)) :=
    (by fun_prop : Continuous _).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable hm hf]
  have he (zw : E × E) :
      Complex.exp ((⟪P zw.1 + R zw.2, t⟫_ℝ : ℂ) * Complex.I) =
        Complex.exp ((⟪zw.1, P t⟫_ℝ : ℂ) * Complex.I) *
          Complex.exp ((⟪zw.2, R t⟫_ℝ : ℂ) * Complex.I) := by
    have hs (z : E) : ⟪(K.orthogonalProjectionOnto z : E), t⟫_ℝ =
        ⟪z, (K.orthogonalProjectionOnto t : E)⟫_ℝ := by
      exact K.inner_starProjection_left_eq_right z t
    have hi : ⟪P zw.1 + R zw.2, t⟫_ℝ = ⟪zw.1, P t⟫_ℝ + ⟪zw.2, R t⟫_ℝ := by
      simp only [hP, hR, inner_add_left, inner_sub_left, inner_sub_right, hs]
    rw [hi, Complex.ofReal_add, add_mul, Complex.exp_add]
  simp_rw [he]
  rw [integral_prod_mul
    (fun z : E => Complex.exp ((⟪z, P t⟫_ℝ : ℂ) * Complex.I))
    (fun z : E => Complex.exp ((⟪z, R t⟫_ℝ : ℂ) * Complex.I))]
  change charFun (euclideanGaussianLaw E) (P t) *
    charFun (euclideanGaussianLaw E) (R t) = _
  rw [euclideanGaussian_characteristic, euclideanGaussian_characteristic,
    euclideanGaussian_characteristic, ← Complex.exp_add]
  congr 1
  have henergy : ‖P t‖ ^ 2 + ‖R t‖ ^ 2 = ‖t‖ ^ 2 := orthogonal_components_energy K t
  have hcast : (‖P t‖ : ℂ) ^ 2 + (‖R t‖ : ℂ) ^ 2 = (‖t‖ : ℂ) ^ 2 := by
    exact_mod_cast henergy
  linear_combination (-1 / 2 : ℂ) * hcast

/-- The observed projection and the remaining component of an isotropic Gaussian
are independent, including the zero and full subspaces. -/
theorem euclideanGaussian_orthogonal_independent (K : Submodule ℝ E) :
    IndepFun (fun z : E => (K.orthogonalProjectionOnto z : E))
      (fun z : E => z - (K.orthogonalProjectionOnto z : E)) (euclideanGaussianLaw E) := by
  let P : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjectionOnto
  let R : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P
  have hP (z : E) : P z = (K.orthogonalProjectionOnto z : E) := rfl
  have hR (z : E) : R z = z - (K.orthogonalProjectionOnto z : E) := rfl
  change IndepFun P R (euclideanGaussianLaw E)
  rw [indepFun_iff_map_prod_eq_prod_map_map P.measurable.aemeasurable R.measurable.aemeasurable]
  have hPP (z : E) : P (P z) = P z := by
    simp only [hP, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hPR (z : E) : P (R z) = 0 := by
    change P (z - P z) = 0
    rw [map_sub, hPP, sub_self]
  have hRP (z : E) : R (P z) = 0 := by
    change P z - P (P z) = 0
    rw [hPP, sub_self]
  have hRR (z : E) : R (R z) = R z := by
    change R z - P (R z) = R z
    rw [hPR, sub_zero]
  have hrec := euclideanGaussian_orthogonal_recombine K
  change ((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map
    (fun zw : E × E => P zw.1 + R zw.2) = _ at hrec
  have hm : Measurable (fun zw : E × E => P zw.1 + R zw.2) := by fun_prop
  calc
    _ = (((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map
        (fun zw : E × E => P zw.1 + R zw.2)).map (fun z : E => (P z, R z)) := by rw [hrec]
    _ = ((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map
        (Prod.map P R) := by
      rw [Measure.map_map (P.measurable.prodMk R.measurable) hm]
      congr 1
      funext zw
      simp only [Function.comp_def, map_add, hPP, hPR, hRP, hRR, add_zero, zero_add]
      rfl
    _ = _ := (Measure.map_prod_map _ _ P.measurable R.measurable).symm

end
end Nonsmooth
