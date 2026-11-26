import LowRank.GaussianRotation
import Mathlib.Probability.Independence.Basic

/-! Independence of fixed orthogonal components of a Gaussian vector.
The proof is adapted from the locally verified GaussianOrthogonalComponents
module, rebuilt here using only LowRank and Mathlib. This is a fixed-subspace
result; it does not license replacing a subspace by a data-dependent one. -/

namespace LowRank
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem orthogonal_components_energy (K : Submodule ℝ E) (z : E) :
    ‖(K.orthogonalProjection z : E)‖ ^ 2 +
      ‖z - (K.orthogonalProjection z : E)‖ ^ 2 = ‖z‖ ^ 2 := by
  have h := K.orthogonalProjectionFn_norm_sq z
  change ‖z‖ * ‖z‖ =
    ‖z - (K.orthogonalProjection z : E)‖ * ‖z - (K.orthogonalProjection z : E)‖ +
      ‖(K.orthogonalProjection z : E)‖ * ‖(K.orthogonalProjection z : E)‖ at h
  nlinarith

theorem gaussian_orthogonal_recombine (K : Submodule ℝ E) :
    ((euclideanGaussianLaw E).prod (euclideanGaussianLaw E)).map
      (fun zw : E × E => (K.orthogonalProjection zw.1 : E) +
        (zw.2 - (K.orthogonalProjection zw.2 : E))) = euclideanGaussianLaw E := by
  let P : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjection
  let R : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P
  have hP (z : E) : P z = (K.orthogonalProjection z : E) := rfl
  have hR (z : E) : R z = z - (K.orthogonalProjection z : E) := rfl
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
    have hi : ⟪P zw.1 + R zw.2, t⟫_ℝ = ⟪zw.1, P t⟫_ℝ + ⟪zw.2, R t⟫_ℝ := by
      simp only [hP, hR, inner_add_left, inner_sub_left, inner_sub_right,
        Submodule.inner_orthogonalProjection_left_eq_right]
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

theorem gaussian_orthogonal_independent (K : Submodule ℝ E) :
    IndepFun (fun z : E => (K.orthogonalProjection z : E))
      (fun z : E => z - (K.orthogonalProjection z : E)) (euclideanGaussianLaw E) := by
  let P : E →L[ℝ] E := K.subtypeL.comp K.orthogonalProjection
  let R : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P
  have hP (z : E) : P z = (K.orthogonalProjection z : E) := rfl
  have hR (z : E) : R z = z - (K.orthogonalProjection z : E) := rfl
  change IndepFun P R (euclideanGaussianLaw E)
  rw [indepFun_iff_map_prod_eq_prod_map_map P.measurable.aemeasurable R.measurable.aemeasurable]
  have hPP (z : E) : P (P z) = P z := by
    simp only [hP, Submodule.orthogonalProjection_mem_subspace_eq_self]
  have hPR (z : E) : P (R z) = 0 := by
    change P (z - P z) = 0
    rw [map_sub, hPP, sub_self]
  have hRP (z : E) : R (P z) = 0 := by
    change P z - P (P z) = 0
    rw [hPP, sub_self]
  have hRR (z : E) : R (R z) = R z := by
    change R z - P (R z) = R z
    rw [hPR, sub_zero]
  have hrec := gaussian_orthogonal_recombine K
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
      simp only [Function.comp_def, map_add, hPP, hPR, hRP, hRR, add_zero, zero_add,
        Prod.map_apply]
      rfl
    _ = _ := (Measure.map_prod_map _ _ P.measurable R.measurable).symm

end
end LowRank
