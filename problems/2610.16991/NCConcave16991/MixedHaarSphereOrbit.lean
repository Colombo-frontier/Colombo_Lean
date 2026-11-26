import NCConcave16991.MixedHaarHouseholder
import NCConcave16991.ConditionalHaarSymmetry
import Mathlib.MeasureTheory.Measure.Prod

/-! # Uniqueness of the actual rotation-invariant probability on a unit sphere

The proof averages the given probability against the actual normalized Haar
law, then uses an explicit orthogonal Householder map between unit vectors.
-/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000

attribute [local irreducible] householder orthogonalOfIsometry householderOrthogonal

variable {k : ℕ}

abbrev SphereSpace (k : ℕ) := EuclideanSpace ℝ (Fin k)

theorem sphereAction_joint_continuous :
    Continuous (fun p : Haar.OrthogonalGroup k × SphereSpace k ↦
      Haar.orthogonalLinearIsometryEquiv p.1 p.2) := by
  simp_rw [Haar.orthogonalLinearIsometryEquiv_apply]
  have hm : Continuous (fun p : Haar.OrthogonalGroup k × SphereSpace k ↦ (p.1.val,p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def] using
    (Matrix.continuous_uncurry_toEuclideanCLM (n := Fin k) (𝕜 := ℝ)).comp hm

theorem sphereAction_joint_measurable :
    Measurable (fun p : Haar.OrthogonalGroup k × SphereSpace k ↦
      Haar.orthogonalLinearIsometryEquiv p.1 p.2) := sphereAction_joint_continuous.measurable

def sphereOrbitLaw (e : SphereSpace k) : Measure (SphereSpace k) :=
  (Haar.haarLaw k).map (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e)

instance sphereOrbitLaw_probability (e : SphereSpace k) : IsProbabilityMeasure (sphereOrbitLaw e) := by
  unfold sphereOrbitLaw
  infer_instance

theorem sphereOrbitLaw_eq_of_norm_eq (e x : SphereSpace k) (hx : ‖e‖ = ‖x‖) :
    sphereOrbitLaw x = sphereOrbitLaw e := by
  let R := householderOrthogonal (e - x)
  have hR : Haar.orthogonalLinearIsometryEquiv R e = x := by
    dsimp only [R]
    rw [householderOrthogonal,orthogonalOfIsometry_action]
    exact householder_swap e x hx
  have hm := (Haar.continuous_orthogonalLinearIsometryEquiv_apply e).measurable
  have he : (fun Q : Haar.OrthogonalGroup k ↦ Haar.orthogonalLinearIsometryEquiv Q x) =
      (fun Q ↦ Haar.orthogonalLinearIsometryEquiv (Q * R) e) := by
    funext Q
    rw [Haar.action_mul,hR]
  unfold sphereOrbitLaw
  rw [he]
  calc
    _ = ((Haar.haarLaw k).map (fun Q ↦ Q * R)).map
        (fun Q ↦ Haar.orthogonalLinearIsometryEquiv Q e) := by
      simpa only [Function.comp_def] using
        (Measure.map_map (μ := Haar.haarLaw k) hm (measurable_mul_const R)).symm
    _ = _ := by rw [(measurePreserving_mul_right (Haar.haarLaw k) R).map_eq]


end NCConcave16991.MixedHaar

