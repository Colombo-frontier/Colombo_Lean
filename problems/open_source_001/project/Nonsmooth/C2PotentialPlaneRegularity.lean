import Nonsmooth.PlaneSliceBounds
import Nonsmooth.PrimitiveStrongSliceFamily

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every orthonormal plane restriction of a potential in the explicit
analytic class has the regular strong-slice structure needed for the
two-dimensional no-spike theorem. -/
theorem c2StrongQuadraticPotential_plane_regular {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : inner ℝ u v = (0 : ℝ)) :
    ∃ H : RegularStrongSliceFamily (fun t x => U (planePoint u v t x)),
      RegularSliceMomentContinuity (fun t x => U (planePoint u v t x)) H := by
  obtain ⟨a, B, ha, hB, hVB⟩ := hU.envelope
  obtain ⟨D, hD, hAB⟩ := hU.hessian_growth
  have hd := contDiff_two_derivative_data U hU.smooth
  let S := fderiv ℝ U
  let A := fderiv ℝ (fderiv ℝ U)
  let M := planeSliceData U S A hU.smooth.continuous hd.2.2.1 hd.2.2.2 hd.1 hd.2.1 hU.hessian_symmetric u v
  have hblock (t x p q : ℝ) : ρ * (p ^ 2 + q ^ 2) ≤
      M.dxx () t x * p ^ 2 + 2 * M.dtx () t x * p * q + M.dtt () t x * q ^ 2 := by
    let z := planePoint u v t x
    have hb := hU.hessian_lower z (planePoint u v q p)
    rw [planePoint_norm_sq u v hu hv ho q p] at hb
    change ρ * (q ^ 2 + p ^ 2) ≤ A z (q • v + p • u) (q • v + p • u) at hb
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hU.hessian_symmetric z v u] at hb
    have hsym : A z v u = A z u v := hU.hessian_symmetric z v u
    rw [hsym] at hb
    change ρ * (p ^ 2 + q ^ 2) ≤ A z u u * p ^ 2 + 2 * A z u v * p * q + A z v v * q ^ 2
    nlinarith
  have hVb (t x : ℝ) : a * x ^ 2 - B ≤ M.value () t x := by
    have hb := (hVB (planePoint u v t x)).1
    rw [planePoint_norm_sq u v hu hv ho t x] at hb
    change _ ≤ U (planePoint u v t x)
    nlinarith [mul_nonneg ha.le (sq_nonneg t)]
  have hs (t x : ℝ) : |M.dt () t x| ≤ (6 * B) * (1 + |t| + |x|) := by
    have he := (S (planePoint u v t x)).le_opNorm v
    rw [Real.norm_eq_abs, hv, mul_one] at he
    have hb := c2StrongQuadraticPotential_gradient_bound hU (by linarith) ha.le hB.le hVB
      (planePoint u v t x)
    have hn := mul_le_mul_of_nonneg_left (planePoint_norm_le u v hu hv t x)
      (show 0 ≤ 6 * B by positivity)
    change |S (planePoint u v t x) v| ≤ _
    nlinarith
  have hg (t x : ℝ) : |M.dtt () t x| ≤ D * (1 + t ^ 2 + x ^ 2) := by
    have he := bilinear_apply_unit_abs_bound (A (planePoint u v t x)) v v hv hv
    have hb := hAB (planePoint u v t x)
    rw [planePoint_norm_sq u v hu hv ho t x] at hb
    change |A (planePoint u v t x) v v| ≤ _
    exact he.trans (by simpa only [add_assoc] using hb)
  have hgrowth : smoothSliceDataPolynomialGrowth M () :=
    scalar_slice_local_polynomial_growth (M.dt ()) (M.dtt ()) (by positivity) hD hs hg
  exact smoothSliceData_regular_exists M () hρ ha hblock hVb hgrowth

theorem c2StrongQuadraticPotential_plane_regular_both {U : E → ℝ} {ρ : ℝ}
    (hU : C2StrongQuadraticPotential U ρ) (hρ : 1 < ρ)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ho : inner ℝ u v = (0 : ℝ)) :
    (∃ H : RegularStrongSliceFamily (fun t x => U (planePoint u v t x)),
      RegularSliceMomentContinuity (fun t x => U (planePoint u v t x)) H) ∧
    (∃ H : RegularStrongSliceFamily (fun t x => U (planePoint u v x t)),
      RegularSliceMomentContinuity (fun t x => U (planePoint u v x t)) H) := by
  refine ⟨c2StrongQuadraticPotential_plane_regular hU hρ u v hu hv ho, ?_⟩
  have hr := c2StrongQuadraticPotential_plane_regular hU hρ v u hv hu (by rw [real_inner_comm]; exact ho)
  have he : (fun t x => U (planePoint v u t x)) = (fun t x => U (planePoint u v x t)) := by
    funext t x
    simp only [planePoint, add_comm]
  rw [he] at hr
  exact hr

end
end Nonsmooth
