import Nonsmooth.GaussianRealMoments

open MeasureTheory ProbabilityTheory Filter Function
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem standardGaussian_fourth_moment : (∫ z : ℝ, z ^ 4 ∂gaussianReal 0 1) = 3 := by
  let g : ℝ → ℝ := fun t => Real.exp (t ^ 2 / 2)
  have he0 : mgf id (gaussianReal 0 1) = g := funext standardGaussian_mgf
  have h0 (t : ℝ) : HasDerivAt g (g t * t) t := by
    have h := standardGaussian_mgf_hasDerivAt t
    rw [he0] at h
    exact h
  have h1 (t : ℝ) : HasDerivAt (fun u => g u * u) (g t * (1 + t ^ 2)) t := by
    convert (h0 t).mul (hasDerivAt_id t) using 1 <;> first | rfl | (simp only [id_eq, Pi.add_apply, Pi.pow_apply]; ring)
  have h2 (t : ℝ) : HasDerivAt (fun u => g u * (1 + u ^ 2)) (g t * (3 * t + t ^ 3)) t := by
    convert (h0 t).mul ((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)) using 1 <;> first | rfl | (simp only [id_eq, Pi.add_apply, Pi.pow_apply]; ring)
  have h3 (t : ℝ) : HasDerivAt (fun u => g u * (3 * u + u ^ 3))
      (g t * (3 + 6 * t ^ 2 + t ^ 4)) t := by
    convert (h0 t).mul (((hasDerivAt_id t).const_mul 3).add ((hasDerivAt_id t).pow 3)) using 1 <;> first | rfl | (simp only [id_eq, Pi.add_apply, Pi.pow_apply]; ring)
  have he1 : iteratedDeriv 1 (mgf id (gaussianReal 0 1)) = fun t => g t * t := by
    rw [iteratedDeriv_one, he0]
    exact funext (fun t => (h0 t).deriv)
  have he2 : iteratedDeriv 2 (mgf id (gaussianReal 0 1)) = fun t => g t * (1 + t ^ 2) := by
    rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, he1]
    exact funext (fun t => (h1 t).deriv)
  have he3 : iteratedDeriv 3 (mgf id (gaussianReal 0 1)) = fun t => g t * (3 * t + t ^ 3) := by
    rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ, he2]
    exact funext (fun t => (h2 t).deriv)
  have hint : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
    rw [standardGaussian_integrableExpSet, interior_univ]
    exact Set.mem_univ _
  have hm := hasDerivAt_iteratedDeriv_mgf hint 3
  rw [he3] at hm
  simpa [g] using hm.unique (h3 0)

end
end Nonsmooth
