import Nonsmooth.SoftSliceDerivatives
import Nonsmooth.SoftHessianAlgebra

open Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {ι : Type} [Fintype ι]

theorem softSlice_data_continuous (ρ : ℝ) (D : SmoothSliceConstraints ι) :
    Continuous (Function.uncurry (softSlicePotential ρ D)) ∧
    Continuous (Function.uncurry (softSliceDx ρ D)) ∧
    Continuous (Function.uncurry (softSliceScore ρ D)) ∧
    Continuous (Function.uncurry (softSliceDxx ρ D)) ∧
    Continuous (Function.uncurry (softSliceMixed D)) ∧
    Continuous (Function.uncurry (softSliceGamma ρ D)) := by
  have hv (i : ι) : Continuous (fun p : ℝ × ℝ => D.value i p.1 p.2) := D.value_cont i
  have hx (i : ι) : Continuous (fun p : ℝ × ℝ => D.dx i p.1 p.2) := D.dx_cont i
  have ht (i : ι) : Continuous (fun p : ℝ × ℝ => D.dt i p.1 p.2) := D.dt_cont i
  have hxx (i : ι) : Continuous (fun p : ℝ × ℝ => D.dxx i p.1 p.2) := D.dxx_cont i
  have htx (i : ι) : Continuous (fun p : ℝ × ℝ => D.dtx i p.1 p.2) := D.dtx_cont i
  have htt (i : ι) : Continuous (fun p : ℝ × ℝ => D.dtt i p.1 p.2) := D.dtt_cont i
  have hp := softplus_contDiff.continuous
  have hs := softplusSlope_contDiff.continuous
  have hc := softplusCurvature_contDiff.continuous
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_const.mul ((continuous_fst.pow 2).add (continuous_snd.pow 2))).add
      (continuous_finsetSum _ (fun i _ => hp.comp (hv i)))
  · exact (continuous_const.mul continuous_snd).add
      (continuous_finsetSum _ (fun i _ => (hs.comp (hv i)).mul (hx i)))
  · exact (continuous_const.mul continuous_fst).add
      (continuous_finsetSum _ (fun i _ => (hs.comp (hv i)).mul (ht i)))
  · exact continuous_const.add (continuous_finsetSum _ (fun i _ =>
      ((hc.comp (hv i)).mul ((hx i).pow 2)).add ((hs.comp (hv i)).mul (hxx i))))
  · exact continuous_finsetSum _ (fun i _ =>
      (((hc.comp (hv i)).mul (hx i)).mul (ht i)).add ((hs.comp (hv i)).mul (htx i)))
  · exact continuous_const.add (continuous_finsetSum _ (fun i _ =>
      ((hc.comp (hv i)).mul ((ht i).pow 2)).add ((hs.comp (hv i)).mul (htt i))))

theorem softSlicePotential_gaussian_lower {ρ : ℝ} (hρ : 0 ≤ ρ)
    (D : SmoothSliceConstraints ι) (t x : ℝ) : ρ / 2 * x ^ 2 ≤ softSlicePotential ρ D t x := by
  have hs : 0 ≤ ∑ i, softplus (D.value i t x) := Finset.sum_nonneg (fun i _ =>
    Real.log_nonneg (by linarith [Real.exp_pos (D.value i t x)]))
  have ht := mul_nonneg hρ (sq_nonneg t)
  dsimp only [softSlicePotential]
  nlinarith

theorem softSlice_hessian_bound {ρ : ℝ} (hρ : 1 < ρ) (D : SmoothSliceConstraints ι)
    (hD : ∀ i t x p q, 0 ≤ D.dxx i t x * p ^ 2 + 2 * D.dtx i t x * p * q + D.dtt i t x * q ^ 2)
    (t x : ℝ) :
    0 < softSliceDxx ρ D t x - 1 ∧
      (softSliceMixed D t x) ^ 2 ≤ (softSliceDxx ρ D t x - 1) * (softSliceGamma ρ D t x - 1) := by
  apply two_dimensional_hessian_from_quadratic_lower hρ
  intro p q
  exact softplus_finite_hessian_lower ρ (fun i => D.value i t x)
    (fun i => D.dx i t x) (fun i => D.dt i t x)
    (fun i => D.dxx i t x) (fun i => D.dtx i t x) (fun i => D.dtt i t x)
    (fun i => hD i t x) p q

end
end Nonsmooth
