import Nonsmooth.SoftplusDerivatives

open Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

structure SmoothSliceConstraints (ι : Type) where
  value : ι → ℝ → ℝ → ℝ
  dx : ι → ℝ → ℝ → ℝ
  dt : ι → ℝ → ℝ → ℝ
  dxx : ι → ℝ → ℝ → ℝ
  dtx : ι → ℝ → ℝ → ℝ
  dtt : ι → ℝ → ℝ → ℝ
  value_cont : ∀ i, Continuous (Function.uncurry (value i))
  dx_cont : ∀ i, Continuous (Function.uncurry (dx i))
  dt_cont : ∀ i, Continuous (Function.uncurry (dt i))
  dxx_cont : ∀ i, Continuous (Function.uncurry (dxx i))
  dtx_cont : ∀ i, Continuous (Function.uncurry (dtx i))
  dtt_cont : ∀ i, Continuous (Function.uncurry (dtt i))
  value_dx : ∀ i t x, HasDerivAt (value i t) (dx i t x) x
  value_dt : ∀ i t x, HasDerivAt (fun r => value i r x) (dt i t x) t
  dx_dx : ∀ i t x, HasDerivAt (dx i t) (dxx i t x) x
  dx_dt : ∀ i t x, HasDerivAt (fun r => dx i r x) (dtx i t x) t
  dt_dx : ∀ i t x, HasDerivAt (dt i t) (dtx i t x) x
  dt_dt : ∀ i t x, HasDerivAt (fun r => dt i r x) (dtt i t x) t

variable {ι : Type} [Fintype ι]

def softSlicePotential (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) : ℝ :=
  ρ / 2 * (t ^ 2 + x ^ 2) + ∑ i, softplus (D.value i t x)

def softSliceDx (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) : ℝ :=
  ρ * x + ∑ i, softplusSlope (D.value i t x) * D.dx i t x

def softSliceScore (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) : ℝ :=
  ρ * t + ∑ i, softplusSlope (D.value i t x) * D.dt i t x

def softSliceDxx (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) : ℝ :=
  ρ + ∑ i, (softplusCurvature (D.value i t x) * (D.dx i t x) ^ 2 +
    softplusSlope (D.value i t x) * D.dxx i t x)

def softSliceMixed (D : SmoothSliceConstraints ι) (t x : ℝ) : ℝ :=
  ∑ i, (softplusCurvature (D.value i t x) * D.dx i t x * D.dt i t x +
    softplusSlope (D.value i t x) * D.dtx i t x)

def softSliceGamma (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) : ℝ :=
  ρ + ∑ i, (softplusCurvature (D.value i t x) * (D.dt i t x) ^ 2 +
    softplusSlope (D.value i t x) * D.dtt i t x)

theorem softSlicePotential_hasDerivAt_x (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) :
    HasDerivAt (softSlicePotential ρ D t) (softSliceDx ρ D t x) x := by
  have hq : HasDerivAt (fun y : ℝ => ρ / 2 * (t ^ 2 + y ^ 2)) (ρ * x) x := by
    convert! (((hasDerivAt_id x).pow 2).const_add (t ^ 2)).const_mul (ρ / 2) using 1 <;> norm_num [id_eq] <;> ring
  have h := hq.fun_add (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (softplus_hasDerivAt (D.value i t x)).comp x (D.value_dx i t x)))
  convert! h using 1 <;> simp only [softSlicePotential, softSliceDx, softplusSlope, Function.comp_def]

theorem softSlicePotential_hasDerivAt_t (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) :
    HasDerivAt (fun r => softSlicePotential ρ D r x) (softSliceScore ρ D t x) t := by
  have hq : HasDerivAt (fun r : ℝ => ρ / 2 * (r ^ 2 + x ^ 2)) (ρ * t) t := by
    convert! (((hasDerivAt_id t).pow 2).add_const (x ^ 2)).const_mul (ρ / 2) using 1 <;> norm_num [id_eq] <;> ring
  simpa only [softSlicePotential, softSliceScore, softplusSlope, Function.comp_def] using
    hq.fun_add (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (softplus_hasDerivAt (D.value i t x)).comp t (D.value_dt i t x)))

theorem softSliceDx_hasDerivAt_x (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) :
    HasDerivAt (softSliceDx ρ D t) (softSliceDxx ρ D t x) x := by
  have hi (i : ι) : HasDerivAt (fun y => softplusSlope (D.value i t y) * D.dx i t y)
      (softplusCurvature (D.value i t x) * (D.dx i t x) ^ 2 +
        softplusSlope (D.value i t x) * D.dxx i t x) x := by
    convert! ((softplusSlope_hasDerivAt (D.value i t x)).comp x (D.value_dx i t x)).mul
      (D.dx_dx i t x) using 1 <;> (try simp only [Function.comp_def, Pi.mul_apply]) <;> ring
  have h := ((hasDerivAt_id x).const_mul ρ).fun_add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i))
  convert! h using 1 <;> simp only [softSliceDx, softSliceDxx, id_eq, mul_one]

theorem softSliceScore_hasDerivAt_x (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) :
    HasDerivAt (softSliceScore ρ D t) (softSliceMixed D t x) x := by
  have hi (i : ι) : HasDerivAt (fun y => softplusSlope (D.value i t y) * D.dt i t y)
      (softplusCurvature (D.value i t x) * D.dx i t x * D.dt i t x +
        softplusSlope (D.value i t x) * D.dtx i t x) x := by
    exact ((softplusSlope_hasDerivAt (D.value i t x)).comp x (D.value_dx i t x)).mul (D.dt_dx i t x)
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)).const_add (ρ * t)

theorem softSliceScore_hasDerivAt_t (ρ : ℝ) (D : SmoothSliceConstraints ι) (t x : ℝ) :
    HasDerivAt (fun r => softSliceScore ρ D r x) (softSliceGamma ρ D t x) t := by
  have hi (i : ι) : HasDerivAt (fun r => softplusSlope (D.value i r x) * D.dt i r x)
      (softplusCurvature (D.value i t x) * (D.dt i t x) ^ 2 +
        softplusSlope (D.value i t x) * D.dtt i t x) t := by
    convert! ((softplusSlope_hasDerivAt (D.value i t x)).comp t (D.value_dt i t x)).mul
      (D.dt_dt i t x) using 1 <;> (try simp only [Function.comp_def, Pi.mul_apply]) <;> ring
  simpa only [softSliceScore, softSliceGamma, id_eq, mul_one] using
    ((hasDerivAt_id t).const_mul ρ).fun_add (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i))

end
end Nonsmooth
