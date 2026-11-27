import Nonsmooth.SoftSliceProperties

open Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {ι : Type}

def quadraticSliceConstraints (A B C D E F : ι → ℝ) : SmoothSliceConstraints ι where
  value i t x := A i * t ^ 2 + 2 * B i * t * x + C i * x ^ 2 + D i * t + E i * x + F i
  dx i t x := 2 * B i * t + 2 * C i * x + E i
  dt i t x := 2 * A i * t + 2 * B i * x + D i
  dxx i _ _ := 2 * C i
  dtx i _ _ := 2 * B i
  dtt i _ _ := 2 * A i
  value_cont i := by fun_prop
  dx_cont i := by fun_prop
  dt_cont i := by fun_prop
  dxx_cont i := continuous_const
  dtx_cont i := continuous_const
  dtt_cont i := continuous_const
  value_dx i t x := by
    have h1 := hasDerivAt_const x (A i * t ^ 2)
    have h2 := (hasDerivAt_id x).const_mul (2 * B i * t)
    have h3 := ((hasDerivAt_id x).pow 2).const_mul (C i)
    have h4 := hasDerivAt_const x (D i * t)
    have h5 := (hasDerivAt_id x).const_mul (E i)
    convert! (((h1.add h2).add h3).add h4).add h5 |>.add_const (F i) using 1 <;>
      norm_num [id_eq, Pi.mul_apply, Pi.pow_apply] <;> ring
  value_dt i t x := by
    have h1 := ((hasDerivAt_id t).pow 2).const_mul (A i)
    have h2 := ((hasDerivAt_id t).const_mul (2 * B i)).mul_const x
    have h3 := hasDerivAt_const t (C i * x ^ 2)
    have h4 := (hasDerivAt_id t).const_mul (D i)
    have h5 := hasDerivAt_const t (E i * x)
    convert! (((h1.add h2).add h3).add h4).add h5 |>.add_const (F i) using 1 <;>
      norm_num [id_eq, Pi.mul_apply, Pi.pow_apply] <;> ring
  dx_dx i t x := by
    convert! (((hasDerivAt_id x).const_mul (2 * C i)).const_add (2 * B i * t)).add_const (E i)
      using 1 <;> norm_num [id_eq, Pi.mul_apply, Pi.pow_apply] <;> ring
  dx_dt i t x := by
    convert! (((hasDerivAt_id t).const_mul (2 * B i)).add_const (2 * C i * x)).add_const (E i)
      using 1 <;> norm_num [id_eq, Pi.mul_apply, Pi.pow_apply] <;> ring
  dt_dx i t x := by
    convert! (((hasDerivAt_id x).const_mul (2 * B i)).const_add (2 * A i * t)).add_const (D i)
      using 1 <;> norm_num [id_eq, Pi.mul_apply, Pi.pow_apply] <;> ring
  dt_dt i t x := by
    convert! (((hasDerivAt_id t).const_mul (2 * A i)).add_const (2 * B i * x)).add_const (D i)
      using 1 <;> norm_num [id_eq, Pi.mul_apply, Pi.pow_apply] <;> ring

theorem quadraticSliceConstraints_hessian (A B C D E F : ι → ℝ)
    (h : ∀ i p q, 0 ≤ C i * p ^ 2 + 2 * B i * p * q + A i * q ^ 2)
    (i : ι) (t x p q : ℝ) :
    0 ≤ (quadraticSliceConstraints A B C D E F).dxx i t x * p ^ 2 +
      2 * (quadraticSliceConstraints A B C D E F).dtx i t x * p * q +
      (quadraticSliceConstraints A B C D E F).dtt i t x * q ^ 2 := by
  dsimp only [quadraticSliceConstraints]
  nlinarith [h i p q]

end
end Nonsmooth
