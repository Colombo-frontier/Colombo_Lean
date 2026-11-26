import RationalLocalKL254
import GaussianTilt254

noncomputable section
open scoped BigOperators Matrix.Norms.Operator
open Matrix
namespace Paper254

theorem covariance_entry_bound {d : ℕ} (C : Precision d) (hC : C.PosDef)
    (lo hi : ℝ) (hhi : 0≤hi)
    (hL : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic C x)
    (hU : ∀ x : Space d,matrixQuadratic C x≤hi*‖x‖^2) :
    ∀ i j,|C i j|≤(d:ℝ)^2*hi := by
  have he := eigenvalues_from_quadratic_bounds C hC lo hi hL hU
  have hb := rotatedPrecision_norm_bound (star hC.isHermitian.eigenvectorUnitary)
    hC.isHermitian.eigenvalues hi hhi
    (fun j=>by rw [abs_of_pos (hC.eigenvalues_pos j)]; exact (he j).2)
  rw [←precision_spectral_rotated hC] at hb
  exact fun i j=>(matrix_entry_le_operator_norm C i j).trans hb

theorem tilted_coefficient_bound (lam z v : ℝ) (hlam : 0≤lam) (hv : 0≤v)
    (hz : |2*lam*z|≤1/4) :
    |lam*(1+2*lam*z)/(1+lam*(2*lam)*v)|≤(5/4)*lam := by
  have hden : 1≤1+lam*(2*lam)*v := by
    have hh : 0≤lam*(2*lam)*v := by positivity
    linarith
  rw [abs_div,abs_mul,abs_of_nonneg hlam,abs_of_pos (by linarith : 0<1+lam*(2*lam)*v)]
  have hn : |1+2*lam*z|≤5/4 := by
    have hh := abs_add_le (1:ℝ) (2*lam*z)
    rw [abs_one] at hh
    linarith
  have hm := mul_le_mul_of_nonneg_left hn hlam
  exact (div_le_self (mul_nonneg hlam (abs_nonneg _)) hden).trans (by linarith [hm])

theorem rationalTiltMean_uniform_radius {d : ℕ} {D : ℝ} (W : Domain d D)
    (lo hi G : ℝ) (hhi : 0≤hi) (hG : 0≤G) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) (hg : ∀ i,|(g i:ℝ)|≤G)
    (hsmall : |2*(lam:ℝ)*((fun j=>(g j:ℝ)) ⬝ᵥ
      ((fun j=>(S.mean j:ℝ))-(fun j=>(w j:ℝ))))|≤1/4) (p : ℕ) :
    ∀ v : W.carrier,∀ i,|v.val i-(rationalTiltMean S lam g w i:ℝ)|+((2:ℝ)^p)⁻¹≤
      D+(5/4)*(lam:ℝ)*(d:ℝ)^3*hi*G+1 := by
  let C := realMatrix S.covariance
  let P := S.gaussian hS.covariance_pos
  let gr : Coordinates d := fun j=>(g j:ℝ)
  let wr : Coordinates d := fun j=>(w j:ℝ)
  have hiC : P.precision⁻¹=C := Matrix.nonsing_inv_nonsing_inv _
    (isUnit_iff_ne_zero.mpr hS.covariance_pos.det_pos.ne')
  have hc := covariance_entry_bound C hS.covariance_pos lo hi hhi hS.covariance_lower hS.covariance_upper
  have hmul : ∀ i,|(C *ᵥ gr) i|≤(d:ℝ)^3*hi*G := by
    intro i
    calc
      _ ≤ ∑ j,|C i j*gr j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d,(d:ℝ)^2*hi*G := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hc i j) (hg j) (abs_nonneg _) (by positivity)
      _ = _ := by simp; ring
  have hcoef := tilted_coefficient_bound (lam:ℝ) (gr ⬝ᵥ (P.mean-wr))
    (matrixQuadratic P.precision⁻¹ gr) hlam (matrixQuadratic_nonneg P.positive.inv gr) hsmall
  have he := P.tilt_mean (lam:ℝ) (2*(lam:ℝ)) hlam (by positivity) gr wr
  rw [hiC] at he hcoef
  intro v i
  have hmean := congrFun (rationalTiltGaussian_mean S hS.covariance_pos lam hlam g w).symm i
  rw [congrFun he i] at hmean
  have hbase : |v.val i-(S.mean i:ℝ)|≤D :=
    (PiLp.norm_apply_le (v.val-WithLp.toLp 2 (fun j=>(S.mean j:ℝ))) i).trans
      (W.diameter v.val v.property _ hS.feasible)
  have hdelta : |(S.mean i:ℝ)-(rationalTiltMean S lam g w i:ℝ)|≤
      (5/4)*(lam:ℝ)*(d:ℝ)^3*hi*G := by
    rw [hmean]
    change |(S.mean i:ℝ)-((S.mean i:ℝ)-_*_)|≤_
    rw [sub_sub_cancel,abs_mul]
    have hh := mul_le_mul hcoef (hmul i) (abs_nonneg _) (by positivity : 0≤(5/4)*(lam:ℝ))
    nlinarith
  have ht := abs_sub_le (v.val i) (S.mean i:ℝ) (rationalTiltMean S lam g w i:ℝ)
  have hp := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n := p))
  linarith

end Paper254
#print axioms Paper254.rationalTiltMean_uniform_radius
