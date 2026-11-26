import GradientHessian.IntegralProfiles
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The literal radial squash from `lem:squash`, over arbitrary real inner
product spaces. The definitions retain the actual integrated septic profile. -/

noncomputable section
open Set Filter
open scoped Topology InnerProductSpace

namespace GradientHessian.RadialSquash
open IntegralProfiles

def scale (K r : ℝ) : ℝ := K * primitive 1 (r/K) / r

theorem scale_identity {K r : ℝ} (hK : 0 < K) (hr : 0 < r) (hrK : r ≤ K) :
    scale K r = 1 := by
  rw [scale, primitive_identity (by norm_num) ((div_le_one hK).mpr hrK)]
  field_simp

theorem scale_bounds {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    0 < scale K r ∧ scale K r ≤ 1 := by
  have ht : 0 < r/K := div_pos hr hK
  have hq : 0 < primitive 1 (r/K) := by
    by_cases ht₁ : r/K ≤ 1
    · rw [primitive_identity (by norm_num) ht₁]; exact ht
    · have hmono := primitive_monotone 1 (le_of_not_ge ht₁)
      rw [primitive_identity (by norm_num : (0:ℝ) ≤ 1) le_rfl] at hmono
      linarith
  constructor
  · exact div_pos (mul_pos hK hq) hr
  · have h := mul_le_mul_of_nonneg_left (primitive_le_self (a := 1) ht.le) hK.le
    have heq : K*(r/K) = r := by field_simp
    rw [heq] at h
    exact (div_le_one hr).mpr h

theorem scale_derivative {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    HasDerivAt (scale K)
      ((density 1 (r/K)*r - K*primitive 1 (r/K))/r^2) r := by
  convert ((((primitive_derivative 1 (r/K)).comp r
    ((hasDerivAt_id r).div_const K)).const_mul K).div (hasDerivAt_id r) hr.ne') using 1
  dsimp [scale]
  field_simp

theorem density_le_scale {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    density 1 (r/K) ≤ scale K r := by
  have h := mul_le_mul_of_nonneg_left (density_mul_le_primitive (a := 1)
    (show 0 ≤ r/K by positivity)) hK.le
  have heq : K*(density 1 (r/K)*(r/K)) = density 1 (r/K)*r := by field_simp
  rw [heq] at h
  exact (le_div_iff₀ hr).mpr h

theorem scale_derivative_nonpos {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    deriv (scale K) r ≤ 0 := by
  rw [(scale_derivative hK hr).deriv]
  have h := (le_div_iff₀ hr).mp (density_le_scale hK hr)
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (sq_nonneg r)

theorem scale_radial_lower {K r : ℝ} (hK : 0 < K) (hrK : K ≤ r) :
    K ≤ r*scale K r := by
  have hr : 0 < r := hK.trans_le hrK
  have ht : 1 ≤ r/K := (le_div_iff₀ hK).mpr (by simpa using hrK)
  have h := primitive_monotone 1 ht
  rw [primitive_identity (by norm_num : (0:ℝ) ≤ 1) le_rfl] at h
  have hmul := mul_le_mul_of_nonneg_left h hK.le
  have heq : r*scale K r = K*primitive 1 (r/K) := by unfold scale; field_simp
  rw [heq]
  simpa using hmul

def scale₁ (K r : ℝ) : ℝ := (density 1 (r/K)-scale K r)/r
def scale₂ (K r : ℝ) : ℝ := -Profiles.step₁ (r/K-1)/(K*r)-2*(scale₁ K r/r)
def scale₃ (K r : ℝ) : ℝ := -Profiles.step₂ (r/K-1)/(K^2*r) +
  3*Profiles.step₁ (r/K-1)/(K*r^2)+6*scale₁ K r/r^2

theorem scale_derivative' {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    HasDerivAt (scale K) (scale₁ K r) r := by
  convert scale_derivative hK hr using 1
  unfold scale₁ scale
  field_simp
  simp [pow_two]

theorem radial_density_derivative {K r : ℝ} :
    HasDerivAt (fun r => density 1 (r/K)) (-Profiles.step₁ (r/K-1)/K) r := by
  have h := ((Profiles.step_derivative (r/K-1)).comp r
    (((hasDerivAt_id r).div_const K).sub_const 1)).const_sub 1
  convert h using 1
  simp [density]
  ring

theorem scale₁_derivative {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    HasDerivAt (scale₁ K) (scale₂ K r) r := by
  have h := ((radial_density_derivative (K := K) (r := r)).sub (scale_derivative' hK hr)).div
    (hasDerivAt_id r) hr.ne'
  convert h using 1
  unfold scale₂ scale₁
  field_simp
  ring

theorem scale₂_derivative {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    HasDerivAt (scale₂ K) (scale₃ K r) r := by
  have hp := (Profiles.step₁_derivative (r/K-1)).comp r
    (((hasDerivAt_id r).div_const K).sub_const 1)
  have h := (hp.neg.div ((hasDerivAt_id r).const_mul K) (mul_ne_zero hK.ne' hr.ne')).sub
    (((scale₁_derivative hK hr).div (hasDerivAt_id r) hr.ne').const_mul 2)
  convert h using 1
  unfold scale₃ scale₂
  field_simp
  ring

theorem scale_second_derivative {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    HasDerivAt (deriv (scale K)) (scale₂ K r) r := by
  apply (scale₁_derivative hK hr).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with t ht
  exact (scale_derivative' hK ht).deriv

theorem scale_third_derivative {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    HasDerivAt (deriv (deriv (scale K))) (scale₃ K r) r := by
  apply (scale₂_derivative hK hr).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with t ht
  exact (scale_second_derivative hK ht).deriv

theorem scale₁_abs_bound {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    |scale₁ K r| ≤ 1/r := by
  rw [scale₁, abs_div, abs_of_pos hr, abs_of_nonpos (sub_nonpos.mpr (density_le_scale hK hr))]
  apply div_le_div_of_nonneg_right _ hr.le
  linarith [(scale_bounds hK hr).2, (density_bounds 1 (r/K)).1]

theorem step₁_abs_bound (t : ℝ) : |Profiles.step₁ t| ≤ 3 := by
  have h := Profiles.derivative_bounds t
  rw [Profiles.deriv_step] at h
  rw [abs_of_nonneg h.1]
  linarith [h.2]

theorem exists_step₂_abs_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, |Profiles.step₂ t| ≤ C := by
  have hc : Continuous Profiles.step₂ :=
    continuous_iff_continuousAt.mpr (fun t => (Profiles.step₂_derivative t).continuousAt)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max 1 C, le_max_left _ _, fun t => ?_⟩
  by_cases h₀ : t ≤ 0
  · simp [Profiles.step₂, h₀]
  by_cases h₁ : t ≤ 1
  · exact (hC t ⟨le_of_lt (not_le.mp h₀), h₁⟩).trans (le_max_right _ _)
  · simp [Profiles.step₂, h₀, h₁]

def secondProfileBound : ℝ := Classical.choose exists_step₂_abs_bound

theorem secondProfileBound_ge_one : 1 ≤ secondProfileBound :=
  (Classical.choose_spec exists_step₂_abs_bound).1

theorem step₂_abs_bound (t : ℝ) : |Profiles.step₂ t| ≤ secondProfileBound :=
  (Classical.choose_spec exists_step₂_abs_bound).2 t

theorem scale₂_abs_bound {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    |scale₂ K r| ≤ 3/(K*r)+2/r^2 := by
  calc
    |scale₂ K r| ≤ |Profiles.step₁ (r/K-1)|/(K*r)+2*(|scale₁ K r|/r) := by
      have h := abs_sub (-Profiles.step₁ (r/K-1)/(K*r)) (2*(scale₁ K r/r))
      simpa only [scale₂, abs_div, abs_neg, abs_mul,
        abs_of_pos (mul_pos hK hr), abs_of_pos hr, abs_of_pos (by norm_num : (0:ℝ) < 2)] using h
    _ ≤ 3/(K*r)+2*((1/r)/r) := by
      gcongr
      · exact step₁_abs_bound _
      · exact scale₁_abs_bound hK hr
    _ = 3/(K*r)+2/r^2 := by ring

theorem scale₃_abs_bound {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    |scale₃ K r| ≤ secondProfileBound/(K^2*r)+9/(K*r^2)+6/r^3 := by
  calc
    |scale₃ K r| ≤ |Profiles.step₂ (r/K-1)|/(K^2*r)+
        3*|Profiles.step₁ (r/K-1)|/(K*r^2)+6*|scale₁ K r|/r^2 := by
      have h := (abs_add_le
        (-Profiles.step₂ (r/K-1)/(K^2*r)+3*Profiles.step₁ (r/K-1)/(K*r^2))
        (6*scale₁ K r/r^2)).trans
        (add_le_add_right (abs_add_le _ _) _)
      simpa only [scale₃, abs_div, abs_neg, abs_mul,
        abs_of_pos (mul_pos (sq_pos_of_pos hK) hr),
        abs_of_pos (mul_pos hK (sq_pos_of_pos hr)), abs_of_pos (sq_pos_of_pos hr),
        abs_of_pos (by norm_num : (0:ℝ) < 3), abs_of_pos (by norm_num : (0:ℝ) < 6)] using h
    _ ≤ secondProfileBound/(K^2*r)+3*3/(K*r^2)+6*(1/r)/r^2 := by
      gcongr
      · exact step₂_abs_bound _
      · exact step₁_abs_bound _
      · exact scale₁_abs_bound hK hr
    _ = secondProfileBound/(K^2*r)+9/(K*r^2)+6/r^3 := by ring

/-- Bounds for the actual first three one-dimensional derivatives of the radial
factor. The fixed scalar `secondProfileBound` is independent of `K`, `r`, and
the ambient inner product space. -/
theorem scale_derivative_bounds {K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    |deriv (scale K) r| ≤ 1/r ∧
    |deriv (deriv (scale K)) r| ≤ 3/(K*r)+2/r^2 ∧
    |deriv (deriv (deriv (scale K))) r| ≤
      secondProfileBound/(K^2*r)+9/(K*r^2)+6/r^3 := by
  rw [(scale_derivative' hK hr).deriv, (scale_second_derivative hK hr).deriv,
    (scale_third_derivative hK hr).deriv]
  exact ⟨scale₁_abs_bound hK hr, scale₂_abs_bound hK hr, scale₃_abs_bound hK hr⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def squash (K : ℝ) (z : E) : E := scale K ‖z‖ • z

theorem squash_zero (K : ℝ) : squash K (0:E) = 0 := by simp [squash]

theorem squash_identity {K : ℝ} (hK : 0 < K) {z : E} (hz : ‖z‖ ≤ K) :
    squash K z = z := by
  by_cases hz₀ : z = 0
  · subst z; exact squash_zero K
  · rw [squash, scale_identity hK (norm_pos_iff.mpr hz₀) hz, one_smul]

theorem norm_squash {K : ℝ} (hK : 0 < K) (z : E) :
    ‖squash K z‖ = K*primitive 1 (‖z‖/K) := by
  by_cases hz : z = 0
  · subst z; simp [squash_zero, primitive_zero]
  · have hr := norm_pos_iff.mpr hz
    rw [squash, norm_smul, Real.norm_eq_abs, abs_of_pos (scale_bounds hK hr).1]
    unfold scale
    field_simp

theorem norm_squash_bound {K : ℝ} (hK : 0 < K) (z : E) :
    ‖squash K z‖ ≤ 3*K/2 := by
  rw [norm_squash hK]
  have h := mul_le_mul_of_nonneg_left (primitive_upper
    (a := (1:ℝ)) (t := ‖z‖/K) (by norm_num)) hK.le
  nlinarith

theorem norm_squash_le {K : ℝ} (hK : 0 < K) (z : E) : ‖squash K z‖ ≤ ‖z‖ := by
  rw [norm_squash hK]
  have h := mul_le_mul_of_nonneg_left (primitive_le_self
    (a := (1:ℝ)) (show 0 ≤ ‖z‖/K by positivity)) hK.le
  have heq : K*(‖z‖/K) = ‖z‖ := by field_simp
  rwa [heq] at h

theorem norm_squash_lower {K : ℝ} (hK : 0 < K) {z : E} (hz : K ≤ ‖z‖) :
    K ≤ ‖squash K z‖ := by
  rw [squash, norm_smul, Real.norm_eq_abs,
    abs_of_pos (scale_bounds hK (hK.trans_le hz)).1, mul_comm]
  exact scale_radial_lower hK hz

theorem squash_contDiff {K : ℝ} (hK : 0 < K) : ContDiff ℝ 4 (squash K : E → E) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    apply (contDiffAt_id : ContDiffAt ℝ 4 (id : E → E) 0).congr_of_eventuallyEq
    have hball : ∀ᶠ x : E in 𝓝 0, ‖x‖ < K :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by simpa using hK))
    filter_upwards [hball] with x hx
    exact squash_identity hK hx.le
  · have hn : ContDiffAt ℝ 4 (fun z : E => ‖z‖) z := contDiffAt_norm ℝ hz
    have hp := (primitive_contDiff 1).contDiffAt.comp z (hn.div_const K)
    exact (contDiffAt_const.mul hp |>.div hn (norm_ne_zero_iff.mpr hz)).smul contDiffAt_id

theorem norm_hasFDerivAt {z : E} (hz : z ≠ 0) :
    HasFDerivAt (fun z : E => ‖z‖) ((1/‖z‖) • innerSL ℝ z) z := by
  have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
  simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul, two_smul,
    ContinuousLinearMap.add_apply]
  field_simp
  ring

theorem squash_fderiv_apply {K : ℝ} (hK : 0 < K) {z : E} (hz : z ≠ 0) (v : E) :
    fderiv ℝ (squash K) z v = scale K ‖z‖ • v +
      ((density 1 (‖z‖/K)-scale K ‖z‖) * ⟪z,v⟫_ℝ / ‖z‖^2) • z := by
  have hr := norm_pos_iff.mpr hz
  have hd := ((scale_derivative hK hr).comp_hasFDerivAt z (norm_hasFDerivAt hz)).smul
    (hasFDerivAt_id z)
  change HasFDerivAt (squash K) _ z at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply,
    smul_eq_mul]
  congr 1
  congr 1
  unfold scale
  field_simp [hr.ne', hK.ne']
  ring_nf
  simp

/-- A radial linear map with radial eigenvalue `d` and tangential eigenvalue `s`
is a contraction when `0 ≤ d ≤ s ≤ 1`. No dimension enters this statement. -/
theorem radial_linear_contraction {s d : ℝ} (hd : 0 ≤ d) (hds : d ≤ s) (hs : s ≤ 1)
    {e : E} (he : ‖e‖ = 1) (v : E) :
    ‖s • v + ((d-s)*⟪e,v⟫_ℝ) • e‖ ≤ ‖v‖ := by
  have hs₀ : 0 ≤ s := hd.trans hds
  have hsq : d^2 ≤ s^2 := by nlinarith
  have hs₁ : s^2 ≤ 1 := by nlinarith
  have hn : ‖s • v + ((d-s)*⟪e,v⟫_ℝ) • e‖^2 =
      s^2*‖v‖^2 + (d^2-s^2)*⟪e,v⟫_ℝ^2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm v e]
    ring
  have hnegative : (d^2-s^2)*⟪e,v⟫_ℝ^2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsq) (sq_nonneg _)
  have hscale : s^2*‖v‖^2 ≤ ‖v‖^2 := by nlinarith [sq_nonneg ‖v‖]
  nlinarith [norm_nonneg (s • v + ((d-s)*⟪e,v⟫_ℝ) • e), norm_nonneg v]

theorem squash_fderiv_norm_le {K : ℝ} (hK : 0 < K) (z : E) :
    ‖fderiv ℝ (squash K) z‖ ≤ 1 := by
  by_cases hz : z = 0
  · subst z
    have heq : squash K =ᶠ[𝓝 (0:E)] (id : E → E) := by
      have hball : ∀ᶠ x : E in 𝓝 0, ‖x‖ < K :=
        continuous_norm.continuousAt.eventually (gt_mem_nhds (by simpa using hK))
      filter_upwards [hball] with x hx
      exact squash_identity hK hx.le
    rw [heq.fderiv_eq, fderiv_id]
    exact ContinuousLinearMap.norm_id_le
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    rw [one_mul, squash_fderiv_apply hK hz]
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have he : ‖(1/‖z‖) • z‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1/‖z‖)]
      field_simp
    have h := radial_linear_contraction (density_bounds 1 (‖z‖/K)).1
      (density_le_scale hK hr) (scale_bounds hK hr).2 he v
    convert h using 1
    congr 1
    simp only [real_inner_smul_left, smul_smul]
    congr 1
    field_simp [hr.ne']
    simp only [pow_two]

theorem squash_lipschitz {K : ℝ} (hK : 0 < K) : LipschitzWith 1 (squash K : E → E) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((squash_contDiff hK).differentiable (by norm_num))
  intro z
  exact_mod_cast squash_fderiv_norm_le hK z

end GradientHessian.RadialSquash
