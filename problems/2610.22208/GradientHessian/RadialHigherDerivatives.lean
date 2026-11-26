import GradientHessian.RadialSquash
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Nat.Choose.Sum

/-!
Dimension-independent operator bounds for the actual integrated-septic radial
squash. A scalar coefficient in the squared radius controls a fixed ball;
outside that ball, exact tail homogeneity reduces to the fixed ball. Radius
scaling then gives the second- and third-order bounds in `lem:squash`.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators InnerProductSpace

namespace GradientHessian.RadialHigherDerivatives
open IntegralProfiles RadialSquash

def coefficient (t : ℝ) : ℝ :=
  if t ≤ 1 then 1 else primitive 1 (Real.sqrt t) / Real.sqrt t

theorem coefficient_eq_ratio {t : ℝ} (ht : 0 < t) :
    coefficient t = primitive 1 (Real.sqrt t) / Real.sqrt t := by
  by_cases h : t ≤ 1
  · rw [coefficient, if_pos h, primitive_identity (by norm_num)
      ((Real.sqrt_le_one).mpr h), div_self (Real.sqrt_pos.mpr ht).ne']
  · exact if_neg h

theorem coefficient_contDiff : ContDiff ℝ 4 coefficient := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t < 1
  · apply (contDiffAt_const : ContDiffAt ℝ 4 (fun _ : ℝ => (1:ℝ)) t).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ht] with u hu
    exact if_pos hu.le
  · have ht₀ : 0 < t := by linarith
    have hs : ContDiffAt ℝ 4 Real.sqrt t := Real.contDiffAt_sqrt ht₀.ne'
    apply (((primitive_contDiff 1).contDiffAt.comp t hs).div hs
      (Real.sqrt_pos.mpr ht₀).ne').congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht₀] with u hu
    exact coefficient_eq_ratio hu

theorem coefficient_jet_bound (n : ℕ) (hn : n ≤ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ t ∈ Icc (0:ℝ) 16,
      |iteratedDeriv i coefficient t| ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (coefficient_contDiff.continuous.continuousOn : ContinuousOn coefficient (Icc (0:ℝ) 16))
    refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro i hi t ht
    have hi₀ : i = 0 := by omega
    simpa only [hi₀, iteratedDeriv_zero, Real.norm_eq_abs] using
      (hC t ht).trans (le_max_right 1 C)
  | succ n ih =>
    obtain ⟨C, hC, hbound⟩ := ih (by omega)
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((coefficient_contDiff.continuous_iteratedDeriv (n+1)
        (by exact_mod_cast hn)).continuousOn :
          ContinuousOn (iteratedDeriv (n+1) coefficient) (Icc (0:ℝ) 16))
    refine ⟨max C M, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
    intro i hi t ht
    by_cases hin : i ≤ n
    · exact (hbound i hin t ht).trans (le_max_left _ _)
    · have heq : i = n+1 := by omega
      subst i
      exact (show |iteratedDeriv (n+1) coefficient t| ≤ M by
        simpa only [Real.norm_eq_abs] using hM t ht).trans (le_max_right _ _)

def coefficientJetBound : ℝ := (coefficient_jet_bound 4 le_rfl).choose

theorem coefficientJetBound_pos : 0 < coefficientJetBound :=
  (coefficient_jet_bound 4 le_rfl).choose_spec.1

theorem coefficientJetBound_spec {i : ℕ} (hi : i ≤ 4) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 16) :
    ‖iteratedFDeriv ℝ i coefficient t‖ ≤ coefficientJetBound := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (coefficient_jet_bound 4 le_rfl).choose_spec.2 i hi t ht

/-- Defined without an ambient space or a radius. -/
def radialConstant (n : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    (i.factorial * coefficientJetBound * 32^i) * 4

theorem radialConstant_pos (n : ℕ) : 0 < radialConstant n := by
  have hC := coefficientJetBound_pos
  unfold radialConstant
  positivity

section Normed
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_linear_succ_le (A : E →L[ℝ] F) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (n+1) A x‖ ≤ ‖A‖ := by
  rw [← norm_iteratedFDeriv_fderiv]
  have hA : fderiv ℝ A = fun _ => A := funext (fun _ => A.fderiv)
  rw [hA]
  cases n with
  | zero => rw [norm_iteratedFDeriv_zero]
  | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; exact norm_nonneg A

theorem norm_iteratedFDeriv_id_le_four (i : ℕ) {x : E} (hx : ‖x‖ ≤ 4) :
    ‖iteratedFDeriv ℝ i (id : E → E) x‖ ≤ 4 := by
  cases i with
  | zero => simpa only [norm_iteratedFDeriv_zero, id_eq] using hx
  | succ i =>
    exact (norm_iteratedFDeriv_linear_succ_le (ContinuousLinearMap.id ℝ E) i x).trans
      (ContinuousLinearMap.norm_id_le.trans (by norm_num))

theorem iteratedFDeriv_eq_of_eventuallyEq {f g : E → F} {x : E}
    (h : f =ᶠ[𝓝 x] g) (n : ℕ) : iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  have hw : f =ᶠ[𝓝[univ] x] g := by simpa only [nhdsWithin_univ] using h
  simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq h.self_of_nhds n

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem squash_one_eq_coefficient (x : E) :
    squash 1 x = coefficient ⟪x,x⟫_ℝ • x := by
  rw [real_inner_self_eq_norm_sq]
  by_cases hx : ‖x‖ ≤ 1
  · have hsq : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
    rw [squash_identity (by norm_num) hx, coefficient, if_pos hsq, one_smul]
  · have hsq : ¬ ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
    simp [coefficient, hsq, Real.sqrt_sq_eq_abs, abs_norm, squash, scale]

theorem norm_iteratedFDeriv_inner_self_le {x : E} (hx : ‖x‖ ≤ 4) (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun y : E => ⟪y,y⟫_ℝ) x‖ ≤ (32:ℝ)^i := by
  have h := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (show ContDiff ℝ i (id : E → E) from contDiff_id) contDiff_id x le_rfl (norm_innerSL_le ℝ)
  have hsum : (∑ j ∈ Finset.range (i+1), (i.choose j : ℝ)) = 2^i := by
    exact_mod_cast Nat.sum_range_choose i
  calc
    _ ≤ ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (id : E → E) x‖ * ‖iteratedFDeriv ℝ (i-j) (id : E → E) x‖ := h
    _ ≤ ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ)*4*4 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_id_le_four j hx) (Nat.cast_nonneg _))
        (norm_iteratedFDeriv_id_le_four (i-j) hx) (norm_nonneg _) (by positivity)
    _ = 16*2^i := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]; ring
    _ ≤ 16^i*2^i := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 16) hi
    _ = 32^i := by rw [← mul_pow]; norm_num

theorem coefficient_inner_derivative_bound {i : ℕ} (hi : i ≤ 4) {x : E} (hx : ‖x‖ ≤ 4) :
    ‖iteratedFDeriv ℝ i (fun y : E => coefficient ⟪y,y⟫_ℝ) x‖ ≤
      i.factorial * coefficientJetBound * 32^i := by
  apply norm_iteratedFDeriv_comp_le coefficient_contDiff
    (show ContDiff ℝ 4 (fun y : E => ⟪y,y⟫_ℝ) from contDiff_id.inner ℝ contDiff_id)
    (by exact_mod_cast hi) x
  · intro j hj
    apply coefficientJetBound_spec (hj.trans hi)
    rw [real_inner_self_eq_norm_sq]
    exact ⟨sq_nonneg _, by nlinarith [norm_nonneg x]⟩
  · intro j hj _
    exact norm_iteratedFDeriv_inner_self_le hx j hj

theorem unit_derivative_bound_on_ball (n : ℕ) (hn : n ≤ 4) {x : E} (hx : ‖x‖ ≤ 4) :
    ‖iteratedFDeriv ℝ n (squash 1 : E → E) x‖ ≤ radialConstant n := by
  have heq : (squash 1 : E → E) = fun x => coefficient ⟪x,x⟫_ℝ • x :=
    funext squash_one_eq_coefficient
  rw [heq]
  have hs : ContDiff ℝ 4 (fun y : E => coefficient ⟪y,y⟫_ℝ) :=
    coefficient_contDiff.comp (contDiff_id.inner ℝ contDiff_id)
  have h := norm_iteratedFDeriv_smul_le hs (show ContDiff ℝ 4 (id : E → E) from contDiff_id)
    x (by exact_mod_cast hn)
  apply h.trans
  apply le_trans (Finset.sum_le_sum ?_) (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1))
  intro i hi
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (coefficient_inner_derivative_bound
      ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn) hx) (Nat.cast_nonneg _))
    (norm_iteratedFDeriv_id_le_four (n-i) hx) (norm_nonneg _)
    (by have hC := coefficientJetBound_pos; positivity)

theorem squash_one_tail {x : E} (hx : 2 ≤ ‖x‖) :
    squash 1 x = ((3/2:ℝ)/‖x‖) • x := by
  rw [squash, scale, one_mul, div_one, primitive_plateau (by norm_num)
    (by linarith : (1:ℝ)+1 ≤ ‖x‖)]
  norm_num

theorem squash_one_tail_smul {a : ℝ} (ha : 0 < a) {x : E}
    (hx : 2 ≤ ‖x‖) (hax : 2 ≤ ‖a • x‖) : squash 1 (a • x) = squash 1 x := by
  rw [squash_one_tail hax, squash_one_tail hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos ha, smul_smul]
  congr 1
  field_simp
  ring

theorem unit_derivative_bound (n : ℕ) (hn : n ≤ 4) (x : E) :
    ‖iteratedFDeriv ℝ n (squash 1 : E → E) x‖ ≤ radialConstant n := by
  by_cases hx : ‖x‖ ≤ 4
  · exact unit_derivative_bound_on_ball n hn hx
  have hr : 0 < ‖x‖ := by linarith
  let a : ℝ := 3/‖x‖
  have ha : 0 < a := by dsimp [a]; positivity
  have ha₁ : a ≤ 1 := by dsimp [a]; apply (div_le_one hr).mpr; linarith
  let A : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ 1 := by
    calc
      ‖A‖ = a * ‖ContinuousLinearMap.id ℝ E‖ := by
        simp only [A, norm_smul a (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a := mul_le_of_le_one_right ha.le ContinuousLinearMap.norm_id_le
      _ ≤ 1 := ha₁
  have hAx : ‖A x‖ = 3 := by
    simp only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    dsimp [a]
    field_simp
  have heq : (squash 1 : E → E) =ᶠ[𝓝 x] (squash 1 ∘ A) := by
    have hy : ∀ᶠ y : E in 𝓝 x, 2 < ‖y‖ :=
      continuous_norm.continuousAt.eventually (lt_mem_nhds (by linarith : 2 < ‖x‖))
    have hAy : ∀ᶠ y : E in 𝓝 x, 2 < ‖A y‖ :=
      (continuous_norm.comp A.continuous).continuousAt.eventually
        (lt_mem_nhds (by rw [hAx]; norm_num : (2:ℝ) < ‖A x‖))
    filter_upwards [hy, hAy] with y hy hAy
    exact (squash_one_tail_smul ha hy.le hAy.le).symm
  rw [iteratedFDeriv_eq_of_eventuallyEq heq n,
    A.iteratedFDeriv_comp_right (squash_contDiff (by norm_num : (0:ℝ) < 1)) x
      (by exact_mod_cast hn)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (squash 1 : E → E) (A x)‖ * ‖A‖^n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (squash 1 : E → E) (A x)).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ radialConstant n * 1 := mul_le_mul
      (unit_derivative_bound_on_ball n hn (by rw [hAx]; norm_num))
      (pow_le_one₀ (norm_nonneg A) hA) (by positivity) (radialConstant_pos n).le
    _ = radialConstant n := mul_one _

theorem squash_radius_scaling {K : ℝ} (hK : 0 < K) (x : E) :
    squash K x = K • squash 1 (K⁻¹ • x) := by
  by_cases hx : x = 0
  · subst x; simp [squash_zero]
  simp only [squash, scale, one_mul, div_one, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hK, smul_smul]
  rw [inv_mul_eq_div]
  congr 1
  field_simp [hK.ne', norm_ne_zero_iff.mpr hx]
  ring

theorem squash_derivative_bound (n : ℕ) (hn : n ≤ 4) {K : ℝ} (hK : 0 < K) (x : E) :
    ‖iteratedFDeriv ℝ n (squash K : E → E) x‖ ≤ radialConstant n * K^(1-(n:ℤ)) := by
  let A : E →L[ℝ] E := K⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ K⁻¹ := by
    dsimp only [A]
    rw [norm_smul K⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hK.le) ContinuousLinearMap.norm_id_le
  have heq : (squash K : E → E) = K • ((squash 1 : E → E) ∘ A) := by
    funext y
    exact squash_radius_scaling hK y
  have hu : ContDiff ℝ n (squash 1 : E → E) :=
    (squash_contDiff (by norm_num : (0:ℝ) < 1)).of_le (by exact_mod_cast hn)
  rw [heq, iteratedFDeriv_const_smul_apply
      ((hu.comp A.contDiff).contDiffAt),
    norm_smul K (iteratedFDeriv ℝ n ((squash 1 : E → E) ∘ A) x), Real.norm_eq_abs, abs_of_pos hK,
    A.iteratedFDeriv_comp_right hu x le_rfl]
  calc
    _ ≤ K*(‖iteratedFDeriv ℝ n (squash 1 : E → E) (A x)‖ * ‖A‖^n) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (squash 1 : E → E) (A x)).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ K*(radialConstant n * (K⁻¹)^n) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      exact mul_le_mul (unit_derivative_bound n hn (A x))
        (pow_le_pow_left₀ (norm_nonneg A) hA n) (by positivity) (radialConstant_pos n).le
    _ = radialConstant n * K^(1-(n:ℤ)) := by
      rw [zpow_sub₀ hK.ne', zpow_one, zpow_natCast, div_eq_mul_inv, ← inv_pow]
      ring

theorem squash_second_bound {K : ℝ} (hK : 0 < K) (x : E) :
    ‖iteratedFDeriv ℝ 2 (squash K : E → E) x‖ ≤ radialConstant 2 / K := by
  have h := squash_derivative_bound 2 (by norm_num) hK x
  simpa only [Nat.cast_ofNat, show (1:ℤ)-2 = -1 by norm_num, zpow_neg_one,
    div_eq_mul_inv] using h

theorem squash_third_bound {K : ℝ} (hK : 0 < K) (x : E) :
    ‖iteratedFDeriv ℝ 3 (squash K : E → E) x‖ ≤ radialConstant 3 / K^2 := by
  have h := squash_derivative_bound 3 (by norm_num) hK x
  simpa only [Nat.cast_ofNat, show (1:ℤ)-3 = -2 by norm_num, zpow_neg, zpow_ofNat,
    div_eq_mul_inv] using h

/-- The source radial factor, with its removable value one at radius zero.
The extension to negative radii is also constant one. -/
def radialFactor (K r : ℝ) : ℝ := if r ≤ 0 then 1 else scale K r

theorem radialFactor_eq_scale {K r : ℝ} (hr : 0 < r) :
    radialFactor K r = scale K r := by simp [radialFactor, not_le.mpr hr]

theorem radialFactor_identity {K r : ℝ} (hK : 0 < K) (hrK : r ≤ K) :
    radialFactor K r = 1 := by
  by_cases hr : r ≤ 0
  · simp [radialFactor, hr]
  · rw [radialFactor_eq_scale (lt_of_not_ge hr)]
    exact scale_identity hK (lt_of_not_ge hr) hrK

theorem radialFactor_pos {K : ℝ} (hK : 0 < K) (r : ℝ) : 0 < radialFactor K r := by
  by_cases hr : r ≤ 0
  · simp [radialFactor, hr]
  · rw [radialFactor_eq_scale (lt_of_not_ge hr)]
    exact (scale_bounds hK (lt_of_not_ge hr)).1

theorem radialFactor_eventually_scale {K r : ℝ} (hr : 0 < r) :
    radialFactor K =ᶠ[𝓝 r] scale K := by
  filter_upwards [lt_mem_nhds hr] with t ht
  exact radialFactor_eq_scale ht

theorem radialFactor_eventually_one {K r : ℝ} (hK : 0 < K) (hrK : r < K) :
    radialFactor K =ᶠ[𝓝 r] (fun _ => 1) := by
  filter_upwards [gt_mem_nhds hrK] with t ht
  exact radialFactor_identity hK ht.le

theorem radialFactor_differentiableAt {K : ℝ} (hK : 0 < K) (r : ℝ) :
    DifferentiableAt ℝ (radialFactor K) r := by
  by_cases hr : r < K
  · exact ((hasDerivAt_const r (1:ℝ)).congr_of_eventuallyEq
      (radialFactor_eventually_one hK hr)).differentiableAt
  · have hr₀ : 0 < r := hK.trans_le (le_of_not_gt hr)
    exact ((scale_derivative hK hr₀).congr_of_eventuallyEq
      (radialFactor_eventually_scale hr₀)).differentiableAt

theorem radialFactor_derivative_nonpos {K : ℝ} (hK : 0 < K) (r : ℝ) :
    deriv (radialFactor K) r ≤ 0 := by
  by_cases hr : r < K
  · rw [(radialFactor_eventually_one hK hr).deriv_eq, deriv_const]
  · have hr₀ : 0 < r := hK.trans_le (le_of_not_gt hr)
    rw [(radialFactor_eventually_scale hr₀).deriv_eq]
    exact scale_derivative_nonpos hK hr₀

theorem radialFactor_radial_lower {K r : ℝ} (hK : 0 < K) (hrK : K ≤ r) :
    K ≤ r * radialFactor K r := by
  rw [radialFactor_eq_scale (hK.trans_le hrK)]
  exact scale_radial_lower hK hrK

theorem squash_eq_radialFactor (K : ℝ) (x : E) :
    squash K x = radialFactor K ‖x‖ • x := by
  by_cases hx : x = 0
  · subst x; simp [squash_zero]
  · rw [radialFactor_eq_scale (norm_pos_iff.mpr hx)]
    rfl

/-- One fixed absolute constant for both higher derivative estimates. -/
def squashConstant : ℝ := max (radialConstant 2) (radialConstant 3)

theorem squashConstant_pos : 0 < squashConstant :=
  (radialConstant_pos 2).trans_le (le_max_left _ _)

/-- All conclusions of the manuscript's `lem:squash`, including radius zero,
with one absolute constant independent of the ambient real inner product space. -/
theorem radial_squash_bounds {K : ℝ} (hK : 0 < K) (x : E) :
    squash K x = radialFactor K ‖x‖ • x ∧
    0 < radialFactor K ‖x‖ ∧
    deriv (radialFactor K) ‖x‖ ≤ 0 ∧
    ‖fderiv ℝ (squash K : E → E) x‖ ≤ 1 ∧
    ‖iteratedFDeriv ℝ 2 (squash K : E → E) x‖ ≤ squashConstant / K ∧
    ‖iteratedFDeriv ℝ 3 (squash K : E → E) x‖ ≤ squashConstant / K^2 ∧
    (K ≤ ‖x‖ → K ≤ ‖x‖ * radialFactor K ‖x‖) := by
  refine ⟨squash_eq_radialFactor K x, radialFactor_pos hK _,
    radialFactor_derivative_nonpos hK _, squash_fderiv_norm_le hK x,
    (squash_second_bound hK x).trans ?_, (squash_third_bound hK x).trans ?_,
    fun hx => radialFactor_radial_lower hK hx⟩
  · exact div_le_div_of_nonneg_right (le_max_left _ _) hK.le
  · exact div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg K)

end GradientHessian.RadialHigherDerivatives
