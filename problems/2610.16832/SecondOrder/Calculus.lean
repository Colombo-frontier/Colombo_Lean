import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

open scoped InnerProductSpace

namespace SecondOrder

/-- Comparison by integration, proved from the mean value theorem. -/
theorem scalar_comparison {f g f' g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hle : ∀ t ∈ Set.Icc a b, f' t ≤ g' t) : f b-f a ≤ g b-g a := by
  have hd (t : ℝ) := (hg t).sub (hf t)
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (show ContinuousOn (fun t => g t-f t) (Set.Icc a b) from
      (show Continuous (fun t => g t-f t) from continuous_iff_continuousAt.mpr
        (fun t => (hd t).continuousAt)).continuousOn)
    (fun t _ => (hd t).hasDerivWithinAt)
    (fun t ht => sub_nonneg.mpr (hle t (interior_subset ht)))
  have h := hm (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
  dsimp only at h
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem line_hasDerivAt {f : E → ℝ} {G : E → E}
    (hd : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x) (x h : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => f (x+t•h)) ⟪G (x+t•h),h⟫_ℝ t := by
  simpa only [id_eq, one_smul] using
    (hd _).comp_hasDerivAt t (((hasDerivAt_id t).smul_const h).const_add x)

/- Adapted from ExactValue.SmoothModel; generalized from Euclidean space to a
real inner product space and with no dependency on that project. -/
theorem smooth_remainder {f : E → ℝ} {G : E → E} {L : ℝ}
    (hd : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x-G y‖ ≤ L*‖x-y‖) (x h : E) :
    |f (x+h)-f x-⟪G x,h⟫_ℝ| ≤ L/2*‖h‖^2 := by
  let φ := fun t : ℝ => f (x+t•h)-f x-t*⟪G x,h⟫_ℝ
  let q := fun t : ℝ => L/2*t^2*‖h‖^2
  have hφ (t : ℝ) : HasDerivAt φ ⟪G (x+t•h)-G x,h⟫_ℝ t := by
    convert ((line_hasDerivAt hd x h t).sub_const (f x)).sub
      ((hasDerivAt_id t).mul_const ⟪G x,h⟫_ℝ) using 1
    simp only [inner_sub_left, one_mul]
  have hq (t : ℝ) : HasDerivAt q (L*t*‖h‖^2) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (L/2)).mul_const (‖h‖^2) using 1
    dsimp only [id_eq]
    ring
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      |⟪G (x+t•h)-G x,h⟫_ℝ| ≤ L*t*‖h‖^2 := by
    have hi := abs_real_inner_le_norm (G (x+t•h)-G x) h
    have hl := hLip (x+t•h) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hl
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg h)
    nlinarith
  have hup := scalar_comparison (by norm_num : (0:ℝ) ≤ 1) hφ hq
    (fun t ht => (le_abs_self _).trans (hb t ht))
  have hlo := scalar_comparison (by norm_num : (0:ℝ) ≤ 1) (fun t => (hφ t).neg) hq
    (fun t ht => (neg_le_abs _).trans (hb t ht))
  simp only [φ, q, one_smul, zero_smul, add_zero, zero_mul, one_pow,
    zero_pow (by decide : 2 ≠ 0), mul_one, one_mul, mul_zero, sub_self,
    sub_zero, neg_zero] at hup hlo
  exact abs_le.mpr ⟨by linarith, hup⟩

/-- Exact scalar C^(2,ν) Taylor remainder on the unit segment. -/
theorem holder_taylor_scalar {f f' f'' : ℝ → ℝ} {ν C : ℝ} (hν : 0 < ν)
    (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : ∀ t, HasDerivAt f' (f'' t) t)
    (hmod : ∀ t ∈ Set.Icc (0:ℝ) 1, |f'' t-f'' 0| ≤ C*t^ν) :
    |f 1-f 0-f' 0-f'' 0/2| ≤ C/((1+ν)*(2+ν)) := by
  have hn1 : 1+ν ≠ 0 := by linarith
  have hn2 : 2+ν ≠ 0 := by linarith
  let R₁ := fun t : ℝ => f' t-f' 0-t*f'' 0
  let Q₁ := fun t : ℝ => C/(1+ν)*t^(1+ν)
  have hR₁ (t : ℝ) : HasDerivAt R₁ (f'' t-f'' 0) t := by
    simpa only [one_mul] using ((hf' t).sub_const (f' 0)).sub
      ((hasDerivAt_id t).mul_const (f'' 0))
  have hQ₁ (t : ℝ) : HasDerivAt Q₁ (C*t^ν) t := by
    convert (Real.hasDerivAt_rpow_const (x := t) (p := 1+ν) (Or.inr (by linarith))).const_mul (C/(1+ν)) using 1
    rw [show 1+ν-1=ν by ring]
    field_simp
    <;> ring
  have hb₁ (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : |R₁ t| ≤ Q₁ t := by
    have hu := scalar_comparison ht.1 hR₁ hQ₁ (fun u hu =>
      (le_abs_self _).trans (hmod u ⟨hu.1, hu.2.trans ht.2⟩))
    have hl := scalar_comparison ht.1 (fun u => (hR₁ u).neg) hQ₁ (fun u hu =>
      (neg_le_abs _).trans (hmod u ⟨hu.1, hu.2.trans ht.2⟩))
    have hz : R₁ 0 = 0 := by simp [R₁]
    have hqz : Q₁ 0 = 0 := by simp [Q₁, Real.zero_rpow hn1]
    rw [hz, hqz, sub_zero, sub_zero] at hu
    rw [hz, neg_zero, hqz, sub_zero, sub_zero] at hl
    exact abs_le.mpr ⟨by linarith, hu⟩
  let R₂ := fun t : ℝ => f t-f 0-t*f' 0-t^2/2*f'' 0
  let Q₂ := fun t : ℝ => C/((1+ν)*(2+ν))*t^(2+ν)
  have hR₂ (t : ℝ) : HasDerivAt R₂ (R₁ t) t := by
    convert (((hf t).sub_const (f 0)).sub ((hasDerivAt_id t).mul_const (f' 0))).sub
      ((((hasDerivAt_id t).pow 2).div_const 2).mul_const (f'' 0)) using 1
    dsimp [R₁]
    ring
  have hQ₂ (t : ℝ) : HasDerivAt Q₂ (Q₁ t) t := by
    convert (Real.hasDerivAt_rpow_const (x := t) (p := 2+ν) (Or.inr (by linarith))).const_mul
      (C/((1+ν)*(2+ν))) using 1
    rw [show 2+ν-1=1+ν by ring]
    dsimp [Q₁]
    field_simp
    <;> ring
  have hu := scalar_comparison (by norm_num : (0:ℝ) ≤ 1) hR₂ hQ₂
    (fun t ht => (le_abs_self _).trans (hb₁ t ht))
  have hl := scalar_comparison (by norm_num : (0:ℝ) ≤ 1) (fun t => (hR₂ t).neg) hQ₂
    (fun t ht => (neg_le_abs _).trans (hb₁ t ht))
  simp [R₂, Q₂, Real.zero_rpow hn2] at hu hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem holder_taylor {f : E → ℝ} {G : E → E} {H : E → E →L[ℝ] E} {ν L : ℝ}
    (hν : 0 < ν) (hf : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x, HasFDerivAt G (H x) x)
    (hH : ∀ x y, ‖H x-H y‖ ≤ L*‖x-y‖^ν) (x h : E) :
    |f (x+h)-f x-⟪G x,h⟫_ℝ-⟪H x h,h⟫_ℝ/2| ≤
      L/((1+ν)*(2+ν))*‖h‖^(2+ν) := by
  let f' := fun t : ℝ => ⟪G (x+t•h),h⟫_ℝ
  let f'' := fun t : ℝ => ⟪H (x+t•h) h,h⟫_ℝ
  have hd (t : ℝ) : HasDerivAt f' (f'' t) t := by
    have hline : HasDerivAt (fun t : ℝ => G (x+t•h)) (H (x+t•h) h) t := by
      simpa only [id_eq, one_smul] using
        (hG _).comp_hasDerivAt t (((hasDerivAt_id t).smul_const h).const_add x)
    simpa only [inner_zero_right, zero_add] using hline.inner ℝ (hasDerivAt_const t h)
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      |f'' t-f'' 0| ≤ (L*‖h‖^(2+ν))*t^ν := by
    dsimp [f'']
    simp only [zero_smul, add_zero]
    rw [← inner_sub_left]
    have hi := abs_real_inner_le_norm ((H (x+t•h)-H x) h) h
    have hop := (H (x+t•h)-H x).le_opNorm h
    have hmod := hH (x+t•h) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1] at hmod
    calc
      _ ≤ (‖H (x+t•h)-H x‖*‖h‖)*‖h‖ :=
        hi.trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
      _ ≤ (L*(t*‖h‖)^ν*‖h‖)*‖h‖ := by gcongr
      _ = _ := by
        rw [Real.mul_rpow ht.1 (norm_nonneg _),
          Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2) hν.le,
          Real.rpow_two]
        ring
  have ht := holder_taylor_scalar hν (line_hasDerivAt hf x h) hd hb
  simpa [f', f'', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using ht

end SecondOrder
