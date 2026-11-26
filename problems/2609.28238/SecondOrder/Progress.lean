import SecondOrder.Calculus

open scoped InnerProductSpace

namespace SecondOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gradient_alignment {G g : E} {τ : ℝ} (hτ : 0 ≤ τ)
    (he : ‖g-G‖ ≤ τ) (hg : 4*τ ≤ ‖g‖) :
    (3/4:ℝ)*‖g‖^2 ≤ ⟪G,g⟫_ℝ := by
  have hcs := real_inner_le_norm (g-G) g
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hcs
  have herr := mul_le_mul_of_nonneg_right he (norm_nonneg g)
  have hlarge := mul_le_mul_of_nonneg_right hg (norm_nonneg g)
  nlinarith

/-- A genuine gradient move, with the descent estimate derived from global
gradient Lipschitzness rather than included among the assumptions. -/
theorem gradient_move_progress {f : E → ℝ} {G : E → E} {L τ : ℝ}
    (hL : 0 < L) (hτ : 0 ≤ τ)
    (hd : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x-G y‖ ≤ L*‖x-y‖) (x g : E)
    (he : ‖g-G x‖ ≤ τ) (hg : 4*τ ≤ ‖g‖) :
    let h := (-1/(4*L)) • g
    τ^2/L ≤ f x-f (x+h) ∧ L*‖h‖^2 ≤ f x-f (x+h) := by
  dsimp only
  have hpos : 0 < 4*L := by positivity
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hnorm : ‖(-1/(4*L)) • g‖^2 = ‖g‖^2/(16*L^2) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hs := (abs_le.mp (smooth_remainder hd hLip x ((-1/(4*L)) • g))).2
  rw [inner_smul_right, hnorm] at hs
  have ha := gradient_alignment hτ he hg
  have hmain : 5*‖g‖^2/(32*L) ≤ f x-f (x+(-1/(4*L)) • g) := by
    have hs' := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ 32*L)
    have hc1 : (f (x+(-1/(4*L)) • g)-f x- -1/(4*L)*⟪G x,g⟫_ℝ)*(32*L) =
        (f (x+(-1/(4*L)) • g)-f x)*(32*L)+8*⟪G x,g⟫_ℝ := by
      field_simp [hL0]
      <;> ring
    have hc2 : L/2*(‖g‖^2/(16*L^2))*(32*L) = ‖g‖^2 := by
      field_simp [hL0]
      <;> ring
    rw [hc1,hc2] at hs'
    apply (div_le_iff₀ (by positivity : 0 < 32*L)).mpr
    nlinarith
  constructor
  · apply le_trans _ hmain
    apply (div_le_div_iff₀ hL (by positivity : 0 < 32*L)).mpr
    have hg2 := pow_le_pow_left₀ (by positivity : 0 ≤ 4*τ) hg 2
    nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hg2)]
  · rw [hnorm]
    apply le_trans _ hmain
    apply (le_div_iff₀ (by positivity : 0 < 32*L)).mpr
    rw [show L*(‖g‖^2/(16*L^2))*(32*L) = 2*‖g‖^2 by
      field_simp [hL0]; ring]
    nlinarith [sq_nonneg ‖g‖]

/-- Averaging the two fresh signs cancels the linear term exactly. -/
theorem signed_curvature_progress {f : E → ℝ} {G : E → E} {H : E → E →L[ℝ] E}
    {ν L γ s : ℝ} (hν : 0 < ν) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hG : ∀ x, HasFDerivAt G (H x) x)
    (hH : ∀ x y, ‖H x-H y‖ ≤ L*‖x-y‖^ν)
    (x u : E) (hu : ‖u‖ = 1) (hc : ⟪H x u,u⟫_ℝ ≤ -γ/2)
    (hscale : L*s^ν ≤ γ/8) :
    3*γ*s^2/16 ≤ f x-(f (x+s•u)+f (x+(-s)•u))/2 := by
  have hp := (abs_le.mp (holder_taylor hν hf hG hH x (s•u))).2
  have hm := (abs_le.mp (holder_taylor hν hf hG hH x ((-s)•u))).2
  have hns : ‖s•u‖ = s := by simp [norm_smul, hu, Real.norm_of_nonneg hs]
  have hnneg : ‖(-s)•u‖ = s := by simp [norm_smul, hu, Real.norm_eq_abs, abs_of_nonneg hs]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at hp hm
  rw [hns] at hp
  rw [hnneg] at hm
  have hexp : s^(2+ν) = s^2*s^ν := by
    rw [Real.rpow_add_of_nonneg hs (by norm_num : (0:ℝ) ≤ 2) hν.le, Real.rpow_two]
  have hden : 2 ≤ (1+ν)*(2+ν) := by nlinarith
  have hrem : L/((1+ν)*(2+ν))*s^(2+ν) ≤ γ*s^2/16 := by
    rw [hexp]
    have hdiv : 1/((1+ν)*(2+ν)) ≤ (1/2:ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hden
    have hv := mul_le_mul_of_nonneg_right hscale (sq_nonneg s)
    have hr := mul_le_mul_of_nonneg_left hdiv
      (mul_nonneg hL (mul_nonneg (sq_nonneg s) (Real.rpow_nonneg hs ν)))
    calc
      _ = L*(s^2*s^ν)*(1/((1+ν)*(2+ν))) := by ring
      _ ≤ L*(s^2*s^ν)*(1/2) := hr
      _ ≤ γ*s^2/16 := by nlinarith only [hv]
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg s)
  nlinarith

end SecondOrder
