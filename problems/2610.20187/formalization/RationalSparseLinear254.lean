import RationalSparseRegret254

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Paper254
namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

theorem loss_linear (f : ℕ → Loss d)
    (hf : ∀ t < T, ExpConcaveOn eta W.carrier (f t))
    (hder : ∀ t < T, HasGradientWithinAt (f t) (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
      W.carrier (C.playedPoint t).val) (u : ℕ → W.carrier) :
    C.cumulativeRegret f u≤G*D*T := by
  have hp (t : ℕ) (ht : t<T) : f t (C.playedPoint t).val-f t (u t).val≤G*D := by
    let g : Space d := WithLp.toLp 2 (fun j => (C.gradient t j : ℝ))
    let w := C.playedPoint t
    have hs := surrogate_domination W C.diameter_pos C.gradient_pos C.curvature_pos (hf t ht)
      (hder t ht) (C.gradient_bound t) w.property (u t).property
    have hb := gradient_inner_bound W C.gradient_pos.le (C.gradient_bound t) w.property (u t).property
    have hgamma := Paper254.curvature_pos D G eta C.diameter_pos C.gradient_pos C.curvature_pos
    have hn : 0≤curvature D G eta/2*⟪g,(u t).val-w.val⟫^2 := by positivity
    change f t w.val-f t (u t).val≤-(⟪g,(u t).val-w.val⟫+
      curvature D G eta/2*⟪g,(u t).val-w.val⟫^2) at hs
    have hb' := (abs_le.mp hb).1
    change -(G*D)≤⟪g,(u t).val-w.val⟫ at hb'
    linarith
  have hs := Finset.sum_le_sum (s := Finset.range T) (fun t ht => hp t (Finset.mem_range.mp ht))
  simpa [cumulativeRegret,intervalCharge,mul_comm] using hs

theorem loss_one_round {d K : ℕ} {D G eta : ℝ} {W : Domain d D}
    (C : RationalSparseConstruction d 1 K D G eta W) (f : ℕ → Loss d)
    (hf : ∀ t < 1, ExpConcaveOn eta W.carrier (f t))
    (hder : ∀ t < 1, HasGradientWithinAt (f t) (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
      W.carrier (C.playedPoint t).val) (u : ℕ → W.carrier) :
    C.cumulativeRegret f u≤(d+1 : ℝ)*logFactor 1^2/curvature D G eta := by
  have hh := C.loss_linear f hf hder u
  have hc := curvature_times_radius D G eta C.diameter_pos C.gradient_pos
  have hg := Paper254.curvature_pos D G eta C.diameter_pos C.gradient_pos C.curvature_pos
  have hL := logFactor_ge_one 1 (by norm_num)
  have hd0 : (0 : ℝ)≤d := Nat.cast_nonneg d
  have hs : (1 : ℝ)≤(d+1 : ℝ)*logFactor 1^2 := by
    nlinarith [mul_nonneg hd0 (sq_nonneg (logFactor 1))]
  apply hh.trans
  apply (le_div_iff₀ hg).mpr
  norm_num only [Nat.cast_one,mul_one]
  nlinarith

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.loss_linear
#print axioms Paper254.RationalSparseConstruction.loss_one_round
