import NCConcave16991.ConeRecoveryGate

/-! # Actual completion of every latched cone clock -/

noncomputable section

namespace NCConcave16991.ConeRecovery

open ConePrimitives ConeRadial ConeClockGap
open scoped InnerProductSpace

theorem clock_completion_scalar {q t r s sp sq : ℝ}
    (hq : 1 ≤ q) (hr : 0 ≤ r) (hs : 0 < s) (hsp : 0 < sp) (hsq : 0 < sq)
    (hs2 : s ^ 2 = 1 + t ^ 2 + r ^ 2)
    (hsp2 : sp ^ 2 = 1 + r ^ 2) (hsq2 : sq ^ 2 = q ^ 2 + r ^ 2)
    (ht : t / s ≤ 1)
    (hparallel : |t / s + t / q - 10 * omega (t - sp + 4)| ≤ 1 / 10)
    (hperp : |1 / s + 1 / q + 10 * omega (t - sp + 4) / sp| * r ≤ 1 / 10) :
    2 ≤ (t - sq) / q := by
  have hq0 : 0 < q := by linarith
  have ho := omega_nonneg (t - sp + 4)
  have hB : 1 / s ≤ 1 / s + 1 / q + 10 * omega (t - sp + 4) / sp := by
    linarith [one_div_nonneg.mpr hq0.le,
      div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) ho) hsp.le]
  have hrdiv : r / s ≤ 1 / 10 := by
    calc
      r / s = (1 / s) * r := by ring
      _ ≤ (1 / s + 1 / q + 10 * omega (t - sp + 4) / sp) * r :=
        mul_le_mul_of_nonneg_right hB hr
      _ ≤ |1 / s + 1 / q + 10 * omega (t - sp + 4) / sp| * r :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hr
      _ ≤ _ := hperp
  have hrs : r ≤ s / 10 := by have hh := (div_le_iff₀ hs).mp hrdiv; linarith
  have hr2 : r ^ 2 ≤ s ^ 2 / 100 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ s / 10 - r) (by linarith : 0 ≤ s / 10 + r)]
  have hA := (abs_le.mp hparallel).1
  have ht0 : 0 ≤ t := by
    by_contra hneg
    have htneg : t < 0 := lt_of_not_ge hneg
    have htq : t / q ≤ 0 := div_nonpos_of_nonpos_of_nonneg htneg.le hq0.le
    have hts : -(s / 10) ≤ t := by
      have hh : -(1 / 10 : ℝ) ≤ t / s := by linarith
      have hh' := (le_div_iff₀ hs).mp hh
      linarith
    have ht2 : t ^ 2 ≤ s ^ 2 / 100 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ s / 10 + t) (by linarith : 0 ≤ s / 10 - t)]
    have hslt : s < 2 := by nlinarith
    have hsplt : sp < 2 := by nlinarith
    have hflat := omega_one (by linarith : (7 / 8 : ℝ) ≤ t - sp + 4)
    rw [hflat] at hA
    have hts' : t / s ≤ 0 := div_nonpos_of_nonpos_of_nonneg htneg.le hs.le
    linarith
  have harg : (7 / 8 : ℝ) ≤ t - sp + 4 := by
    by_contra h
    have halt : t - sp + 4 < 7 / 8 := lt_of_not_ge h
    have hsp3 : 3 < sp := by linarith
    have htsp : t < sp := by linarith
    have ht2 : t ^ 2 ≤ sp ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ sp - t) (by linarith : 0 ≤ sp + t)]
    nlinarith
  have hflat := omega_one harg
  rw [hflat] at hA hperp
  have hcoef : 10 / sp ≤ 1 / s + 1 / q + 10 * 1 / sp := by
    linarith [one_div_nonneg.mpr hs.le, one_div_nonneg.mpr hq0.le]
  have hr10 : 10 * r / sp ≤ 1 / 10 := by
    calc
      10 * r / sp = (10 / sp) * r := by ring
      _ ≤ (1 / s + 1 / q + 10 * 1 / sp) * r :=
        mul_le_mul_of_nonneg_right hcoef hr
      _ ≤ |1 / s + 1 / q + 10 * 1 / sp| * r :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hr
      _ ≤ _ := hperp
  have hr10' := (div_le_iff₀ hsp).mp hr10
  have hr1 : r < 1 := by
    by_contra h
    have hrge : 1 ≤ r := le_of_not_gt h
    have hsp_le : sp ≤ 2 * r := by nlinarith
    nlinarith
  have htq : 89 / 10 ≤ t / q := by linarith
  have hsql : sq ≤ 2 * q := by nlinarith
  apply (le_div_iff₀ hq0).mpr
  have htt := (le_div_iff₀ hq0).mp htq
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem clock_decomposition (q : ℝ) (v z u : E) :
    clockUGradient q v z u =
      (⟪u, v⟫_ℝ / Real.sqrt (1 + ‖u‖ ^ 2) + ⟪u, v⟫_ℝ / q -
        10 * omega (clockArgument v z u)) • v +
      (1 / Real.sqrt (1 + ‖u‖ ^ 2) + 1 / q +
        10 * omega (clockArgument v z u) / Real.sqrt (1 + ‖perpendicular v u‖ ^ 2)) •
          perpendicular v u := by
  have hu : u = ⟪u, v⟫_ℝ • v + perpendicular v u := by unfold perpendicular; abel
  unfold clockUGradient
  conv_lhs => arg 1; arg 2; rw [hu]
  simp only [div_eq_mul_inv]
  module

/-- Once its latch is one, a small actual clock gradient forces its exit
gate to equal one. This is the concrete clock fact in Section D. -/
theorem clock_completed {q : ℝ} (hq : 1 ≤ q) (v z u : E) (hv : ‖v‖ = 1)
    (hH : latch ⟪zeta z, v⟫_ℝ = 1) (hsmall : ‖clockUGradient q v z u‖ ≤ 1 / 10) :
    exitGate q v u = 1 := by
  let A := ⟪u, v⟫_ℝ / Real.sqrt (1 + ‖u‖ ^ 2) + ⟪u, v⟫_ℝ / q -
    10 * omega (clockArgument v z u)
  let B := 1 / Real.sqrt (1 + ‖u‖ ^ 2) + 1 / q +
    10 * omega (clockArgument v z u) / Real.sqrt (1 + ‖perpendicular v u‖ ^ 2)
  have hdecomp := clock_decomposition q v z u
  change _ = A • v + B • perpendicular v u at hdecomp
  rw [hdecomp] at hsmall
  have hparallel : |A| ≤ 1 / 10 := by
    have hh := abs_real_inner_le_norm (A • v + B • perpendicular v u) v
    rw [orthogonal_block_inner v _ hv (perpendicular_inner v u hv), hv, mul_one] at hh
    exact hh.trans hsmall
  have hperp := (orthogonal_block_perp_norm v _ hv (perpendicular_inner v u hv) A B).trans hsmall
  have ha : clockArgument v z u = ⟪u, v⟫_ℝ - Real.sqrt (1 + ‖perpendicular v u‖ ^ 2) + 4 := by
    simp only [clockArgument, hH, mul_one]
  dsimp only [A] at hparallel
  dsimp only [B] at hperp
  rw [ha] at hparallel hperp
  have ht : ⟪u, v⟫_ℝ / Real.sqrt (1 + ‖u‖ ^ 2) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (1 + ‖u‖ ^ 2))).mpr
    have hi := real_inner_le_norm u v
    rw [hv, mul_one] at hi
    have hn : ‖u‖ ≤ Real.sqrt (1 + ‖u‖ ^ 2) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 1 + ‖u‖ ^ 2 by positivity),
        Real.sqrt_nonneg (1 + ‖u‖ ^ 2), norm_nonneg u]
    simpa only [one_mul] using hi.trans hn
  have hq0 : 0 < q := by linarith
  have hnorm := norm_sq_decomposition v u hv
  have hs2 : (Real.sqrt (1 + ‖u‖ ^ 2)) ^ 2 =
      1 + ⟪u, v⟫_ℝ ^ 2 + ‖perpendicular v u‖ ^ 2 := by
    rw [Real.sq_sqrt (by positivity), hnorm]
    ring
  have hξ := clock_completion_scalar hq (norm_nonneg _) (by positivity) (by positivity)
    (by positivity) hs2 (Real.sq_sqrt (by positivity)) (Real.sq_sqrt (by positivity))
    ht hparallel hperp
  exact exitStep_one hξ

end NCConcave16991.ConeRecovery
