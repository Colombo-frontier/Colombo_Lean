import VIReference.Pilot.ModelExistence

open Set
open scoped RealInnerProductSpace

namespace VIReference.Pilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unscaled radial regularizer in `lem:model-existence`. -/
def radialPower (q : ℕ) (a : E) : E := ‖a‖ ^ q • a

/-- Quantitative monotonicity of the radial power map. -/
theorem radialPower_pair_lower (q : ℕ) (a b : E) :
    (1 / 2 : ℝ) * (‖a‖ ^ q + ‖b‖ ^ q) * ‖a - b‖ ^ 2 ≤
      inner ℝ (radialPower q a - radialPower q b) (a - b) := by
  let r : ℝ := ‖a‖
  let s : ℝ := ‖b‖
  let A : ℝ := r ^ q
  let B : ℝ := s ^ q
  let c : ℝ := inner ℝ a b
  have hr : 0 ≤ r := norm_nonneg a
  have hs : 0 ≤ s := norm_nonneg b
  have hpowsame : 0 ≤ (A - B) * (r ^ 2 - s ^ 2) := by
    rcases le_total r s with hrs | hrs
    · have hAB : A ≤ B := by
        dsimp [A, B]
        exact pow_le_pow_left₀ hr hrs q
      have hrsq : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr hrs 2
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hAB) (sub_nonpos.mpr hrsq)
    · have hBA : B ≤ A := by
        dsimp [A, B]
        exact pow_le_pow_left₀ hs hrs q
      have hsrq : s ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hs hrs 2
      exact mul_nonneg (sub_nonneg.mpr hBA) (sub_nonneg.mpr hsrq)
  have hnorm : ‖a - b‖ ^ 2 = r ^ 2 + s ^ 2 - 2 * c := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [r, s, c]
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm b a]
    ring
  have hexpand : inner ℝ (radialPower q a - radialPower q b) (a - b) =
      A * r ^ 2 + B * s ^ 2 - (A + B) * c := by
    dsimp [radialPower, A, B, r, s, c]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, conj_trivial,
      real_inner_self_eq_norm_sq]
    rw [real_inner_comm b a]
    ring
  rw [hexpand, hnorm]
  dsimp [A, B, r, s]
  nlinarith

/-- The radial power map is strictly monotone.  This proof is algebraic and
does not use differentiability of the norm at the origin. -/
theorem radialPower_strictMonotone (q : ℕ) {a b : E} (hab : a ≠ b) :
    0 < inner ℝ (radialPower q a - radialPower q b) (a - b) := by
  let r : ℝ := ‖a‖
  let s : ℝ := ‖b‖
  let A : ℝ := r ^ q
  let B : ℝ := s ^ q
  let c : ℝ := inner ℝ a b
  have hr : 0 ≤ r := norm_nonneg a
  have hs : 0 ≤ s := norm_nonneg b
  have hA : 0 ≤ A := pow_nonneg hr q
  have hB : 0 ≤ B := pow_nonneg hs q
  have hc : c ≤ r * s := by
    dsimp [c, r, s]
    exact real_inner_le_norm _ _
  have hexpand : inner ℝ (radialPower q a - radialPower q b) (a - b) =
      A * r ^ 2 + B * s ^ 2 - (A + B) * c := by
    dsimp [radialPower, A, B, r, s, c]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, conj_trivial,
      real_inner_self_eq_norm_sq]
    rw [real_inner_comm b a]
    ring
  rw [hexpand]
  have hlower :
      A * r ^ 2 + B * s ^ 2 - (A + B) * (r * s) ≤
        A * r ^ 2 + B * s ^ 2 - (A + B) * c := by
    gcongr
  by_cases hrs : r = s
  · have habnorm : ‖a‖ = ‖b‖ := by
      change r = s
      exact hrs
    rw [hrs] at *
    have hrpos : 0 < s := by
      by_contra h
      have hs0 : s = 0 := le_antisymm (le_of_not_gt h) hs
      have ha0 : a = 0 := norm_eq_zero.mp (habnorm.trans (by simpa [s] using hs0))
      have hb0 : b = 0 := norm_eq_zero.mp (by simpa [s] using hs0)
      exact hab (ha0.trans hb0.symm)
    have hdiff : 0 < ‖a - b‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab))
    have hcform : ‖a - b‖ ^ 2 = 2 * (s ^ 2 - c) := by
      rw [← real_inner_self_eq_norm_sq]
      dsimp [c, s] at *
      simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
      rw [real_inner_comm b a]
      nlinarith [habnorm]
    have hBpos : 0 < B := pow_pos hrpos q
    dsimp [A, B] at *
    nlinarith
  · rcases lt_or_gt_of_ne hrs with hrslt | hrslt
    · have hpow : A * r < B * s := by
        dsimp [A, B]
        simpa [pow_succ] using pow_lt_pow_left₀ hrslt hr (Nat.succ_ne_zero q)
      have hfactor : 0 < (r - s) * (A * r - B * s) :=
        mul_pos_of_neg_of_neg (sub_neg.mpr hrslt) (sub_neg.mpr hpow)
      have hid : (r - s) * (A * r - B * s) =
          A * r ^ 2 + B * s ^ 2 - (A + B) * (r * s) := by ring
      nlinarith [hlower]
    · have hpow : B * s < A * r := by
        dsimp [A, B]
        simpa [pow_succ] using pow_lt_pow_left₀ hrslt hs (Nat.succ_ne_zero q)
      have hfactor : 0 < (r - s) * (A * r - B * s) :=
        mul_pos (sub_pos.mpr hrslt) (sub_pos.mpr hpow)
      have hid : (r - s) * (A * r - B * s) =
          A * r ^ 2 + B * s ^ 2 - (A + B) * (r * s) := by ring
      nlinarith [hlower]

theorem centeredRadialPower_strictMonotone (q : ℕ) (center : E)
    {u v : E} (huv : u ≠ v) :
    0 < inner ℝ
      (radialPower q (u - center) - radialPower q (v - center)) (u - v) := by
  have hne : u - center ≠ v - center := by
    intro h
    apply huv
    exact sub_left_injective h
  simpa [sub_sub_sub_cancel_right] using radialPower_strictMonotone q hne

/-- A derivative remainder bound turns monotonicity of `G` into the exact
hypomonotonicity estimate needed for the Taylor model. -/
theorem inner_sub_lower_of_fderiv_close
    [FiniteDimensional ℝ E] (G T : E → E) (u v : E) (C : ℝ)
    (hmono : 0 ≤ inner ℝ (G u - G v) (u - v))
    (hdiffG : ∀ z ∈ segment ℝ u v, DifferentiableAt ℝ G z)
    (hdiffT : ∀ z ∈ segment ℝ u v, DifferentiableAt ℝ T z)
    (hclose : ∀ z ∈ segment ℝ u v,
      ‖fderiv ℝ G z - fderiv ℝ T z‖ ≤ C) :
    -C * ‖u - v‖ ^ 2 ≤ inner ℝ (T u - T v) (u - v) := by
  let H : E → E := fun z ↦ T z - G z
  have hdiffH : ∀ z ∈ segment ℝ u v, DifferentiableAt ℝ H z := by
    intro z hz
    exact (hdiffT z hz).sub (hdiffG z hz)
  have hboundH : ∀ z ∈ segment ℝ u v, ‖fderiv ℝ H z‖ ≤ C := by
    intro z hz
    rw [show fderiv ℝ H z = fderiv ℝ T z - fderiv ℝ G z by
      exact fderiv_sub (hdiffT z hz) (hdiffG z hz)]
    rw [show fderiv ℝ T z - fderiv ℝ G z =
      -(fderiv ℝ G z - fderiv ℝ T z) by abel, norm_neg]
    exact hclose z hz
  have hH := (convex_segment u v).norm_image_sub_le_of_norm_fderiv_le
    hdiffH hboundH (right_mem_segment ℝ u v) (left_mem_segment ℝ u v)
  have hinner : -(‖H u - H v‖ * ‖u - v‖) ≤ inner ℝ (H u - H v) (u - v) := by
    have := real_inner_le_norm (-(H u - H v)) (u - v)
    rw [inner_neg_left, norm_neg] at this
    linarith
  have hC0 : 0 ≤ C := by
    have hzero := hclose u (left_mem_segment ℝ u v)
    exact le_trans (norm_nonneg _) hzero
  have hnorm : ‖H u - H v‖ * ‖u - v‖ ≤ C * ‖u - v‖ ^ 2 := by
    calc
      ‖H u - H v‖ * ‖u - v‖ ≤
          (C * ‖u - v‖) * ‖u - v‖ :=
        mul_le_mul_of_nonneg_right (by simpa [norm_sub_rev] using hH) (norm_nonneg _)
      _ = C * ‖u - v‖ ^ 2 := by ring
  have hdecomp : T u - T v = (G u - G v) + (H u - H v) := by
    dsimp [H]
    module
  rw [hdecomp, inner_add_left]
  nlinarith

/-- The coefficient `2*C` used by the paper upgrades the Taylor
hypomonotonicity bound to strict monotonicity. -/
def stabilizedModel (q : ℕ) (C : ℝ) (center : E) (T : E → E) (z : E) : E :=
  T z + (2 * C) • radialPower q (z - center)

theorem stabilizedModel_strictMonotone_of_taylor_lower
    (q : ℕ) (C : ℝ) (hC : 0 < C) (center : E) (T : E → E)
    {u v : E} (huv : u ≠ v)
    (hT : -C * max (‖u - center‖ ^ q) (‖v - center‖ ^ q) * ‖u - v‖ ^ 2 ≤
      inner ℝ (T u - T v) (u - v)) :
    0 < inner ℝ (stabilizedModel q C center T u -
      stabilizedModel q C center T v) (u - v) := by
  let a := u - center
  let b := v - center
  have hab : a ≠ b := by
    intro h
    apply huv
    exact sub_left_injective h
  have hdpos : 0 < ‖u - v‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr huv))
  have hrad := radialPower_pair_lower q a b
  have habdiff : a - b = u - v := by
    dsimp [a, b]
    abel
  rw [habdiff] at hrad
  have hexpand : inner ℝ (stabilizedModel q C center T u -
      stabilizedModel q C center T v) (u - v) =
      inner ℝ (T u - T v) (u - v) +
        (2 * C) * inner ℝ (radialPower q a - radialPower q b) (a - b) := by
    dsimp [stabilizedModel, a, b]
    rw [show (T u + (2 * C) • radialPower q (u - center)) -
        (T v + (2 * C) • radialPower q (v - center)) =
      (T u - T v) + (2 * C) •
        (radialPower q (u - center) - radialPower q (v - center)) by module,
      inner_add_left, inner_smul_left, conj_trivial]
    rw [show (u - center) - (v - center) = u - v by abel]
  rw [habdiff] at hexpand
  rw [hexpand]
  rcases le_total ‖a‖ ‖b‖ with habnorm | hbanorm
  · have hp : ‖a‖ ^ q ≤ ‖b‖ ^ q :=
      pow_le_pow_left₀ (norm_nonneg a) habnorm q
    rw [max_eq_right hp] at hT
    by_cases ha0 : a = 0
    · have hb0 : b ≠ 0 := by
        intro hb
        exact hab (ha0.trans hb.symm)
      have hbpos : 0 < ‖b‖ ^ q := pow_pos (norm_pos_iff.mpr hb0) q
      have hnormdiff : ‖b‖ ^ 2 = ‖u - v‖ ^ 2 := by
        rw [← habdiff, ha0, zero_sub, norm_neg]
      have hradexact : inner ℝ (radialPower q a - radialPower q b)
          (u - v) = ‖b‖ ^ q * ‖u - v‖ ^ 2 := by
        rw [← habdiff, ha0]
        simp only [radialPower, smul_zero, zero_sub, inner_neg_left,
          inner_neg_right, neg_neg]
        rw [inner_smul_left, conj_trivial]
        rw [real_inner_self_eq_norm_sq, norm_neg, hnormdiff]
      have hprodpos : 0 < C * ‖b‖ ^ q * ‖u - v‖ ^ 2 := by positivity
      rw [hradexact]
      nlinarith
    · have hapos : 0 < ‖a‖ ^ q := pow_pos (norm_pos_iff.mpr ha0) q
      have hrad' : C * (‖a‖ ^ q + ‖b‖ ^ q) * ‖u - v‖ ^ 2 ≤
          (2 * C) * inner ℝ (radialPower q a - radialPower q b) (u - v) := by
        have hh := mul_le_mul_of_nonneg_left hrad (show 0 ≤ 2 * C by positivity)
        nlinarith [hh]
      have hprodpos : 0 < C * ‖a‖ ^ q * ‖u - v‖ ^ 2 := by positivity
      nlinarith
  · have hp : ‖b‖ ^ q ≤ ‖a‖ ^ q :=
      pow_le_pow_left₀ (norm_nonneg b) hbanorm q
    rw [max_eq_left hp] at hT
    by_cases hb0 : b = 0
    · have ha0 : a ≠ 0 := by
        intro ha
        exact hab (ha.trans hb0.symm)
      have hapos : 0 < ‖a‖ ^ q := pow_pos (norm_pos_iff.mpr ha0) q
      have hnormdiff : ‖a‖ ^ 2 = ‖u - v‖ ^ 2 := by
        rw [← habdiff, hb0, sub_zero]
      have hradexact : inner ℝ (radialPower q a - radialPower q b)
          (u - v) = ‖a‖ ^ q * ‖u - v‖ ^ 2 := by
        rw [← habdiff, hb0]
        simp only [radialPower, smul_zero, sub_zero]
        rw [inner_smul_left, conj_trivial]
        rw [real_inner_self_eq_norm_sq, hnormdiff]
      have hprodpos : 0 < C * ‖a‖ ^ q * ‖u - v‖ ^ 2 := by positivity
      rw [hradexact]
      nlinarith
    · have hbpos : 0 < ‖b‖ ^ q := pow_pos (norm_pos_iff.mpr hb0) q
      have hrad' : C * (‖a‖ ^ q + ‖b‖ ^ q) * ‖u - v‖ ^ 2 ≤
          (2 * C) * inner ℝ (radialPower q a - radialPower q b) (u - v) := by
        have hh := mul_le_mul_of_nonneg_left hrad (show 0 ≤ 2 * C by positivity)
        nlinarith [hh]
      have hprodpos : 0 < C * ‖b‖ ^ q * ‖u - v‖ ^ 2 := by positivity
      nlinarith

end VIReference.Pilot
