import Bilevel.RadialCompression

/-! The two-region end-game estimate for the actual wrapped-gradient formula. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem wrapper_inner (ν R : ℝ) (u h w : E) :
    ⟪wrappedGradient ν R u h, w⟫ = scale R u * ⟪h, w⟫ +
      (ν - scale R u ^ 2 / R ^ 2 * ⟪u, h⟫) * ⟪compress R u, w⟫ := by
  simp only [wrappedGradient, compress, inner_add_left, real_inner_smul_left]
  ring

theorem interior_coefficient_bound (ν R G : ℝ) (hν : 0 ≤ ν) (hR : 0 < R) (hG : 0 ≤ G)
    (u h : E) (hu : ‖u‖ ≤ R) (hh : ‖h‖ ≤ G) :
    |ν - scale R u ^ 2 / R ^ 2 * ⟪u, h⟫| ≤ ν + G / R := by
  have hi : |⟪u, h⟫| ≤ R * G :=
    (abs_real_inner_le_norm u h).trans (mul_le_mul hu hh (norm_nonneg h) hR.le)
  have ha : scale R u ^ 2 ≤ 1 := by
    have hp := scale_pos R u
    have hl := scale_le_one R u
    nlinarith
  have hc : |scale R u ^ 2 / R ^ 2 * ⟪u, h⟫| ≤ G / R := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc
      scale R u ^ 2 / R ^ 2 * |⟪u, h⟫| ≤ scale R u ^ 2 / R ^ 2 * (R * G) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = scale R u ^ 2 * (G / R) := by field_simp; ring
      _ ≤ 1 * (G / R) := mul_le_mul_of_nonneg_right ha (div_nonneg hG hR.le)
      _ = G / R := one_mul _
  exact (abs_sub ν _).trans (by rw [abs_of_nonneg hν]; linarith)

theorem interior_endgame (ν R G β s : ℝ)
    (hν : 0 ≤ ν) (hR : 0 < R) (hG : 0 ≤ G) (hs : 0 < s)
    (hmargin : (ν + G / R) * β ≤ s / 6)
    (u h w : E) (hu : ‖u‖ ≤ R) (hh : ‖h‖ ≤ G) (hw : ‖w‖ = 1)
    (hfront : ⟪h, w⟫ ≤ -s) (hchild : |⟪compress R u, w⟫| ≤ β) :
    s / 2 ≤ ‖wrappedGradient ν R u h‖ := by
  have ha := scale_interior_lower R hR u hu
  have hcoef := interior_coefficient_bound ν R G hν hR hG u h hu hh
  have herr : (ν - scale R u ^ 2 / R ^ 2 * ⟪u, h⟫) * ⟪compress R u, w⟫ ≤ s / 6 := by
    calc
      _ ≤ |(ν - scale R u ^ 2 / R ^ 2 * ⟪u, h⟫) * ⟪compress R u, w⟫| := le_abs_self _
      _ ≤ (ν + G / R) * β := by
        rw [abs_mul]
        exact mul_le_mul hcoef hchild (abs_nonneg _) (by positivity)
      _ ≤ _ := hmargin
  have hlead := mul_le_mul_of_nonneg_left hfront (scale_pos R u).le
  have hwg : ⟪wrappedGradient ν R u h, w⟫ ≤ -s / 2 := by
    rw [wrapper_inner]
    nlinarith
  have hb := abs_real_inner_le_norm (wrappedGradient ν R u h) w
  rw [hw, mul_one] at hb
  have hab := neg_le_abs ⟪wrappedGradient ν R u h, w⟫
  linarith

def radialUnit (u : E) : E := ‖u‖⁻¹ • u

theorem radialUnit_norm (u : E) (hu : 0 < ‖u‖) : ‖radialUnit u‖ = 1 := by
  simp [radialUnit, norm_smul, Real.norm_eq_abs, abs_of_pos hu, hu.ne']

theorem wrapper_radial_inner (ν R : ℝ) (hR : 0 < R) (u h : E) (hu : 0 < ‖u‖) :
    ⟪wrappedGradient ν R u h, radialUnit u⟫ =
      scale R u ^ 3 * ⟪h, radialUnit u⟫ + ν * scale R u * ‖u‖ := by
  have hs := scale_radius_identity R hR u
  have hi : ⟪u, h⟫ = ⟪h, u⟫ := real_inner_comm _ _
  simp only [wrappedGradient, radialUnit, inner_add_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hi]
  field_simp [hR.ne', hu.ne']
  have hm := congrArg (fun z : ℝ => z * scale R u * ⟪h, u⟫ * ‖u‖ ^ 2) hs
  linear_combination -hm

theorem exterior_endgame (ν R G s : ℝ)
    (hν : 0 ≤ ν) (hR : 0 < R) (hG : 0 ≤ G)
    (hmargin : s / 2 ≤ 2 * ν * R / 3 - G)
    (u h : E) (hu : R ≤ ‖u‖) (hh : ‖h‖ ≤ G) :
    s / 2 ≤ ‖wrappedGradient ν R u h‖ := by
  have hun : 0 < ‖u‖ := hR.trans_le hu
  have hw := radialUnit_norm u hun
  have hi : -G ≤ ⟪h, radialUnit u⟫ := by
    have hb := abs_real_inner_le_norm h (radialUnit u)
    rw [hw, mul_one] at hb
    have hneg := neg_le_abs ⟪h, radialUnit u⟫
    linarith
  have ha3 : 0 ≤ scale R u ^ 3 := pow_nonneg (scale_pos R u).le _
  have ha31 : scale R u ^ 3 ≤ 1 := pow_le_one₀ (scale_pos R u).le (scale_le_one R u)
  have hchain := mul_le_mul_of_nonneg_left hi ha3
  have hprod := mul_le_mul_of_nonneg_right ha31 hG
  have hrad := mul_le_mul_of_nonneg_left (compressed_radius_exterior_lower R hR u hu) hν
  have hwg : s / 2 ≤ ⟪wrappedGradient ν R u h, radialUnit u⟫ := by
    rw [wrapper_radial_inner ν R hR u h hun]
    nlinarith
  have hb := abs_real_inner_le_norm (wrappedGradient ν R u h) (radialUnit u)
  rw [hw, mul_one] at hb
  exact hwg.trans ((le_abs_self _).trans hb)

theorem wrapper_endgame (ν R G β s : ℝ)
    (hν : 0 ≤ ν) (hR : 0 < R) (hG : 0 ≤ G) (hs : 0 < s)
    (hinner : (ν + G / R) * β ≤ s / 6)
    (houter : s / 2 ≤ 2 * ν * R / 3 - G)
    (u h : E) (hh : ‖h‖ ≤ G)
    (hfront : ‖u‖ ≤ R → ∃ w : E, ‖w‖ = 1 ∧ ⟪h, w⟫ ≤ -s ∧ |⟪compress R u, w⟫| ≤ β) :
    s / 2 ≤ ‖wrappedGradient ν R u h‖ := by
  rcases le_total ‖u‖ R with hu | hu
  · obtain ⟨w, hw, hg, hc⟩ := hfront hu
    exact interior_endgame ν R G β s hν hR hG hs hinner u h w hu hh hw hg hc
  · exact exterior_endgame ν R G s hν hR hG houter u h hu hh

end Bilevel.RadialWrapper
