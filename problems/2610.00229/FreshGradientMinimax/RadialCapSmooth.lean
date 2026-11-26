import FreshGradientMinimax.RadialCap

/-! A direct global gradient estimate for the actual radial cap. The proof
crosses both joins without assuming a classical Hessian exists there. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radialWallGradient_lipschitz {β : ℝ} (hβ : 0 ≤ β) (x y : E) :
    ‖(8 * β) • x - (8 * β) • y‖ ≤ 8 * β * ‖x - y‖ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 8 * β)]

theorem radialGap_hasFDerivAt {Q : E → ℝ} {G : E → E} {β R : ℝ}
    (hQ : ∀ x, HasFDerivAt Q (innerSL ℝ (G x)) x) (x : E) :
    HasFDerivAt (fun y => radialWall β R y - Q y)
      (innerSL ℝ ((8 * β) • x - G x)) x := by
  simpa only [map_sub] using (radialWall_hasFDerivAt β R x).sub (hQ x)

theorem radialGapGradient_lipschitz {G : E → E} {β : ℝ} (hβ : 0 ≤ β)
    (hG : ∀ x y, ‖G x - G y‖ ≤ 4 * β * ‖x - y‖) (x y : E) :
    ‖((8 * β) • x - G x) - ((8 * β) • y - G y)‖ ≤ 12 * β * ‖x - y‖ := by
  rw [show ((8 * β) • x - G x) - ((8 * β) • y - G y) =
    ((8 * β) • x - (8 * β) • y) - (G x - G y) by abel]
  exact (norm_sub_le _ _).trans (by
    have h₁ := radialWallGradient_lipschitz hβ x y
    have h₂ := hG x y
    linarith)

theorem radialGapGradient_norm {G : E → E} {β : ℝ} (hβ : 0 ≤ β)
    (hG : ∀ x, ‖G x‖ ≤ 4 * β * ‖x‖) (x : E) :
    ‖(8 * β) • x - G x‖ ≤ 12 * β * ‖x‖ := by
  have h := norm_sub_le ((8 * β) • x) (G x)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 8 * β)] at h
  have hg := hG x
  linarith

theorem radialGap_local_variation {Q : E → ℝ} {G : E → E} {β R : ℝ}
    (hβ : 0 ≤ β)
    (hQ : ∀ x, HasFDerivAt Q (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ 4 * β * ‖x - y‖)
    (hGn : ∀ x, ‖G x‖ ≤ 4 * β * ‖x‖)
    {x y : E} (hx : ‖x‖ ≤ 2 * R) (hxy : ‖x - y‖ ≤ R) :
    |(radialWall β R x - Q x) - (radialWall β R y - Q y)| ≤
      30 * β * R * ‖x - y‖ := by
  have ht := smooth_taylor_remainder (radialGap_hasFDerivAt (R := R) hQ)
    (radialGapGradient_lipschitz hβ hG) x (y - x)
  rw [add_sub_cancel, norm_sub_rev] at ht
  have hi := abs_real_inner_le_norm ((8 * β) • x - G x) (y - x)
  rw [norm_sub_rev y x] at hi
  have hn := radialGapGradient_norm hβ hGn x
  have hnr : ‖(8 * β) • x - G x‖ ≤ 24 * β * R :=
    hn.trans (by nlinarith [mul_le_mul_of_nonneg_left hx (show 0 ≤ 12 * β by positivity)])
  have hib := hi.trans (mul_le_mul_of_nonneg_right hnr (norm_nonneg _))
  have hsq : 6 * β * ‖x - y‖ ^ 2 ≤ 6 * β * R * ‖x - y‖ := by
    have h := mul_le_mul_of_nonneg_right hxy (show 0 ≤ 6 * β * ‖x - y‖ by positivity)
    nlinarith only [h]
  have ha := abs_add ((radialWall β R y - Q y) - (radialWall β R x - Q x) -
    ⟪(8 * β) • x - G x, y - x⟫_ℝ) ⟪(8 * β) • x - G x, y - x⟫_ℝ
  rw [sub_add_cancel] at ha
  rw [abs_sub_comm]
  nlinarith only [ht, hib, hsq, ha]

theorem radialCapWeight_local_variation {Q : E → ℝ} {G : E → E} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (hQ : ∀ x, HasFDerivAt Q (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ 4 * β * ‖x - y‖)
    (hGn : ∀ x, ‖G x‖ ≤ 4 * β * ‖x‖)
    {x y : E} (hx : ‖x‖ ≤ 2 * R) (hxy : ‖x - y‖ ≤ R) :
    (β * R ^ 2) * |radialCapWeight Q β R x - radialCapWeight Q β R y| ≤
      30 * β * R * ‖x - y‖ := by
  have hη : 0 < β * R ^ 2 := by positivity
  have h := (smoothRampSlope_lipschitz hη).dist_le_mul
    (radialWall β R x - Q x) (radialWall β R y - Q y)
  simp only [Real.dist_eq, NNReal.coe_mk] at h
  calc
    _ ≤ (β * R ^ 2) * ((1 / (β * R ^ 2)) *
        |(radialWall β R x - Q x) - (radialWall β R y - Q y)|) :=
      mul_le_mul_of_nonneg_left h hη.le
    _ = |(radialWall β R x - Q x) - (radialWall β R y - Q y)| := by field_simp
    _ ≤ _ := radialGap_local_variation hβ.le hQ hG hGn hx hxy

theorem radialCapGradient_difference {Q : E → ℝ} {G : E → E} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (hG : ∀ x y, ‖G x - G y‖ ≤ 4 * β * ‖x - y‖) (x y : E) :
    ‖radialCapGradient Q G β R x - radialCapGradient Q G β R y‖ ≤
      8 * β * ‖x - y‖ + |radialCapWeight Q β R x - radialCapWeight Q β R y| *
        ‖(8 * β) • x - G x‖ := by
  let b := radialCapWeight Q β R
  have hy := radialCapWeight_bounds (Q := Q) hβ hR y
  have he : radialCapGradient Q G β R x - radialCapGradient Q G β R y =
      ((1 - b y) • (G x - G y) + b y • ((8 * β) • x - (8 * β) • y)) +
        (b x - b y) • ((8 * β) • x - G x) := by
    dsimp [radialCapGradient, b]; module
  rw [he]
  have h₁ := norm_add_le ((1 - b y) • (G x - G y))
    (b y • ((8 * β) • x - (8 * β) • y))
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ 1 - b y by dsimp [b]; linarith [hy.2]),
    abs_of_nonneg (show 0 ≤ b y from hy.1)] at h₁
  have h₂ := mul_le_mul_of_nonneg_left (hG x y) (show 0 ≤ 1 - b y by dsimp [b]; linarith [hy.2])
  have h₃ := mul_le_mul_of_nonneg_left (radialWallGradient_lipschitz hβ.le x y) hy.1
  have hb : ‖(1 - b y) • (G x - G y) + b y • ((8 * β) • x - (8 * β) • y)‖ ≤
      8 * β * ‖x - y‖ := by
    have h₅ : b y * (4 * β * ‖x - y‖) ≤ 4 * β * ‖x - y‖ :=
      mul_le_of_le_one_left (by positivity) hy.2
    nlinarith only [h₁, h₂, h₃, h₅]
  calc
    _ ≤ ‖(1 - b y) • (G x - G y) + b y • ((8 * β) • x - (8 * β) • y)‖ +
        ‖(b x - b y) • ((8 * β) • x - G x)‖ := norm_add_le _ _
    _ ≤ _ := by
      simpa only [norm_smul, Real.norm_eq_abs] using
        (add_le_add_right hb (|b x - b y| * ‖(8 * β) • x - G x‖))

theorem radialCapGradient_bounded_difference {Q : E → ℝ} {G : E → E} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (hQ : ∀ x, HasFDerivAt Q (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ 4 * β * ‖x - y‖)
    (hGn : ∀ x, ‖G x‖ ≤ 4 * β * ‖x‖)
    {x y : E} (hx : ‖x‖ ≤ 2 * R) :
    ‖radialCapGradient Q G β R x - radialCapGradient Q G β R y‖ ≤
      1000 * β * ‖x - y‖ := by
  let w := |radialCapWeight Q β R x - radialCapWeight Q β R y|
  have hw0 : 0 ≤ w := abs_nonneg _
  have hn : ‖(8 * β) • x - G x‖ ≤ 24 * β * R :=
    (radialGapGradient_norm hβ.le hGn x).trans (by
      nlinarith [mul_le_mul_of_nonneg_left hx (show 0 ≤ 12 * β by positivity)])
  have he := radialCapGradient_difference (Q := Q) hβ hR hG x y
  have hp := mul_le_mul_of_nonneg_left hn hw0
  by_cases hxy : ‖x - y‖ ≤ R
  · have hw := radialCapWeight_local_variation hβ hR hQ hG hGn hx hxy
    have hc : (β * R) * (R * w) ≤ (β * R) * (30 * ‖x - y‖) := by
      dsimp only [w]; nlinarith only [hw]
    have hwr := (mul_le_mul_left (mul_pos hβ hR)).mp hc
    have hmul := mul_le_mul_of_nonneg_left hwr (show 0 ≤ 24 * β by positivity)
    change ‖radialCapGradient Q G β R x - radialCapGradient Q G β R y‖ ≤
      8 * β * ‖x - y‖ + w * ‖(8 * β) • x - G x‖ at he
    nlinarith only [he, hp, hmul, mul_nonneg hβ.le (norm_nonneg (x - y))]
  · have hb₁ := radialCapWeight_bounds (Q := Q) hβ hR x
    have hb₂ := radialCapWeight_bounds (Q := Q) hβ hR y
    have hw1 : w ≤ 1 := abs_le.mpr ⟨by linarith [hb₁.1, hb₂.2], by linarith [hb₁.2, hb₂.1]⟩
    have hmul := mul_le_mul_of_nonneg_right hw1 (show 0 ≤ 24 * β * R by positivity)
    have hfar := mul_le_mul_of_nonneg_left (le_of_not_ge hxy) (show 0 ≤ 24 * β by positivity)
    change ‖radialCapGradient Q G β R x - radialCapGradient Q G β R y‖ ≤
      8 * β * ‖x - y‖ + w * ‖(8 * β) • x - G x‖ at he
    nlinarith only [he, hp, hmul, hfar, mul_nonneg hβ.le (norm_nonneg (x - y))]

theorem radialCapGradient_lipschitz {Q : E → ℝ} {G : E → E} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    (hQ : ∀ x, HasFDerivAt Q (innerSL ℝ (G x)) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ 4 * β * ‖x - y‖)
    (hGn : ∀ x, ‖G x‖ ≤ 4 * β * ‖x‖)
    (hQu : ∀ x, Q x ≤ 2 * β * ‖x‖ ^ 2) :
    LipschitzWith ⟨1000 * β, by positivity⟩ (radialCapGradient Q G β R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_mk]
  by_cases hx : 2 * R ≤ ‖x‖
  · by_cases hy : 2 * R ≤ ‖y‖
    · rw [radialCapGradient_outside hβ hR hQu hx, radialCapGradient_outside hβ hR hQu hy]
      exact (radialWallGradient_lipschitz hβ.le x y).trans (by
        nlinarith only [mul_nonneg hβ.le (norm_nonneg (x - y))])
    · simpa only [norm_sub_rev] using
        radialCapGradient_bounded_difference hβ hR hQ hG hGn (le_of_not_ge hy)
          (y := x)
  · exact radialCapGradient_bounded_difference hβ hR hQ hG hGn (le_of_not_ge hx)

end FreshGradientMinimax
