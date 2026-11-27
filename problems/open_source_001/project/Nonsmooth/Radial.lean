import Nonsmooth.Scales

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- D(s) is represented by its attained maximum, already justified by radial_maximizer. -/
def radial (μ R s : ℝ) : ℝ := energy s μ R

theorem radial_monotone {μ R : ℝ} (hμ : 0 < μ) (hR : 0 ≤ R) :
    MonotoneOn (radial μ R) (Set.Ici 0) := by
  intro s hs t ht hst
  have hr := radius_nonneg hs hμ hR
  have hm := radial_maximizer ht hμ hR hr (radius_le_R s μ R)
  have hp := mul_le_mul_of_nonneg_right hst hr
  dsimp [radial, energy] at *
  linarith

theorem radial_convex {μ R : ℝ} (hμ : 0 < μ) (hR : 0 ≤ R) :
    ConvexOn ℝ (Set.Ici 0) (radial μ R) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro s hs t ht a b ha hb hab
  have hs' : 0 ≤ s := hs
  have ht' : 0 ≤ t := ht
  let r := radius (a * s + b * t) μ R
  have hr : 0 ≤ r := radius_nonneg (by positivity) hμ hR
  have h₁ := mul_le_mul_of_nonneg_left
    (radial_maximizer hs' hμ hR hr (radius_le_R _ μ R)) ha
  have h₂ := mul_le_mul_of_nonneg_left
    (radial_maximizer ht' hμ hR hr (radius_le_R _ μ R)) hb
  change (a * s + b * t) * r - μ / 2 * r ^ 2 ≤ a * energy s μ R + b * energy t μ R
  linear_combination h₁ + h₂ + (μ / 2 * r ^ 2) * hab

theorem radial_increment {μ R s : ℝ} (hμ : 0 < μ) (hR : 0 ≤ R) (hs : 0 ≤ s) :
    175 / 512 * min (s * R) (s ^ 2 / μ) ≤ radial μ R s - radial μ R (9 * s / 16) := by
  unfold radial
  by_cases hlo : s ≤ μ * R
  · have hclo : 9 * s / 16 ≤ μ * R := by linarith
    have hmin : s ^ 2 / μ ≤ s * R := by
      rw [div_le_iff₀ hμ]
      nlinarith [mul_le_mul_of_nonneg_left hlo hs]
    rw [energy_interior hμ hlo, energy_interior hμ hclo, min_eq_right hmin]
    apply le_of_eq
    ring
  · have hsR : μ * R ≤ s := le_of_lt (lt_of_not_ge hlo)
    have hmin : s * R ≤ s ^ 2 / μ := by
      rw [le_div_iff₀ hμ]
      nlinarith [mul_le_mul_of_nonneg_left hsR hs]
    rw [energy_boundary hμ hsR, min_eq_left hmin]
    by_cases hhi : μ * R ≤ 9 * s / 16
    · rw [energy_boundary hμ hhi]
      nlinarith [mul_nonneg hs hR]
    · have hc : 9 * s / 16 ≤ μ * R := le_of_lt (lt_of_not_ge hhi)
      rw [energy_interior hμ hc]
      have hid : s * R - μ / 2 * R ^ 2 - (9 * s / 16) ^ 2 / (2 * μ) =
          (2 * μ * s * R - μ ^ 2 * R ^ 2 - (9 * s / 16) ^ 2) / (2 * μ) := by
        field_simp
        <;> ring
      rw [hid, le_div_iff₀ (by positivity : 0 < 2 * μ)]
      have hp := mul_nonneg (show 0 ≤ s - μ * R by linarith)
        (show 0 ≤ 256 * μ * R - 81 * s by nlinarith)
      nlinarith only [hp]

theorem convex_increment_mono {F : ℝ → ℝ} (hF : ConvexOn ℝ (Set.Ici 0) F)
    {q x y : ℝ} (hq : 0 ≤ q) (hx : q ≤ x) (hxy : x ≤ y) :
    F x - F (x - q) ≤ F y - F (y - q) := by
  rcases eq_or_lt_of_le hq with hq | hq
  · subst q
    simp
  · let D := y - x + q
    have hD : 0 < D := by dsimp [D]; linarith
    let a := q / D
    let b := (y - x) / D
    have ha : 0 ≤ a := div_nonneg hq.le hD.le
    have hb : 0 ≤ b := div_nonneg (by linarith) hD.le
    have hab : a + b = 1 := by dsimp [a, b]; field_simp [hD.ne']; dsimp [D]; ring
    have hi : b * (x - q) + a * y = x := by
      dsimp [a, b]
      field_simp [hD.ne']
      dsimp [D]
      ring
    have hj : a * (x - q) + b * y = y - q := by
      dsimp [a, b]
      field_simp [hD.ne']
      dsimp [D]
      ring
    have hxI : x - q ∈ Set.Ici 0 := by change 0 ≤ x - q; linarith
    have hyI : y ∈ Set.Ici 0 := by change 0 ≤ y; linarith
    have h₁ := hF.2 hxI hyI hb ha (by linarith)
    have h₂ := hF.2 hxI hyI ha hb hab
    simp only [smul_eq_mul] at h₁ h₂
    rw [hi] at h₁
    rw [hj] at h₂
    linear_combination h₁ + h₂ + (F (x - q) + F y) * hab

theorem radial_fixed_increment_mono {μ R q x y : ℝ} (hμ : 0 < μ) (hR : 0 ≤ R)
    (hq : 0 ≤ q) (hx : q ≤ x) (hxy : x ≤ y) :
    radial μ R x - radial μ R (x - q) ≤ radial μ R y - radial μ R (y - q) :=
  convex_increment_mono (radial_convex hμ hR) hq hx hxy

end
end Nonsmooth
