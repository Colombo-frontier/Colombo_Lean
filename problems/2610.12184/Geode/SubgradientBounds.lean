import Geode.ContactRealization

/-! The norm bound on every legal ordinary subgradient of a globally
Lipschitz function, proved using an actual geodesic query in its direction. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem subgradient_norm_le {f : Point E → ℝ} {x : Point E} {g : Ambient E}
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b)
    (hg : IsSubgradient f x g) : tangentNorm g ≤ L := by
  by_cases hg0 : g = 0
  · simpa [hg0, tangentNorm] using hL
  let r := tangentNorm g
  have hgg : 0 < form E g g := tangent_pos x hg.1 hg0
  have hr : 0 < r := Real.sqrt_pos.mpr hgg
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hr2 : r ^ 2 = form E g g := Real.sq_sqrt hgg.le
  let q := r⁻¹ • g
  have hq : form E x.val q = 0 := by simp [q, hg.1]
  have hqu : form E q q = 1 := by
    simp only [q, form_smul_left, form_smul_right]
    rw [← hr2]
    field_simp
    ring
  let y := unitGeodesic x q hq hqu 1
  have hd : dist x y = 1 := dist_unitGeodesic_pos x q hq hqu (by norm_num)
  have hdir : direction x y = q := direction_unitGeodesic_pos x q hq hqu (by norm_num)
  have hlog : logMap x y = q := by rw [logMap, hd, hdir, one_smul]
  have hpair : form E g q = r := by
    simp only [q, form_smul_right]
    rw [← hr2]
    field_simp
    ring
  have hs := hg.2 y
  rw [hlog, hpair] at hs
  have hl := hlip y x
  rw [dist_comm y x, hd, mul_one] at hl
  have hdiff := (le_abs_self (f y - f x)).trans hl
  change r ≤ L
  linarith

theorem subgradient_norm_sq_le {f : Point E → ℝ} {x : Point E} {g : Ambient E}
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ a b, |f a - f b| ≤ L * dist a b)
    (hg : IsSubgradient f x g) : form E g g ≤ L ^ 2 := by
  have hb := subgradient_norm_le hL hlip hg
  have hn := tangent_nonneg x hg.1
  have hs := Real.sq_sqrt hn
  have hs0 := Real.sqrt_nonneg (form E g g)
  unfold tangentNorm at hb
  nlinarith

end Geode.Lorentz
