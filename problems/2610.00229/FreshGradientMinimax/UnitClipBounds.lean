import FreshGradientMinimax.UnitClip

/-! Global and local estimates for the explicit odd clip. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem positiveClip_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ positiveClip t ∧ positiveClip t ≤ 3 / 2 := by
  unfold positiveClip scalarJoin
  split_ifs with h1 h2
  · simp only [id_eq]
    exact ⟨ht, by linarith⟩
  · have h := clipTransition_bounds (show 0 ≤ t - 1 by linarith)
      (show t - 1 ≤ 1 by linarith)
    exact ⟨by linarith [h.1], h.2⟩
  · norm_num

theorem positiveClipSlope_bounds (t : ℝ) :
    0 ≤ positiveClipSlope t ∧ positiveClipSlope t ≤ 1 := by
  unfold positiveClipSlope scalarJoin
  split_ifs with h1 h2
  · norm_num
  · exact clipTransitionSlope_bounds (by linarith) (by linarith)
  · norm_num

theorem positiveClipCurve_bound (t : ℝ) : |positiveClipCurve t| ≤ 3 / 2 := by
  unfold positiveClipCurve scalarJoin
  split_ifs with h1 h2
  · norm_num
  · exact clipTransitionCurve_bound (by linarith) (by linarith)
  · norm_num

theorem unitClip_of_nonneg {t : ℝ} (ht : 0 ≤ t) : unitClip t = positiveClip t := by
  rcases ht.eq_or_lt with h | h
  · subst t; norm_num [unitClip, positiveClip, scalarJoin]
  · simp [unitClip, scalarJoin, not_le.mpr h]

theorem unitClip_odd (t : ℝ) : unitClip (-t) = -unitClip t := by
  rcases le_total t 0 with ht | ht
  · rw [unitClip_of_nonneg (neg_nonneg.mpr ht)]
    simp only [unitClip, scalarJoin, if_pos ht, neg_neg]
  · rw [unitClip_of_nonneg ht]
    simp only [unitClip, scalarJoin, if_pos (neg_nonpos.mpr ht), neg_neg]

theorem unitClip_identity {t : ℝ} (ht : |t| ≤ 1) : unitClip t = t := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ht
  unfold unitClip scalarJoin positiveClip
  split_ifs with h
  · simp only [scalarJoin, if_pos (show -t ≤ 1 by linarith), id_eq, neg_neg]
  · simp only [scalarJoin, if_pos hhi, id_eq]

theorem unitClipSlope_identity {t : ℝ} (ht : |t| ≤ 1) : unitClipSlope t = 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ht
  unfold unitClipSlope scalarJoin positiveClipSlope
  split_ifs with h
  · simp only [scalarJoin, if_pos (show -t ≤ 1 by linarith)]
  · simp only [scalarJoin, if_pos hhi]

theorem unitClipCurve_identity {t : ℝ} (ht : |t| ≤ 1) : unitClipCurve t = 0 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ht
  unfold unitClipCurve scalarJoin positiveClipCurve
  split_ifs with h
  · simp only [scalarJoin, if_pos (show -t ≤ 1 by linarith), neg_zero]
  · simp only [scalarJoin, if_pos hhi]

theorem unitClip_bound (t : ℝ) : |unitClip t| ≤ 3 / 2 := by
  rcases le_total 0 t with ht | ht
  · rw [unitClip_of_nonneg ht, abs_of_nonneg (positiveClip_bounds ht).1]
    exact (positiveClip_bounds ht).2
  · rw [← abs_neg (unitClip t), ← unitClip_odd,
      unitClip_of_nonneg (neg_nonneg.mpr ht),
      abs_of_nonneg (positiveClip_bounds (neg_nonneg.mpr ht)).1]
    exact (positiveClip_bounds (neg_nonneg.mpr ht)).2

theorem unitClipSlope_bounds (t : ℝ) : 0 ≤ unitClipSlope t ∧ unitClipSlope t ≤ 1 := by
  unfold unitClipSlope scalarJoin
  split_ifs <;> exact positiveClipSlope_bounds _

theorem unitClipCurve_bound (t : ℝ) : |unitClipCurve t| ≤ 3 / 2 := by
  unfold unitClipCurve scalarJoin
  split_ifs
  · simpa only [abs_neg] using positiveClipCurve_bound (-t)
  · exact positiveClipCurve_bound t

theorem unitClip_lipschitz (x y : ℝ) : |unitClip x - unitClip y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (C := 1) (fun t _ => (unitClip_derivative t).hasDerivWithinAt)
    (fun t _ => show ‖unitClipSlope t‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg (unitClipSlope_bounds t).1]
      exact (unitClipSlope_bounds t).2)
    (convex_univ) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem unitClip_le_abs (t : ℝ) : |unitClip t| ≤ |t| := by
  have hz : unitClip 0 = 0 := unitClip_identity (by norm_num)
  simpa only [hz, sub_zero] using unitClip_lipschitz t 0

end FreshGradientMinimax
