import FreshGradientMinimax.FlatLocality
import FreshGradientMinimax.CoordinateMask

/-! Deleting the still hidden coordinates of a path preserves both value and
gradient at good queries. An edge touching the old visible set is retained in
full after the next exposure; every other changed row lies in the flat zone. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ}

theorem signed_difference_small {s a b δ : ℝ} (hs : |s| ≤ 1)
    (ha : |a| ≤ δ / 2) (hb : |b| ≤ δ / 2) : |a - s * b| ≤ δ := by
  have hm : |s * b| ≤ |b| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (abs_nonneg b)
  have ht := abs_sub a (s * b)
  linarith

omit [CompleteSpace E] in
theorem path_truncation_row_agreement (C : E →L[ℝ] Euclid (n + 1))
    (old new : Finset (Fin (n + 1))) {s : Fin (n + 2) → ℝ} (hs : ∀ i, |s i| ≤ 1)
    (hfirst : (0 : Fin (n + 1)) ∈ new) (hlast : Fin.last n ∈ new)
    (hexpand : ∀ i : Fin n, i.castSucc ∈ old ∨ i.succ ∈ old →
      i.castSucc ∈ new ∧ i.succ ∈ new)
    {δ : ℝ} {x : E} (hsmall : ∀ i ∉ old, |C x i| ≤ δ / 2) :
    FlatRowAgreement ((pathIncidence s).comp C)
      ((pathIncidence s).comp ((coordinateMask new).comp C)) δ x := by
  intro e
  refine Fin.cases ?_ (fun j => ?_) e
  · left
    intro v
    simp only [ContinuousLinearMap.comp_apply, pathIncidence_apply, Fin.cons_zero,
      mul_zero, sub_zero]
    change Fin.snoc (α := fun _ => ℝ) (fun i => C v i) 0 (0 : Fin (n + 1)).castSucc =
      Fin.snoc (α := fun _ => ℝ) (fun i => coordinateMask new (C v) i) 0
        (0 : Fin (n + 1)).castSucc
    simp only [Fin.snoc_castSucc, coordinateMask_apply, if_pos hfirst]
  · refine Fin.lastCases ?_ (fun i => ?_) j
    · left
      intro v
      simp only [ContinuousLinearMap.comp_apply]
      rw [pathIncidence_apply, pathIncidence_apply, Fin.cons_succ, Fin.cons_succ,
        Fin.succ_last, Fin.snoc_last, Fin.snoc_last, coordinateMask_apply, if_pos hlast]
    · have hrow (B : E →L[ℝ] Euclid (n + 1)) (v : E) :
          ((pathIncidence s).comp B) v i.castSucc.succ =
            B v i.succ - s i.castSucc.succ * B v i.castSucc := by
        rw [ContinuousLinearMap.comp_apply, pathIncidence_apply, Fin.cons_succ,
          Fin.succ_castSucc, Fin.snoc_castSucc]
      by_cases hv : i.castSucc ∈ new ∧ i.succ ∈ new
      · left
        intro v
        rw [hrow, hrow]
        simp only [ContinuousLinearMap.comp_apply, coordinateMask_apply,
          if_pos hv.1, if_pos hv.2]
      · right
        have hhidden : i.castSucc ∉ old ∧ i.succ ∉ old := by
          constructor
          · intro h; exact hv (hexpand i (Or.inl h))
          · intro h; exact hv (hexpand i (Or.inr h))
        rw [hrow, hrow]
        constructor
        · exact signed_difference_small (hs _) (hsmall _ hhidden.2) (hsmall _ hhidden.1)
        · exact signed_difference_small (hs _)
            ((coordinateMask_abs_le new (C x) _).trans (hsmall _ hhidden.2))
            ((coordinateMask_abs_le new (C x) _).trans (hsmall _ hhidden.1))

omit [CompleteSpace E] in
theorem path_bands_row_agreement (C : E →L[ℝ] Euclid (n + 1))
    {w : ℕ} (hw : 0 < w) {s : Fin (n + 2) → ℝ} (hs : ∀ i, |s i| ≤ 1)
    {δ : ℝ} {x : E} (hsmall : ∀ i ∉ pathVisible (n + 1) w, |C x i| ≤ δ / 2) :
    FlatRowAgreement ((pathIncidence s).comp C)
      ((pathIncidence s).comp ((coordinateMask (pathVisible (n + 1) (w + 1))).comp C)) δ x :=
  path_truncation_row_agreement C _ _ hs (pathVisible_first (by omega))
    (pathVisible_last (by omega)) pathVisible_expand_edge hsmall

theorem path_bands_cap_gradient (C : E →L[ℝ] Euclid (n + 1))
    {w : ℕ} (hw : 0 < w) {s : Fin (n + 2) → ℝ} (hs : ∀ i, |s i| ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) {x : E}
    (hsmall : ∀ i ∉ pathVisible (n + 1) w, |C x i| ≤ δ / 2) (β R : ℝ) :
    let A := (pathIncidence s).comp C
    let B := (pathIncidence s).comp ((coordinateMask (pathVisible (n + 1) (w + 1))).comp C)
    radialCapGradient (linearFlatEnergy A β δ) (linearFlatGradient A β δ) β R x =
      radialCapGradient (linearFlatEnergy B β δ) (linearFlatGradient B β δ) β R x :=
  cappedLinearFlatGradient_row_agreement hδ (path_bands_row_agreement C hw hs hsmall) β R

end FreshGradientMinimax

