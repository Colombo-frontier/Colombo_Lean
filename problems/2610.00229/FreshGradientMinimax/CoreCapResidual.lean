import FreshGradientMinimax.CoreLinkResidual

/-! The shared radial wall does not introduce a dimension factor in the
static truncation residual. These estimates apply at every dual query. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem sqrt_dimension_le_dimension (n : ℕ) : Real.sqrt (n + 1 : ℝ) ≤ (n + 1 : ℝ) := by
  have hs := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  nlinarith only [hs, Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]

theorem coreCap_prefix_correction_u (n : ℕ) {μ t a : ℝ}
    (hμ : 0 < μ) (ht : 0 < t) (ha : 0 ≤ a) :
    (8 * a / coreCapHeight n μ t) * (7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ)) ≤ 82 * a := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (coreCapHeight_pos n hμ ht)).mpr
  have h := mul_le_mul_of_nonneg_left (sqrt_dimension_le_dimension n)
    (show 0 ≤ 62400 * a * μ * t ^ 2 by positivity)
  unfold coreCapHeight
  nlinarith only [h, show 0 ≤ a * (n + 1 : ℝ) * μ * t ^ 2 by positivity]

theorem coreCap_prefix_correction_y (n : ℕ) {μ t a r : ℝ}
    (hμ : 0 < μ) (ht : 0 < t) (ha : 0 ≤ a) (hrt : r ≤ t) :
    ((8 * a / coreCapHeight n μ t) * r) * (180 * μ * t * Real.sqrt (n + 1 : ℝ)) ≤ 2 * a := by
  have he : ((8 * a / coreCapHeight n μ t) * r) * (180 * μ * t * Real.sqrt (n + 1 : ℝ)) =
      (1440 * a * μ * t * (r * Real.sqrt (n + 1 : ℝ))) / coreCapHeight n μ t := by ring
  rw [he]
  apply (div_le_iff₀ (coreCapHeight_pos n hμ ht)).mpr
  have hp := mul_le_mul hrt (sqrt_dimension_le_dimension n) (Real.sqrt_nonneg _) ht.le
  have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1440 * a * μ * t by positivity)
  unfold coreCapHeight
  nlinarith only [h, show 0 ≤ a * (n + 1 : ℝ) * μ * t ^ 2 by positivity]

theorem coreProtectedWeight_prefix_residual {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t r : ℝ} (hμ : 0 < μ) (ht : 0 < t) (k : Fin n) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4)
    (hyL : |frameCoordinates V y (k.castAdd n)| ≤ r) (hyR : |frameCoordinates V y (k.natAdd n)| ≤ r) :
    |coreProtectedWeight V μ t (fun _ => 1) u y -
      coreProtectedWeight V μ t (coreLinkPrefix n (k.val + 1)) u y| ≤
      (8 * (2 * μ * t) / coreCapHeight n μ t) * r := by
  apply smoothRampSlope_comp_bound (coreCapHeight_pos n hμ ht)
  convert coreInteraction_prefix_residual V (by positivity : 0 ≤ 2 * μ * t)
    (by positivity : 0 < 32 * t) k u y hu hyL hyR using 1
  congr 1
  unfold coreProtectedQ
  ring

theorem coreProtectedCapGradU_prefix_residual {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t r : ℝ} (hμ : 0 < μ) (ht : 0 < t) (hr : 0 ≤ r)
    (k : Fin n) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4)
    (hyL : |frameCoordinates V y (k.castAdd n)| ≤ r) (hyR : |frameCoordinates V y (k.natAdd n)| ≤ r) :
    ‖coreProtectedCapGradU V μ t (fun _ => 1) u y -
      coreProtectedCapGradU V μ t (coreLinkPrefix n (k.val + 1)) u y‖ ≤ 162 * (2 * μ * t) * r := by
  have hn : ‖-coreInteractionGradU V (2 * μ * t) (32 * t) (fun _ => 1) u y‖ ≤
      7800 * (μ * t ^ 2) * Real.sqrt (n + 1 : ℝ) := by
    simpa only [norm_neg] using scaledInteractionGradU_norm V hμ ht (fun _ => 1) (by intro i; norm_num) u y
  have hd : ‖-coreInteractionGradU V (2 * μ * t) (32 * t) (fun _ => 1) u y -
      -coreInteractionGradU V (2 * μ * t) (32 * t) (coreLinkPrefix n (k.val + 1)) u y‖ ≤ 80 * (2 * μ * t) * r := by
    simpa only [neg_sub_neg, norm_sub_rev] using coreInteractionGradU_prefix_residual V
      (by positivity : 0 ≤ 2 * μ * t) (by positivity : 0 < 32 * t) k u y hu hyL hyR
  have h := weighted_vector_difference_bound _ _ _ _
    (coreProtectedWeight_bounds V hμ ht (coreLinkPrefix n (k.val + 1)) u y) hr hn hd
    (coreProtectedWeight_prefix_residual V hμ ht k u y hu hyL hyR)
    (coreCap_prefix_correction_u n hμ ht (by positivity : 0 ≤ 2 * μ * t))
  unfold coreProtectedCapGradU
  convert h using 1
  ring

theorem coreProtectedCapGradY_prefix_residual {n dy : ℕ} (V : Euclid (n + n) →ₗᵢ[ℝ] Euclid dy)
    {μ t r : ℝ} (hμ : 0 < μ) (ht : 0 < t) (hrt : r ≤ t)
    (k : Fin n) (u : Euclid (n + 1)) (y : Euclid dy)
    (hu : ∀ i : Fin (n + 1), k.val < i.val → |u i| ≤ 1 / 4)
    (hyL : |frameCoordinates V y (k.castAdd n)| ≤ r) (hyR : |frameCoordinates V y (k.natAdd n)| ≤ r) :
    ‖coreProtectedCapGradY V μ t (fun _ => 1) u y -
      coreProtectedCapGradY V μ t (coreLinkPrefix n (k.val + 1)) u y‖ ≤ 10 * (2 * μ * t) := by
  by_cases hy : ‖y‖ ≤ coreControlRadius n t
  · have hn := coreGapGradY_norm_on_ball V hμ ht (fun _ => 1) (by intro i; norm_num) u y hy
    have hd : ‖coreGapGradY V μ t (fun _ => 1) u y -
        coreGapGradY V μ t (coreLinkPrefix n (k.val + 1)) u y‖ ≤ 8 * (2 * μ * t) := by
      simpa only [coreGapGradY, add_sub_add_left_eq_sub] using coreInteractionGradY_prefix_residual V
        (by positivity : 0 ≤ 2 * μ * t) (32 * t) k u y hu
    have hb := coreProtectedWeight_prefix_residual V hμ ht k u y hu hyL hyR
    have hp := mul_le_mul hb hn (norm_nonneg _) ((abs_nonneg _).trans hb)
    have hc := coreCap_prefix_correction_y n hμ ht (by positivity : 0 ≤ 2 * μ * t) hrt
    have h := weighted_vector_difference
      (coreProtectedWeight V μ t (fun _ => 1) u y)
      (coreProtectedWeight V μ t (coreLinkPrefix n (k.val + 1)) u y)
      (coreGapGradY V μ t (fun _ => 1) u y)
      (coreGapGradY V μ t (coreLinkPrefix n (k.val + 1)) u y)
      (coreProtectedWeight_bounds V hμ ht (coreLinkPrefix n (k.val + 1)) u y)
    rw [coreProtectedCapGradY_gap_form, coreProtectedCapGradY_gap_form, sub_sub_sub_cancel_left, norm_sub_rev]
    linarith only [h, hp, hc, hd]
  · have hout := (lt_of_not_ge hy).le
    rw [coreProtectedCapGradY_outside V hμ ht (fun _ => 1) (by intro i; norm_num) u y hout,
      coreProtectedCapGradY_outside V hμ ht (coreLinkPrefix n (k.val + 1)) (coreLinkPrefix_bound _ _) u y hout,
      sub_self, norm_zero]
    positivity

end FreshGradientMinimax
