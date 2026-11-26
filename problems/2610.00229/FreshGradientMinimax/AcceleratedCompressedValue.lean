import FreshGradientMinimax.AcceleratedCompressedModel

/-! The exact supremum and actual value gradient after primal protection.
In particular the large-query part of E.2 holds without a coordinate condition. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {n k dx dy : ℕ}
  (U : Euclid (k * 2 + 1) →ₗᵢ[ℝ] Euclid dx)
  (V : Euclid (k * (n + 2)) →ₗᵢ[ℝ] Euclid dy)

def acceleratedCompressedValue (δ : ℝ) (x : Euclid dx) : ℝ :=
  framedAcceleratedValue V δ (compressedCoordinates U 1 (acceleratedPrimalRadius k) x) +
    primalRidgeConstant / 2 * ‖x‖ ^ 2

def acceleratedCompressedValueGradient (δ : ℝ) (x : Euclid dx) : Euclid dx :=
  radialCompressionDerivative (acceleratedPrimalRadius k) x
    (U (gradient (framedAcceleratedValue V δ) (compressedCoordinates U 1 (acceleratedPrimalRadius k) x))) +
    primalRidgeConstant • x

theorem acceleratedCompressedModel_value (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid dx) :
    (acceleratedCompressedModel U V hn hδ).value x = acceleratedCompressedValue U V δ x := by
  let O := framedAcceleratedModel V hn hδ
  let u := compressedCoordinates U 1 (acceleratedPrimalRadius k) x
  have he : framedAcceleratedValue V δ u = framedAcceleratedProtected V δ u (O.dualMax u) := O.value_eq_max u
  apply IsGreatest.csSup_eq
  refine ⟨⟨O.dualMax u, ?_⟩, ?_⟩
  · change framedAcceleratedProtected V δ u (O.dualMax u) + _ = framedAcceleratedValue V δ u + _
    rw [he]
  · rintro _ ⟨y, rfl⟩
    change framedAcceleratedProtected V δ u y + _ ≤ framedAcceleratedValue V δ u + _
    rw [he]
    exact add_le_add_right (O.le_dualMax u y) _

theorem framedAcceleratedValue_gradient_bound (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (u : Euclid (k * 2 + 1)) :
    ‖gradient (framedAcceleratedValue V δ) u‖ ≤ 10 ^ 8 * Real.sqrt (k + 1 : ℕ) := by
  change ‖gradient (framedAcceleratedModel V hn hδ).value u‖ ≤ _
  rw [NCObjective.true_primal_gradient]
  exact framedAcceleratedModel_gradient_bound V hn hδ u _

theorem acceleratedCompressedValue_hasFDerivAt (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid dx) :
    HasFDerivAt (acceleratedCompressedValue U V δ) (innerSL ℝ (acceleratedCompressedValueGradient U V δ x)) x := by
  let O := framedAcceleratedModel V hn hδ
  let u := compressedCoordinates U 1 (acceleratedPrimalRadius k) x
  have hf : HasFDerivAt (framedAcceleratedValue V δ) (innerSL ℝ (gradient (framedAcceleratedValue V δ) u)) u := by
    change HasFDerivAt O.value (innerSL ℝ (gradient O.value u)) u
    rw [O.true_primal_gradient]
    exact O.value_hasFDerivAt u
  have hd := (hf.comp x (compressedCoordinates_hasFDerivAt U 1 (acceleratedPrimalRadius_pos k) x)).add
    (half_quadratic_hasFDerivAt primalRidgeConstant x)
  apply hd.congr_fderiv
  ext v
  have hi := compressedPullback_inner U 1 (acceleratedPrimalRadius k) x v (gradient (framedAcceleratedValue V δ) u)
  simp only [compressedPullback, inv_one, one_smul] at hi
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, innerSL_apply,
    acceleratedCompressedValueGradient, inner_add_left, InnerProductSpace.toDual_apply]
  exact congrArg (fun a => a + ⟪primalRidgeConstant • x, v⟫_ℝ) hi.symm

theorem acceleratedCompressedValue_gradient (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid dx) :
    gradient (acceleratedCompressedValue U V δ) x = acceleratedCompressedValueGradient U V δ x :=
  (hasGradientAt_iff_hasFDerivAt.mpr (acceleratedCompressedValue_hasFDerivAt U V hn hδ x)).gradient

theorem acceleratedCompressedModel_primalGradient (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid dx) :
    (acceleratedCompressedModel U V hn hδ).primalGradient x = acceleratedCompressedValueGradient U V δ x := by
  rw [← NCObjective.true_primal_gradient,
    show (acceleratedCompressedModel U V hn hδ).value = acceleratedCompressedValue U V δ from
      funext (acceleratedCompressedModel_value U V hn hδ)]
  exact acceleratedCompressedValue_gradient U V hn hδ x

theorem acceleratedCompressedModel_gap (hn : 10 ≤ n + 2) (hk : 0 < k) :
    (acceleratedCompressedModel U V hn (acceleratedThreshold_pos n hk).le).PrimalGapAtMost (1000 * (k + 1 : ℕ)) := by
  intro x
  simp only [acceleratedCompressedModel_value U V hn (acceleratedThreshold_pos n hk).le,
    acceleratedCompressedValue, compressedCoordinates_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, add_zero]
  have h := framedAcceleratedModel_gap V hn hk (compressedCoordinates U 1 (acceleratedPrimalRadius k) x)
  change framedAcceleratedValue V (acceleratedThreshold n k) 0 -
    framedAcceleratedValue V (acceleratedThreshold n k) (compressedCoordinates U 1 (acceleratedPrimalRadius k) x) ≤ _ at h
  nlinarith only [h, mul_nonneg primalRidgeConstant_pos.le (sq_nonneg ‖x‖)]

theorem acceleratedCompressedModel_origin_dual (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    (acceleratedCompressedModel U V hn hδ).dualMax 0 = 0 := by
  apply ((acceleratedCompressedModel U V hn hδ).dualMax_unique 0 0 ?_).symm
  intro y
  change compressedObjective U (framedAcceleratedProtected V δ) 1 (acceleratedPrimalRadius k) primalRidgeConstant 0 y ≤
    compressedObjective U (framedAcceleratedProtected V δ) 1 (acceleratedPrimalRadius k) primalRidgeConstant 0 0
  simp only [compressedObjective, compressedCoordinates_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]
  rw [framedAcceleratedProtected_origin V hn hδ]
  exact framedAcceleratedProtected_origin_max V hn hδ y

theorem acceleratedCompressedValueGradient_large (hn : 10 ≤ n + 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (x : Euclid dx) (hx : acceleratedPrimalRadius k / 2 < ‖x‖) :
    primalRidgeConstant / 2 < ‖acceleratedCompressedValueGradient U V δ x‖ := by
  let g := gradient (framedAcceleratedValue V δ) (compressedCoordinates U 1 (acceleratedPrimalRadius k) x)
  let d := radialCompressionDerivative (acceleratedPrimalRadius k) x (U g)
  have h1 : ‖d‖ ≤ 10 ^ 8 * Real.sqrt (k + 1 : ℕ) :=
    (radialCompressionDerivative_norm_apply x (U g)).trans
      (by simpa only [U.norm_map] using framedAcceleratedValue_gradient_bound V hn hδ _)
  have h2 : ‖primalRidgeConstant • x‖ ≤ ‖d + primalRidgeConstant • x‖ + ‖d‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (d + primalRidgeConstant • x) d
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos primalRidgeConstant_pos] at h2
  have h3 := mul_lt_mul_of_pos_left hx primalRidgeConstant_pos
  change primalRidgeConstant / 2 < ‖d + primalRidgeConstant • x‖
  linarith only [h1, h2, h3, acceleratedPrimalRadius_large k]

end FreshGradientMinimax


