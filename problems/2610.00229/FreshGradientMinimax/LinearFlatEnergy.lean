import FreshGradientMinimax.FlatEnergy

/-! Pulling the flat coordinate energy back through a linear incidence map.
These statements apply equally to a path in its own coordinates and to a path
embedded into a larger Euclidean space by an orthonormal frame. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ}

def linearFlatEnergy (A : E →L[ℝ] Euclid n) (β δ : ℝ) (x : E) : ℝ := β * flatEnergy δ (A x)

def linearFlatGradient (A : E →L[ℝ] Euclid n) (β δ : ℝ) (x : E) : E := β • (A†) (flatSlope δ (A x))

theorem linearFlatEnergy_hasFDerivAt (A : E →L[ℝ] Euclid n) (β : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    HasFDerivAt (linearFlatEnergy A β δ) (innerSL ℝ (linearFlatGradient A β δ x)) x := by
  have hd := ((flatEnergy_hasFDerivAt hδ (A x)).comp x A.hasFDerivAt).const_mul β
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [linearFlatGradient, innerSL_apply, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]

theorem linearFlatEnergy_gradient (A : E →L[ℝ] Euclid n) (β : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (x : E) :
    gradient (linearFlatEnergy A β δ) x = linearFlatGradient A β δ x :=
  (hasGradientAt_iff_hasFDerivAt.mpr (linearFlatEnergy_hasFDerivAt A β hδ x)).gradient

omit [CompleteSpace E] in
theorem linearFlatEnergy_convex (A : E →L[ℝ] Euclid n) {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ) :
    ConvexOn ℝ Set.univ (linearFlatEnergy A β δ) := by
  have h := ((flatEnergy_convex (n := n) hδ).comp_linearMap A.toLinearMap).smul hβ
  simpa only [Set.preimage_univ, Function.comp_def, smul_eq_mul] using h

omit [CompleteSpace E] in
theorem linearFlatEnergy_nonneg (A : E →L[ℝ] Euclid n) {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (x : E) : 0 ≤ linearFlatEnergy A β δ x :=
  mul_nonneg hβ (flatEnergy_bounds hδ (A x)).1

theorem linearFlatGradient_zero (A : E →L[ℝ] Euclid n) (β : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    linearFlatGradient A β δ 0 = 0 := by simp [linearFlatGradient, flatSlope_zero hδ]

theorem linearFlatGradient_difference (A : E →L[ℝ] Euclid n) {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (x y : E) :
    ‖linearFlatGradient A β δ x - linearFlatGradient A β δ y‖ ≤ β * ‖A‖ ^ 2 * ‖x - y‖ := by
  have hs := (flatSlope_lipschitz hδ).dist_le_mul (A x) (A y)
  simp only [dist_eq_norm, NNReal.coe_one, one_mul] at hs
  have hn : ‖A†‖ = ‖A‖ := ContinuousLinearMap.adjoint.norm_map A
  simp only [linearFlatGradient, ← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hβ]
  calc
    _ ≤ β * (‖A†‖ * ‖flatSlope δ (A x) - flatSlope δ (A y)‖) :=
      mul_le_mul_of_nonneg_left ((A†).le_opNorm _) hβ
    _ = β * (‖A‖ * ‖flatSlope δ (A x) - flatSlope δ (A y)‖) := by rw [hn]
    _ ≤ β * (‖A‖ * ‖A x - A y‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (norm_nonneg _)) hβ
    _ ≤ β * (‖A‖ * (‖A‖ * ‖x - y‖)) := by
      rw [← map_sub]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)) hβ
    _ = β * ‖A‖ ^ 2 * ‖x - y‖ := by ring

theorem linearFlatGradient_lipschitz (A : E →L[ℝ] Euclid n) {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hA : ‖A‖ ≤ 2) :
    LipschitzWith ⟨4 * β, by positivity⟩ (linearFlatGradient A β δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_mk]
  have hn : ‖A‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg A]
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hβ) (norm_nonneg (x - y))
  nlinarith only [linearFlatGradient_difference A hβ hδ x y, hm]

theorem linearFlatGradient_norm_bound (A : E →L[ℝ] Euclid n) {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hA : ‖A‖ ≤ 2) (x : E) :
    ‖linearFlatGradient A β δ x‖ ≤ 4 * β * ‖x‖ := by
  have h := (linearFlatGradient_lipschitz A hβ hδ hA).dist_le_mul x 0
  simpa only [linearFlatGradient_zero A β hδ, dist_zero_right, NNReal.coe_mk] using h

omit [CompleteSpace E] in
theorem linearFlatEnergy_upper (A : E →L[ℝ] Euclid n) {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hA : ‖A‖ ≤ 2) (x : E) :
    linearFlatEnergy A β δ x ≤ 2 * β * ‖x‖ ^ 2 := by
  have hx : ‖A x‖ ≤ 2 * ‖x‖ :=
    (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hs : ‖A x‖ ^ 2 ≤ 4 * ‖x‖ ^ 2 := by nlinarith [norm_nonneg (A x), norm_nonneg x]
  have h1 := mul_le_mul_of_nonneg_left (flatEnergy_bounds hδ (A x)).2 hβ
  have h2 := mul_le_mul_of_nonneg_left hs hβ
  change β * flatEnergy δ (A x) ≤ _
  nlinarith only [h1, h2]

theorem linearFlatGradient_perturbation (A : E →L[ℝ] Euclid n) {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hA : ‖A‖ ≤ 2) (x : E) :
    ‖linearFlatGradient A β δ x - β • (A†) (A x)‖ ≤ 2 * β * δ * Real.sqrt n := by
  have hn : ‖A†‖ = ‖A‖ := ContinuousLinearMap.adjoint.norm_map A
  simp only [linearFlatGradient, ← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hβ]
  calc
    _ ≤ β * (‖A†‖ * ‖flatSlope δ (A x) - A x‖) :=
      mul_le_mul_of_nonneg_left ((A†).le_opNorm _) hβ
    _ ≤ β * (2 * ‖flatSlope δ (A x) - A x‖) := by
      rw [hn]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA (norm_nonneg _)) hβ
    _ ≤ β * (2 * (δ * Real.sqrt n)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (flatSlope_perturbation hδ (A x)) (by norm_num)) hβ
    _ = 2 * β * δ * Real.sqrt n := by ring

end FreshGradientMinimax
