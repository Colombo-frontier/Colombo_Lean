import FreshGradientMinimax.FlatEnergy
import FreshGradientMinimax.ClipVector

/-! Weighted flat edge sums with their actual gradients. All bounds include
the flat interfaces and the zero-threshold case. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def weightedFlatEnergy {m : ℕ} (w : Fin m → ℝ) (δ : ℝ) (x : Euclid m) : ℝ :=
  ∑ i, w i * flatEdge δ (x i)

def weightedFlatSlope {m : ℕ} (w : Fin m → ℝ) (δ : ℝ) (x : Euclid m) : Euclid m :=
  coordinateMultiplier w (flatSlope δ x)

@[simp]
theorem weightedFlatSlope_apply {m : ℕ} (w : Fin m → ℝ) (δ : ℝ) (x : Euclid m) (i : Fin m) :
    weightedFlatSlope w δ x i = w i * flatEdgeSlope δ (x i) := rfl

theorem weightedFlatEnergy_hasFDerivAt {m : ℕ} (w : Fin m → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (x : Euclid m) :
    HasFDerivAt (weightedFlatEnergy w δ) (innerSL ℝ (weightedFlatSlope w δ x)) x := by
  have h : HasFDerivAt (weightedFlatEnergy w δ)
      (∑ i : Fin m, (w i * flatEdgeSlope δ (x i)) • EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    apply HasFDerivAt.sum
    intro i _
    convert ((flatEdge_derivative hδ (x i)).comp_hasFDerivAt x
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt).const_mul (w i) using 1
    rw [smul_smul]
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [innerSL_apply, PiLp.inner_apply, RCLike.inner_apply', weightedFlatSlope,
    EuclideanSpace.proj, mul_comm, mul_assoc]

theorem weightedFlatSlope_norm {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, |w i| ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid m) : ‖weightedFlatSlope w δ x‖ ≤ ‖x‖ :=
  (coordinateMultiplier_norm_le hw _).trans (flatSlope_norm_le hδ x)

theorem weightedFlatSlope_difference {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, |w i| ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (x y : Euclid m) :
    ‖weightedFlatSlope w δ x - weightedFlatSlope w δ y‖ ≤ ‖x - y‖ := by
  unfold weightedFlatSlope
  rw [← map_sub]
  exact (coordinateMultiplier_norm_le hw _).trans (by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using (flatSlope_lipschitz hδ).dist_le_mul x y)

theorem flatSlope_zero_threshold {m : ℕ} (x : Euclid m) : flatSlope 0 x = x := by
  ext i
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (flatEdgeSlope_perturbation (le_refl 0) (x i)))

theorem weightedFlatSlope_perturbation {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, |w i| ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid m) :
    ‖weightedFlatSlope w δ x - weightedFlatSlope w 0 x‖ ≤ δ * Real.sqrt m := by
  unfold weightedFlatSlope
  rw [flatSlope_zero_threshold, ← map_sub]
  exact (coordinateMultiplier_norm_le hw _).trans (flatSlope_perturbation hδ x)

theorem weightedFlatSlope_coordinate {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, |w i| ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid m) (i : Fin m) :
    |weightedFlatSlope w δ x i| ≤ |x i| := by
  rw [weightedFlatSlope_apply, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hw i)).trans (flatEdgeSlope_bound hδ _)

end FreshGradientMinimax
