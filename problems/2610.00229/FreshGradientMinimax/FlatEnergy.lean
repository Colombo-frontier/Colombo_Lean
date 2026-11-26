import FreshGradientMinimax.FlatEdge
import FreshGradientMinimax.PathIncidence

/-! Coordinatewise flat energies on Euclidean space, with their true gradient,
dimension-free smoothness, and the accumulated perturbation from a quadratic. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace

def flatEnergy {n : ℕ} (δ : ℝ) (x : Euclid n) : ℝ := ∑ i, flatEdge δ (x i)

def flatSlope {n : ℕ} (δ : ℝ) (x : Euclid n) : Euclid n :=
  (WithLp.equiv 2 _).symm (fun i => flatEdgeSlope δ (x i))

@[simp]
theorem flatSlope_apply {n : ℕ} (δ : ℝ) (x : Euclid n) (i : Fin n) :
    flatSlope δ x i = flatEdgeSlope δ (x i) := rfl

theorem flatEnergy_hasFDerivAt {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid n) :
    HasFDerivAt (flatEnergy δ) (innerSL ℝ (flatSlope δ x)) x := by
  have hd : HasFDerivAt (flatEnergy δ)
      (∑ i : Fin n, flatEdgeSlope δ (x i) • EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    apply HasFDerivAt.sum
    intro i _
    have hp : HasFDerivAt (fun y : Euclid n => y i) (EuclideanSpace.proj (𝕜 := ℝ) i) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
    exact (flatEdge_derivative hδ (x i)).comp_hasFDerivAt x hp
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply, PiLp.inner_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp [flatSlope, EuclideanSpace.proj, RCLike.inner_apply', mul_comm]

theorem flatEnergy_gradient {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid n) :
    gradient (flatEnergy δ) x = flatSlope δ x :=
  (hasGradientAt_iff_hasFDerivAt.mpr (flatEnergy_hasFDerivAt hδ x)).gradient

theorem flatSlope_lipschitz {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    LipschitzWith 1 (flatSlope (n := n) δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [euclid_norm_sq, euclid_norm_sq]
  apply Finset.sum_le_sum
  intro i _
  have h := (flatEdgeSlope_lipschitz hδ).dist_le_mul (x i) (y i)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  change (flatEdgeSlope δ (x i) - flatEdgeSlope δ (y i)) ^ 2 ≤ (x i - y i) ^ 2
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

theorem flatSlope_zero {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) : flatSlope δ (0 : Euclid n) = 0 := by
  ext i
  exact flatEdgeSlope_flat hδ (by simpa using hδ)

theorem flatSlope_norm_le {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid n) :
    ‖flatSlope δ x‖ ≤ ‖x‖ := by
  have h := (flatSlope_lipschitz hδ).dist_le_mul x 0
  simpa only [flatSlope_zero hδ, dist_zero_right, NNReal.coe_one, one_mul] using h

theorem flatSlope_perturbation {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid n) :
    ‖flatSlope δ x - x‖ ≤ δ * Real.sqrt n := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [euclid_norm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑ _ : Fin n, δ ^ 2 := Finset.sum_le_sum (fun i _ => by
      have h := flatEdgeSlope_perturbation hδ (x i)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2)
    _ = δ ^ 2 * n := by simp [mul_comm]

theorem flatEnergy_bounds {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (x : Euclid n) :
    0 ≤ flatEnergy δ x ∧ flatEnergy δ x ≤ ‖x‖ ^ 2 / 2 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (flatEdge_bounds hδ (x i)).1)
  · rw [euclid_norm_sq, Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => (flatEdge_bounds hδ (x i)).2)

theorem flatEnergy_convex {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    ConvexOn ℝ Set.univ (flatEnergy (n := n) δ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [flatEnergy, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact (flatEdge_convex hδ).2 (Set.mem_univ (x i)) (Set.mem_univ (y i)) ha hb hab

end FreshGradientMinimax

