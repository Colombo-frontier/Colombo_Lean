import FreshGradientMinimax.BoundedFlatEdge
import FreshGradientMinimax.FlatEnergy
import FreshGradientMinimax.SparsePairNorm

/-! Coordinate sums of the flat Huber energy and their genuine gradients. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped BigOperators InnerProductSpace InnerProduct

def boundedEnergy {n : ℕ} (δ b : ℝ) (x : Euclid n) : ℝ := ∑ i, boundedFlatEdge δ b (x i)
def boundedSlope {n : ℕ} (δ b : ℝ) (x : Euclid n) : Euclid n :=
  (WithLp.equiv 2 _).symm (fun i => boundedFlatSlope δ b (x i))

theorem boundedSlope_apply {n : ℕ} (δ b : ℝ) (x : Euclid n) (i : Fin n) :
    boundedSlope δ b x i = boundedFlatSlope δ b (x i) := rfl

theorem boundedEnergy_hasFDerivAt {n : ℕ} {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (x : Euclid n) :
    HasFDerivAt (boundedEnergy δ b) (innerSL ℝ (boundedSlope δ b x)) x := by
  have hd : HasFDerivAt (boundedEnergy δ b)
      (∑ i : Fin n, boundedFlatSlope δ b (x i) • EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    apply HasFDerivAt.sum
    intro i _
    exact (boundedFlatEdge_derivative hδ hb (x i)).comp_hasFDerivAt x
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply, PiLp.inner_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp [boundedSlope, EuclideanSpace.proj, RCLike.inner_apply', mul_comm]

theorem boundedSlope_lipschitz {n : ℕ} {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) :
    LipschitzWith 1 (boundedSlope (n := n) δ b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [euclid_norm_sq, euclid_norm_sq]
  apply Finset.sum_le_sum
  intro i _
  have h := (boundedFlatSlope_lipschitz hδ hb).dist_le_mul (x i) (y i)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  change (boundedFlatSlope δ b (x i) - boundedFlatSlope δ b (y i)) ^ 2 ≤ (x i - y i) ^ 2
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

theorem boundedSlope_norm {n : ℕ} {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (x : Euclid n) :
    ‖boundedSlope δ b x‖ ≤ b * Real.sqrt n :=
  euclid_norm_le_of_coordinate_bound _ hb (fun i => boundedFlatSlope_bound hδ hb (x i))

theorem boundedSlope_perturbation {n : ℕ} {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (x : Euclid n) :
    ‖boundedSlope δ b x - boundedSlope 0 b x‖ ≤ δ * Real.sqrt n :=
  euclid_norm_le_of_coordinate_bound _ hδ (fun i => boundedFlatSlope_perturbation hδ hb (x i))

theorem boundedEnergy_bounds {n : ℕ} {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (x : Euclid n) :
    0 ≤ boundedEnergy δ b x ∧ boundedEnergy δ b x ≤ ‖x‖ ^ 2 / 2 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (boundedFlatEdge_bounds hδ hb (x i)).1)
  · rw [euclid_norm_sq, Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => (boundedFlatEdge_bounds hδ hb (x i)).2)

theorem boundedEnergy_convex {n : ℕ} {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) :
    ConvexOn ℝ Set.univ (boundedEnergy (n := n) δ b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  simp only [boundedEnergy, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact (boundedFlatEdge_convex hδ hb).2 (Set.mem_univ (x i)) (Set.mem_univ (y i)) hs ht hst

theorem boundedEnergy_zero_core {n : ℕ} {b : ℝ} (hb : 0 ≤ b) (x : Euclid n)
    (hx : ∀ i, |x i| ≤ b) : boundedEnergy 0 b x = ‖x‖ ^ 2 / 2 := by
  rw [euclid_norm_sq, Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => boundedFlatEdge_zero_core hb (hx i))

theorem boundedSlope_zero_core {n : ℕ} {b : ℝ} (hb : 0 ≤ b) (x : Euclid n)
    (hx : ∀ i, |x i| ≤ b) : boundedSlope 0 b x = x := by
  ext i
  exact boundedFlatSlope_zero_core hb (hx i)

end FreshGradientMinimax
