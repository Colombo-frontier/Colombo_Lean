import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Tactic

/-! # The actual projection used for clipped online updates -/

noncomputable section
open Set Metric
open scoped InnerProductSpace
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def ballProjection (D : ℝ) (hD : 0 ≤ D) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex
    (nonempty_closedBall.mpr hD) isClosed_closedBall.isComplete (convex_closedBall 0 D) x)

theorem ballProjection_mem (D : ℝ) (hD : 0 ≤ D) (x : E) :
    ballProjection D hD x ∈ closedBall (0 : E) D :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    (nonempty_closedBall.mpr hD) isClosed_closedBall.isComplete (convex_closedBall 0 D) x)).1

theorem ballProjection_variational (D : ℝ) (hD : 0 ≤ D) (x : E) {u : E} (hu : ‖u‖ ≤ D) :
    ⟪x - ballProjection D hD x, u - ballProjection D hD x⟫_ℝ ≤ 0 := by
  have hop := (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    (nonempty_closedBall.mpr hD) isClosed_closedBall.isComplete (convex_closedBall (0 : E) D) x)).2
  exact (norm_eq_iInf_iff_real_inner_le_zero (convex_closedBall 0 D)
    (ballProjection_mem D hD x)).mp hop u (by simpa only [mem_closedBall, dist_zero_right] using hu)

theorem ballProjection_distance_le (D : ℝ) (hD : 0 ≤ D) (x : E) {u : E} (hu : ‖u‖ ≤ D) :
    ‖ballProjection D hD x - u‖ ≤ ‖x - u‖ := by
  let p := ballProjection D hD x
  have hv := ballProjection_variational D hD x hu
  have he := norm_sub_sq_real (x - p) (u - p)
  have hab : (x - p) - (u - p) = x - u := by abel
  rw [hab, norm_sub_rev u p] at he
  dsimp only [p] at he
  nlinarith [sq_nonneg ‖x - ballProjection D hD x‖,
    norm_nonneg (ballProjection D hD x - u), norm_nonneg (x - u)]

theorem ballProjection_lipschitz (D : ℝ) (hD : 0 ≤ D) :
    LipschitzWith 1 (ballProjection (E := E) D hD) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let p := ballProjection D hD x
  let q := ballProjection D hD y
  have hp : ‖p‖ ≤ D := by simpa only [mem_closedBall, dist_zero_right] using ballProjection_mem D hD x
  have hq : ‖q‖ ≤ D := by simpa only [mem_closedBall, dist_zero_right] using ballProjection_mem D hD y
  have ha := ballProjection_variational D hD x hq
  have hb := ballProjection_variational D hD y hp
  change ⟪x - p, q - p⟫_ℝ ≤ 0 at ha
  change ⟪y - q, p - q⟫_ℝ ≤ 0 at hb
  have hi : ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right] at ha hb ⊢
    linarith
  have hc := real_inner_le_norm (x - y) (p - q)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  change ‖p - q‖ ≤ ‖x - y‖
  nlinarith [norm_nonneg (p - q), norm_nonneg (x - y)]

theorem ballProjection_measurable [MeasurableSpace E] [BorelSpace E] (D : ℝ) (hD : 0 ≤ D) :
    Measurable (ballProjection (E := E) D hD) :=
  (ballProjection_lipschitz D hD).continuous.measurable

end NCBall
