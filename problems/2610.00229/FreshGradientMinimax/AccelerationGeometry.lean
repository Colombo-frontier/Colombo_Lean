import FreshGradientMinimax.SmoothModel
import FreshGradientMinimax.SaddleGeometry

/-! Potential bounds used by the actual accelerated epoch. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_convex_combination_sq {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) (x z : E) :
    ‖r • x + s • z‖ ^ 2 ≤ r * ‖x‖ ^ 2 + s * ‖z‖ ^ 2 := by
  have he : ‖r • x + s • z‖ ^ 2 =
      r * ‖x‖ ^ 2 + s * ‖z‖ ^ 2 - r * s * ‖x - z‖ ^ 2 := by
    have hs' : s = 1 - r := by linarith
    rw [hs', norm_add_sq_real, norm_smul_sq, norm_smul_sq, real_inner_smul_left,
      real_inner_smul_right, norm_sub_sq_real]
    ring
  rw [he]
  have hnon : 0 ≤ r * s * ‖x - z‖ ^ 2 := by positivity
  linarith

namespace SmoothStrongModel
variable {Q : E → ℝ} {grad : E → E} {m H : ℝ} (model : SmoothStrongModel Q grad m H)
include model

theorem continuous : Continuous Q := continuous_iff_continuousAt.mpr (fun x => (model.derivative x).continuousAt)

theorem gap_quadratic_bounds (v : E) (hmin : ∀ t, Q v ≤ Q t) (x : E) :
    m / 2 * ‖x - v‖ ^ 2 ≤ Q x - Q v ∧ Q x - Q v ≤ H / 2 * ‖x - v‖ ^ 2 := by
  have hg := gradient_zero_at_global_min v (model.derivative v) hmin
  have hl := model.lower v x
  have hu := model.upper v x
  rw [hg, inner_zero_left, add_zero] at hl hu
  constructor <;> linarith

omit [InnerProductSpace ℝ E] model in
theorem potential_nonneg (hm : 0 ≤ m) (v : E) (hmin : ∀ t, Q v ≤ Q t) (x z : E) :
    0 ≤ acceleratedPotential Q m v x z := by
  dsimp [acceleratedPotential]
  have hgap := hmin x
  have hn : 0 ≤ m / 2 * ‖z - v‖ ^ 2 := by positivity
  linarith

theorem potential_distances (hm : 0 < m) (v : E) (hmin : ∀ t, Q v ≤ Q t) (x z : E) :
    ‖x - v‖ ^ 2 ≤ 2 * acceleratedPotential Q m v x z / m ∧
      ‖z - v‖ ^ 2 ≤ 2 * acceleratedPotential Q m v x z / m := by
  have hx := (model.gap_quadratic_bounds v hmin x).1
  have hz : 0 ≤ m / 2 * ‖z - v‖ ^ 2 := by positivity
  have hminx := hmin x
  constructor <;> apply (le_div_iff₀ hm).mpr <;> dsimp [acceleratedPotential] <;> nlinarith

theorem potential_initial_bound (v : E) (hmin : ∀ t, Q v ≤ Q t) (x : E) :
    acceleratedPotential Q m v x x ≤ 2 * (Q x - Q v) := by
  have h := (model.gap_quadratic_bounds v hmin x).1
  dsimp [acceleratedPotential]
  linarith

theorem potential_query_distance (hm : 0 < m) {a : ℝ} (ha : 0 ≤ a)
    (v : E) (hmin : ∀ t, Q v ≤ Q t) (x z : E) :
    ‖acceleratedY a x z - v‖ ^ 2 ≤ 2 * acceleratedPotential Q m v x z / m := by
  have hp : 0 < 1 + a := by linarith
  have hs : (1 + a)⁻¹ + ((1 + a)⁻¹ * a) = 1 := by field_simp
  have he : acceleratedY a x z - v = (1 + a)⁻¹ • (x - v) + ((1 + a)⁻¹ * a) • (z - v) := by
    calc
      _ = (1 + a)⁻¹ • (x + a • z) - ((1 + a)⁻¹ + (1 + a)⁻¹ * a) • v := by
        rw [hs, one_smul]; rfl
      _ = _ := by module
  rw [he]
  have hc := norm_convex_combination_sq (inv_nonneg.mpr hp.le) (mul_nonneg (inv_nonneg.mpr hp.le) ha)
    hs (x - v) (z - v)
  obtain ⟨hx, hz⟩ := model.potential_distances hm v hmin x z
  calc
    _ ≤ _ := hc
    _ ≤ (1 + a)⁻¹ * (2 * acceleratedPotential Q m v x z / m) +
        ((1 + a)⁻¹ * a) * (2 * acceleratedPotential Q m v x z / m) :=
      add_le_add (mul_le_mul_of_nonneg_left hx (by positivity)) (mul_le_mul_of_nonneg_left hz (by positivity))
    _ = _ := by rw [← add_mul, hs, one_mul]

theorem reference_query_distance {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (hm : 0 < m) {a k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k)
    (v : E) (hmin : ∀ t, Q v ≤ Q t) (U : E → F)
    (hU : ∀ x y, ‖U x - U y‖ ≤ k * ‖x - y‖) (u : F) (x z : E) :
    m * ‖u - U (acceleratedY a x z)‖ ^ 2 ≤
      2 * m * ‖u - U v‖ ^ 2 + 4 * k ^ 2 * acceleratedPotential Q m v x z := by
  let y := acceleratedY a x z
  have htri := norm_add_sq_le_two (u - U v) (U v - U y)
  rw [sub_add_sub_cancel] at htri
  have hLip := hU v y
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hk (norm_nonneg _))).mpr hLip
  rw [mul_pow, norm_sub_rev v y] at hsq
  have hdist := model.potential_query_distance hm ha v hmin x z
  have hd := (le_div_iff₀ hm).mp hdist
  have ht := mul_le_mul_of_nonneg_left htri hm.le
  have hl := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * m)
  have hq := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * k ^ 2)
  change ‖y - v‖ ^ 2 * m ≤ _ at hd
  change m * ‖u - U y‖ ^ 2 ≤ _
  nlinarith only [ht, hl, hq]

end SmoothStrongModel
end FreshGradientMinimax
