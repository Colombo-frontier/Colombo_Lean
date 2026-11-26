import FreshGradientMinimax.AccelerationGeometry
import FreshGradientMinimax.EffectiveObjective

/-! The two nonnegative error quantities used by the value solver and its
energy relative to the effective minimizer. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α : ℝ} (S : SCObjective dx dy ℓ μ α)

def solverEnergy (Q : Euclid dy → ℝ) (m : ℝ) (v : Euclid dy) (z : Joint dx dy) : ℝ :=
  Q z.2 - Q v + m * ‖z.1 - S.sliceMin v‖ ^ 2

def fastError (m : ℝ) (z : Joint dx dy) : ℝ := m * ‖z.1 - S.sliceMin z.2‖ ^ 2

theorem solverEnergy_continuous {Q : Euclid dy → ℝ} (hQ : Continuous Q) (m : ℝ) (v : Euclid dy) :
    Continuous (S.solverEnergy Q m v) :=
  ((hQ.comp continuous_snd).sub continuous_const).add
    (continuous_const.mul ((continuous_fst.sub continuous_const).norm.pow 2))

theorem fastError_continuous (m : ℝ) : Continuous (S.fastError m) :=
  continuous_const.mul ((continuous_fst.sub (S.sliceMin_continuous.comp continuous_snd)).norm.pow 2)

theorem solverEnergy_nonneg {Q : Euclid dy → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (z : Joint dx dy) : 0 ≤ S.solverEnergy Q m v z := by
  exact add_nonneg (sub_nonneg.mpr (hmin z.2)) (mul_nonneg hm (sq_nonneg _))

theorem fastError_nonneg {m : ℝ} (hm : 0 ≤ m) (z : Joint dx dy) : 0 ≤ S.fastError m z :=
  mul_nonneg hm (sq_nonneg _)

theorem valueGap_le_solverEnergy {Q : Euclid dy → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (v : Euclid dy) (z : Joint dx dy) : Q z.2 - Q v ≤ S.solverEnergy Q m v z := by
  exact le_add_of_nonneg_right (mul_nonneg hm (sq_nonneg _))

theorem referenceError_le_solverEnergy {Q : Euclid dy → ℝ} (m : ℝ)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (z : Joint dx dy) :
    m * ‖z.1 - S.sliceMin v‖ ^ 2 ≤ S.solverEnergy Q m v z := by
  exact le_add_of_nonneg_left (sub_nonneg.mpr (hmin z.2))

theorem sliceMin_lip_four (hfast : ℓ / 4 ≤ α) (x y : Euclid dy) :
    ‖S.sliceMin x - S.sliceMin y‖ ≤ 4 * ‖x - y‖ := by
  have hratio : ℓ / α ≤ 4 := (div_le_iff₀ S.α_pos).mpr (by linarith)
  exact (S.sliceMin_lip x y).trans (mul_le_mul_of_nonneg_right hratio (norm_nonneg _))

theorem solverEnergy_triangle {Q : Euclid dy → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hfast : ℓ / 4 ≤ α) (v : Euclid dy) (z : Joint dx dy) :
    S.solverEnergy Q m v z ≤ Q z.2 - Q v + 2 * S.fastError m z + 32 * m * ‖z.2 - v‖ ^ 2 := by
  have ht := norm_add_sq_le_two (z.1 - S.sliceMin z.2) (S.sliceMin z.2 - S.sliceMin v)
  rw [sub_add_sub_cancel] at ht
  have hl := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 4 * ‖z.2 - v‖)).mpr
    (S.sliceMin_lip_four hfast z.2 v)
  rw [mul_pow] at hl
  have htm := mul_le_mul_of_nonneg_left ht hm
  have hlm := mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm)
  dsimp [solverEnergy, fastError]
  nlinarith only [htm, hlm]

theorem fastError_le_solverEnergy {Q : Euclid dy → ℝ} {grad : Euclid dy → Euclid dy} {m H : ℝ}
    (model : SmoothStrongModel Q grad m H) (hm : 0 < m) (hfast : ℓ / 4 ≤ α)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (z : Joint dx dy) :
    S.fastError m z ≤ 66 * S.solverEnergy Q m v z := by
  have ht := norm_add_sq_le_two (z.1 - S.sliceMin v) (S.sliceMin v - S.sliceMin z.2)
  rw [sub_add_sub_cancel] at ht
  have hl := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 4 * ‖v - z.2‖)).mpr
    (S.sliceMin_lip_four hfast v z.2)
  rw [mul_pow, norm_sub_rev v z.2] at hl
  have htm := mul_le_mul_of_nonneg_left ht hm.le
  have hlm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * m)
  have hg := (model.gap_quadratic_bounds v hmin z.2).1
  have hpos := hmin z.2
  have hR := mul_nonneg hm.le (sq_nonneg ‖z.1 - S.sliceMin v‖)
  dsimp [fastError, solverEnergy]
  nlinarith only [htm, hlm, hg, hpos, hR]

end SCObjective
end FreshGradientMinimax
