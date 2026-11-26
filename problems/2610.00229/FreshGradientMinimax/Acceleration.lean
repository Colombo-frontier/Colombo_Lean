import FreshGradientMinimax.Basic

/-! Deterministic algebra underlying Lemma F.2, in arbitrary real inner product
spaces. The function inequalities are explicit smoothness/convexity assumptions.
The random moment integration is supplied separately in `Probability.lean`. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def acceleratedY (a : ℝ) (x z : E) : E := (1 + a)⁻¹ • (x + a • z)
def acceleratedZ (a m : ℝ) (z y d : E) : E := (1 - a) • z + a • y - (a / m) • d
def acceleratedPotential (Q : E → ℝ) (m : ℝ) (v x z : E) : ℝ :=
  Q x - Q v + m / 2 * ‖z - v‖ ^ 2

theorem acceleratedY_relation {a : ℝ} (ha : 1 + a ≠ 0) (x z : E) :
    x - acceleratedY a x z = -a • (z - acceleratedY a x z) := by
  have hy : (1 + a) • acceleratedY a x z = x + a • z := by
    simp [acceleratedY, smul_smul, ha]
  calc
    x - acceleratedY a x z =
        ((1 + a) • acceleratedY a x z - a • z) - acceleratedY a x z := by
          rw [hy]
          module
    _ = _ := by module

/-- Equation (47), including the nonpositive remainder from its norm expansion. -/
theorem exact_acceleration_inequality {Q : E → ℝ} {a m H : ℝ}
    (hm : 0 < m) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hscale : a ^ 2 / m = H⁻¹) (v x y z d : E)
    (hxy : x - y = -a • (z - y))
    (hconv : Q y + ⟪d, x - y⟫_ℝ ≤ Q x)
    (hstrong : Q y - Q v + m / 2 * ‖y - v‖ ^ 2 ≤ ⟪d, y - v⟫_ℝ) :
    Q y - Q v - ‖d‖ ^ 2 / (2 * H) +
      m / 2 * ‖acceleratedZ a m z y d - v‖ ^ 2 ≤
      (1 - a) * acceleratedPotential Q m v x z := by
  have hi :
      Q y - Q v - ‖d‖ ^ 2 / (2 * H) +
        m / 2 * ‖acceleratedZ a m z y d - v‖ ^ 2 -
        (1 - a) * acceleratedPotential Q m v x z =
      (1 - a) * (Q y + ⟪d, x - y⟫_ℝ - Q x) +
        a * (Q y - Q v + m / 2 * ‖y - v‖ ^ 2 - ⟪d, y - v⟫_ℝ) -
        m * a * (1 - a) / 2 * ‖z - y‖ ^ 2 := by
    rw [hxy]
    have hcoef : 1 / (2 * H) = a ^ 2 / (2 * m) := by
      calc
        1 / (2 * H) = H⁻¹ / 2 := by ring
        _ = _ := by rw [← hscale]; ring
    rw [div_eq_mul_one_div (‖d‖ ^ 2), hcoef]
    simp only [acceleratedZ, acceleratedPotential, ← real_inner_self_eq_norm_sq,
      inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, real_inner_comm]
    field_simp
    ring
  have hc := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha1)
    (sub_nonpos.mpr hconv)
  have hs := mul_nonpos_of_nonneg_of_nonpos ha (sub_nonpos.mpr hstrong)
  have h1 : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hn : 0 ≤ m * a * (1 - a) / 2 * ‖z - y‖ ^ 2 := by positivity
  linarith

/-- Smoothness at a noisy gradient step, without a cross term in the primal error. -/
theorem noisy_primal_step {Q : E → ℝ} {H : ℝ} (hH : 0 < H) (y d e : E)
    (hsmooth : Q (y - H⁻¹ • (d + e)) ≤ Q y +
      ⟪d, (y - H⁻¹ • (d + e)) - y⟫_ℝ +
      H / 2 * ‖(y - H⁻¹ • (d + e)) - y‖ ^ 2) :
    Q (y - H⁻¹ • (d + e)) ≤ Q y - ‖d‖ ^ 2 / (2 * H) + ‖e‖ ^ 2 / (2 * H) := by
  have he : (y - H⁻¹ • (d + e)) - y = -H⁻¹ • (d + e) := by module
  rw [he] at hsmooth
  have hi : Q y + ⟪d, -H⁻¹ • (d + e)⟫_ℝ + H / 2 * ‖-H⁻¹ • (d + e)‖ ^ 2 =
      Q y - ‖d‖ ^ 2 / (2 * H) + ‖e‖ ^ 2 / (2 * H) := by
    rw [norm_smul_sq, norm_add_sq_real]
    simp only [inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]
    field_simp
    ring
  rwa [hi] at hsmooth

/-- Change in the z-potential from the gradient error. -/
theorem noisy_z_identity {a m H : ℝ} (hm : m ≠ 0)
    (hscale : a ^ 2 / m = H⁻¹) (v y z d e : E) :
    m / 2 * ‖acceleratedZ a m z y (d + e) - v‖ ^ 2 =
      m / 2 * ‖acceleratedZ a m z y d - v‖ ^ 2 -
        a * ⟪acceleratedZ a m z y d - v, e⟫_ℝ + ‖e‖ ^ 2 / (2 * H) := by
  have he : acceleratedZ a m z y (d + e) - v =
      (acceleratedZ a m z y d - v) - (a / m) • e := by
    unfold acceleratedZ
    module
  rw [he, norm_sub_sq_real, inner_smul_right, norm_smul_sq]
  have hc : 1 / (2 * H) = a ^ 2 / (2 * m) := by
    calc
      1 / (2 * H) = H⁻¹ / 2 := by ring
      _ = _ := by rw [← hscale]; ring
  rw [div_eq_mul_one_div (‖e‖ ^ 2), hc]
  field_simp
  ring

/-- Pointwise bound that may be integrated conditionally to prove (46). -/
theorem noisy_acceleration_step {Q : E → ℝ} {a m H : ℝ}
    (hm : 0 < m) (hH : 0 < H) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hscale : a ^ 2 / m = H⁻¹) (v x y z d e : E)
    (hxy : x - y = -a • (z - y))
    (hconv : Q y + ⟪d, x - y⟫_ℝ ≤ Q x)
    (hstrong : Q y - Q v + m / 2 * ‖y - v‖ ^ 2 ≤ ⟪d, y - v⟫_ℝ)
    (hsmooth : Q (y - H⁻¹ • (d + e)) ≤ Q y +
      ⟪d, (y - H⁻¹ • (d + e)) - y⟫_ℝ +
      H / 2 * ‖(y - H⁻¹ • (d + e)) - y‖ ^ 2) :
    acceleratedPotential Q m v (y - H⁻¹ • (d + e)) (acceleratedZ a m z y (d + e)) ≤
      (1 - a) * acceleratedPotential Q m v x z -
        a * ⟪acceleratedZ a m z y d - v, e⟫_ℝ + ‖e‖ ^ 2 / H := by
  have hex := exact_acceleration_inequality hm ha ha1 hscale v x y z d hxy hconv hstrong
  have hp := noisy_primal_step hH y d e hsmooth
  have hz := noisy_z_identity (ne_of_gt hm) hscale v y z d e
  unfold acceleratedPotential at hex ⊢
  ring_nf at hp hz hex ⊢
  linarith

/-- The exact-step z-distance estimate used to absorb conditional bias. -/
theorem exact_z_distance {Q : E → ℝ} {a m H : ℝ} (ha : 0 ≤ a)
    (v x y z d : E)
    (hP : 0 ≤ acceleratedPotential Q m v x z)
    (hdescent : 0 ≤ Q y - Q v - ‖d‖ ^ 2 / (2 * H))
    (hex : Q y - Q v - ‖d‖ ^ 2 / (2 * H) +
      m / 2 * ‖acceleratedZ a m z y d - v‖ ^ 2 ≤
      (1 - a) * acceleratedPotential Q m v x z) :
    m / 2 * ‖acceleratedZ a m z y d - v‖ ^ 2 ≤ acceleratedPotential Q m v x z := by
  have ht : 0 ≤ a * acceleratedPotential Q m v x z := mul_nonneg ha hP
  linarith

/-- Young's inequality with the constants in (46). -/
theorem bias_absorption {P m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (z b : E)
    (hz : m / 2 * ‖z‖ ^ 2 ≤ P) :
    -a * ⟪z, b⟫_ℝ ≤ a / 2 * P + a / m * ‖b‖ ^ 2 := by
  have hsq := sq_nonneg ‖(m / 2) • z + b‖
  rw [norm_add_sq_real, norm_smul_sq, inner_smul_left] at hsq
  simp only [starRingEnd_apply, star_trivial] at hsq
  have hb : -⟪z, b⟫_ℝ ≤ (P * m / 2 + ‖b‖ ^ 2) / m := by
    apply (le_div_iff₀ hm).mpr
    nlinarith [mul_le_mul_of_nonneg_left hz hm.le]
  calc
    -a * ⟪z, b⟫_ℝ ≤ a * ((P * m / 2 + ‖b‖ ^ 2) / m) := by
      nlinarith [mul_le_mul_of_nonneg_left hb ha]
    _ = _ := by field_simp; ring

end FreshGradientMinimax
