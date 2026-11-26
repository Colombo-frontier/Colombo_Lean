import HeavyTail.Curvature
import HeavyTail.ProximalTransfer
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Log

/-! Correctness consequences of the manuscript's public proximal access.
The oracle contract is primal minimization over the original feasible domain.
Subgradient inequalities and displacement monotonicity are derived from it. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace HeavyTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ProximalOracle (S : Set E) (h : E → ℝ) where
  point : ℝ → E → E
  feasible : ∀ η, 0 < η → ∀ z, point η z ∈ S
  minimizing : ∀ η, 0 < η → ∀ z u, u ∈ S →
    h (point η z) + ‖point η z - z‖ ^ 2 / (2 * η) ≤
      h u + ‖u - z‖ ^ 2 / (2 * η)

theorem proximalQuadratic_strongConvex {S : Set E} (hS : Convex ℝ S)
    (η : ℝ) (z : E) : StrongConvexOn S η⁻¹ (fun u => ‖u - z‖ ^ 2 / (2 * η)) := by
  rw [strongConvexOn_iff_convex]
  have hid : (fun u : E => ‖u - z‖ ^ 2 / (2 * η) - η⁻¹ / 2 * ‖u‖ ^ 2) =
      (fun u => -η⁻¹ * ⟪u, z⟫_ℝ + ‖z‖ ^ 2 / (2 * η)) := by
    funext u
    rw [norm_sub_sq_real]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid]
  refine ⟨hS, ?_⟩
  intro u hu v hv a b ha hb hab
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  have heq : -η⁻¹ * (a * ⟪u, z⟫_ℝ + b * ⟪v, z⟫_ℝ) + ‖z‖ ^ 2 / (2 * η) =
      a * (-η⁻¹ * ⟪u, z⟫_ℝ + ‖z‖ ^ 2 / (2 * η)) +
      b * (-η⁻¹ * ⟪v, z⟫_ℝ + ‖z‖ ^ 2 / (2 * η)) := by
    have h := congrArg (fun t : ℝ => t * (‖z‖ ^ 2 / (2 * η))) hab
    nlinarith only [h]
  exact heq.le

theorem proximalObjective_strongConvex {S : Set E} {h : E → ℝ} {μ η : ℝ}
    (hh : StrongConvexOn S μ h) (z : E) :
    StrongConvexOn S (μ + η⁻¹) (fun u => h u + ‖u - z‖ ^ 2 / (2 * η)) := by
  simpa only [StrongConvexOn, Pi.add_apply, add_div, add_mul] using
    hh.add (proximalQuadratic_strongConvex hh.1 η z)

theorem proximalOracle_growth {S : Set E} {h : E → ℝ} {μ η : ℝ}
    (P : ProximalOracle S h) (hh : StrongConvexOn S μ h)
    (hμ : 0 ≤ μ) (hη : 0 < η) (z u : E) (hu : u ∈ S) :
    h (P.point η z) - h u ≤
      (‖u - z‖ ^ 2 - ‖P.point η z - z‖ ^ 2) / (2 * η) -
      (μ + η⁻¹) / 2 * ‖u - P.point η z‖ ^ 2 := by
  have hg := strongConvex_minimum_growth (add_nonneg hμ (inv_nonneg.mpr hη.le))
    (proximalObjective_strongConvex hh z) (P.feasible η hη z) hu
    (P.minimizing η hη z)
  rw [sub_div]
  linarith only [hg]

theorem proximalOracle_subgradient {S : Set E} {h : E → ℝ} {η : ℝ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) (hη : 0 < η)
    (z u : E) (hu : u ∈ S) :
    h (P.point η z) - h u ≤ ⟪η⁻¹ • (z - P.point η z), P.point η z - u⟫_ℝ := by
  have hg := proximalOracle_growth P (strongConvexOn_zero.mpr hh) (le_refl 0) hη z u hu
  have hid : (‖u - z‖ ^ 2 - ‖P.point η z - z‖ ^ 2) / (2 * η) -
      (0 + η⁻¹) / 2 * ‖u - P.point η z‖ ^ 2 =
      ⟪η⁻¹ • (z - P.point η z), P.point η z - u⟫_ℝ := by
    simp only [norm_sub_sq_real, real_inner_smul_left, inner_sub_left, inner_sub_right,
      real_inner_self_eq_norm_sq, zero_add, div_eq_mul_inv, mul_inv_rev]
    rw [real_inner_comm z (P.point η z), real_inner_comm z u,
      real_inner_comm (P.point η z) u]
    ring
  exact hid ▸ hg

theorem proximalOracle_displacement_mono {S : Set E} {h : E → ℝ} {η γ : ℝ}
    (P : ProximalOracle S h) (hη : 0 < η) (hηγ : η ≤ γ) (z : E) :
    ‖P.point η z - z‖ ≤ ‖P.point γ z - z‖ := by
  rcases hηγ.eq_or_lt with hEq | hlt
  · rw [hEq]
  have hγ : 0 < γ := hη.trans hlt
  have hl := P.minimizing η hη z (P.point γ z) (P.feasible γ hγ z)
  have hr := P.minimizing γ hγ z (P.point η z) (P.feasible η hη z)
  have hc : 0 < (2 * η)⁻¹ - (2 * γ)⁻¹ :=
    sub_pos.mpr ((inv_lt_inv₀ (by positivity) (by positivity)).mpr (by linarith))
  simp only [div_eq_mul_inv] at hl hr
  have hprod : (‖P.point η z - z‖ ^ 2 - ‖P.point γ z - z‖ ^ 2) *
      ((2 * η)⁻¹ - (2 * γ)⁻¹) ≤ 0 := by nlinarith only [hl, hr]
  have hs : ‖P.point η z - z‖ ^ 2 ≤ ‖P.point γ z - z‖ ^ 2 := by
    have hnonpos : ‖P.point η z - z‖ ^ 2 - ‖P.point γ z - z‖ ^ 2 ≤ 0 := by
      by_contra hn
      have hp := mul_pos (lt_of_not_ge hn) hc
      linarith only [hp, hprod]
    linarith only [hnonpos]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

omit [InnerProductSpace ℝ E] in
theorem regularizer_linear_lower {S : Set E} {f h : E → ℝ} {xstar u : E} {G : ℝ}
    (hmin : ∀ x ∈ S, f xstar + h xstar ≤ f x + h x)
    (hu : u ∈ S) (hlip : f u - f xstar ≤ G * ‖u - xstar‖) :
    h xstar - G * ‖u - xstar‖ ≤ h u := by
  have hm := hmin u hu
  linarith only [hm, hlip]

theorem proximalOracle_displacement_bound {S : Set E} {h : E → ℝ} {η G : ℝ}
    (P : ProximalOracle S h) (hη : 0 < η) (hG : 0 ≤ G)
    (z xstar : E) (hx : xstar ∈ S)
    (hlower : ∀ u ∈ S, h xstar - G * ‖u - xstar‖ ≤ h u) :
    ‖P.point η z - z‖ ≤ 2 * η * G + ‖z - xstar‖ := by
  have hm := P.minimizing η hη z xstar hx
  have hl := hlower (P.point η z) (P.feasible η hη z)
  have ht : ‖P.point η z - xstar‖ ≤ ‖P.point η z - z‖ + ‖z - xstar‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have ht' := mul_le_mul_of_nonneg_left ht hG
  rw [norm_sub_rev xstar z] at hm
  have hm' : ‖P.point η z - z‖ ^ 2 ≤ ‖z - xstar‖ ^ 2 +
      2 * η * G * (‖P.point η z - z‖ + ‖z - xstar‖) := by
    have hh : (‖P.point η z - z‖ ^ 2 - ‖z - xstar‖ ^ 2) / (2 * η) ≤
        G * (‖P.point η z - z‖ + ‖z - xstar‖) := by
      rw [sub_div]
      linarith only [hm, hl, ht']
    have := (div_le_iff₀ (by positivity : 0 < 2 * η)).mp hh
    nlinarith only [this]
  by_contra hn
  have hgt : 2 * η * G + ‖z - xstar‖ < ‖P.point η z - z‖ := lt_of_not_ge hn
  have hsum : 0 < ‖P.point η z - z‖ + ‖z - xstar‖ := by
    have hp : 0 ≤ 2 * η * G := by positivity
    linarith [norm_nonneg (z - xstar)]
  have hp := mul_pos (sub_pos.mpr hgt) hsum
  nlinarith only [hp, hm']

end HeavyTail
