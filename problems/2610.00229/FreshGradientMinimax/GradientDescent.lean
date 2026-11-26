import FreshGradientMinimax.Calculus
import FreshGradientMinimax.SaddleGeometry
import FreshGradientMinimax.IndependentMoments

/-! Exact and noisy gradient-descent contraction from first-order assumptions.
No Hessian, samplewise smoothness, or reuse of stochastic samples is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gradient_step_contraction {f : E → ℝ} {G : E → E} {L α : ℝ} (hL : 0 < L)
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hsc : StrongConvexGradient f G α) (u : E) (hu : ∀ x, f u ≤ f x) (x : E) :
    ‖x - L⁻¹ • G x - u‖ ^ 2 ≤ (1 - α / L) * ‖x - u‖ ^ 2 := by
  have hs := hsc x u
  rw [norm_sub_rev u x] at hs
  have hi : ⟪G x, u - x⟫_ℝ = -⟪G x, x - u⟫_ℝ := by
    simp only [inner_sub_right]; ring
  rw [hi] at hs
  have hg := smooth_gradient_sq_le_gap hL hder hLip u hu x
  have hsL := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * L by positivity)
  have hb : ‖G x‖ ^ 2 + L * α * ‖x - u‖ ^ 2 ≤ 2 * L * ⟪G x, x - u⟫_ℝ := by
    nlinarith only [hsL, hg]
  have hn : L ^ 2 * ‖x - L⁻¹ • G x - u‖ ^ 2 =
      L ^ 2 * ‖x - u‖ ^ 2 - 2 * L * ⟪G x, x - u⟫_ℝ + ‖G x‖ ^ 2 := by
    rw [show x - L⁻¹ • G x - u = (x - u) - L⁻¹ • G x by abel,
      norm_sub_sq_real, real_inner_smul_right, norm_smul_sq, real_inner_comm (x - u) (G x)]
    field_simp
    ring
  have hc : L ^ 2 * ((1 - α / L) * ‖x - u‖ ^ 2) = (L ^ 2 - α * L) * ‖x - u‖ ^ 2 := by
    field_simp
    ring
  apply (mul_le_mul_left (sq_pos_of_pos hL)).mp
  rw [hn, hc]
  nlinarith only [hb]

variable [CompleteSpace E] {Ω : Type*} [MeasurableSpace Ω]
  {ν : Measure Ω} [IsProbabilityMeasure ν]

theorem mean_zero_affine_square (a : E) (s : ℝ) (e : Ω → E)
    (he : Integrable e ν) (he2 : Integrable (fun ω => ‖e ω‖ ^ 2) ν)
    (hzero : (∫ ω, e ω ∂ν) = 0) :
    (∫ ω, ‖a - s • e ω‖ ^ 2 ∂ν) = ‖a‖ ^ 2 + s ^ 2 * (∫ ω, ‖e ω‖ ^ 2 ∂ν) := by
  have hc : Integrable (fun _ : Ω => ‖a‖ ^ 2) ν := integrable_const _
  have hi : Integrable (fun ω => 2 * (s * ⟪a, e ω⟫_ℝ)) ν :=
    ((he.const_inner a).const_mul s).const_mul 2
  have hs : Integrable (fun ω => ‖a‖ ^ 2 - 2 * (s * ⟪a, e ω⟫_ℝ)) ν := hc.sub hi
  simp_rw [norm_sub_sq_real, real_inner_smul_right, norm_smul_sq]
  rw [integral_add hs (he2.const_mul (s ^ 2)), integral_sub hc hi,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_inner he a, hzero]
  simp

theorem noisy_gradient_step_contraction {f : E → ℝ} {G : E → E} {L α V : ℝ} (hL : 0 < L)
    (hder : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hsc : StrongConvexGradient f G α) (u : E) (hu : ∀ x, f u ≤ f x) (x : E)
    (g : Ω → E) (hg : Integrable g ν) (hmean : (∫ ω, g ω ∂ν) = G x)
    (hg2 : Integrable (fun ω => ‖g ω - G x‖ ^ 2) ν)
    (hvar : (∫ ω, ‖g ω - G x‖ ^ 2 ∂ν) ≤ V) :
    (∫ ω, ‖x - L⁻¹ • g ω - u‖ ^ 2 ∂ν) ≤ (1 - α / L) * ‖x - u‖ ^ 2 + V / L ^ 2 := by
  have he : Integrable (fun ω => g ω - G x) ν := hg.sub (integrable_const _)
  have hz : (∫ ω, g ω - G x ∂ν) = 0 := by
    rw [integral_sub hg (integrable_const _), hmean]
    simp
  have hid := mean_zero_affine_square (x - L⁻¹ • G x - u) L⁻¹ (fun ω => g ω - G x) he hg2 hz
  have hform (ω : Ω) : x - L⁻¹ • g ω - u =
      (x - L⁻¹ • G x - u) - L⁻¹ • (g ω - G x) := by module
  simp_rw [← hform] at hid
  rw [hid]
  have hdet := gradient_step_contraction hL hder hLip hsc u hu x
  have hnoise := mul_le_mul_of_nonneg_left hvar (sq_nonneg L⁻¹)
  have heq : L⁻¹ ^ 2 * V = V / L ^ 2 := by ring
  rw [← heq]
  exact add_le_add hdet hnoise

theorem second_moment_about_target (f : Ω → E) (m t : E)
    (hi : Integrable f ν) (hm : (∫ ω, f ω ∂ν) = m)
    (hv : Integrable (fun ω => ‖f ω - m‖ ^ 2) ν) :
    (∫ ω, ‖f ω - t‖ ^ 2 ∂ν) = (∫ ω, ‖f ω - m‖ ^ 2 ∂ν) + ‖m - t‖ ^ 2 := by
  have hc : Integrable (fun ω => f ω - m) ν := hi.sub (integrable_const _)
  have hz : (∫ ω, f ω - m ∂ν) = 0 := by
    rw [integral_sub hi (integrable_const _), hm]
    simp
  have h := mean_zero_affine_square (m - t) (-1) (fun ω => f ω - m) hc hv hz
  have he (ω : Ω) : (m - t) - (-1 : ℝ) • (f ω - m) = f ω - t := by module
  simp_rw [he] at h
  simpa only [neg_one_sq, one_mul, add_comm] using h

theorem squared_bias_le_second_moment (f : Ω → E) (t : E) (hi : Integrable f ν)
    (hv : Integrable (fun ω => ‖f ω - t‖ ^ 2) ν) :
    ‖(∫ ω, f ω ∂ν) - t‖ ^ 2 ≤ ∫ ω, ‖f ω - t‖ ^ 2 ∂ν := by
  have he : Integrable (fun ω => f ω - t) ν := hi.sub (integrable_const _)
  have h := second_moment_decomposition (fun ω => f ω - t) he hv
  have hn := integral_nonneg (μ := ν) (fun ω => sq_nonneg ‖(f ω - t) - ∫ a, f a - t ∂ν‖)
  rw [integral_sub hi (integrable_const _)] at h
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at h
  have hm : (∫ a, f a - t ∂ν) = (∫ a, f a ∂ν) - t := by
    rw [integral_sub hi (integrable_const _)]
    simp
  rw [hm] at hn
  linarith

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem fast_gradient_contraction (u : Euclid dx) (v : Euclid dy) :
    ‖u - ℓ⁻¹ • S.gradX u v - S.sliceMin v‖ ^ 2 ≤ (1 - α / ℓ) * ‖u - S.sliceMin v‖ ^ 2 :=
  gradient_step_contraction S.toNCObjective.L_pos (fun x => S.toNCObjective.derivative_x x v)
    (fun x y => S.toNCObjective.gradX_lip_primal x y v) (S.primal_strong v)
    (S.sliceMin v) (S.sliceMin_minimizes v) u

end SCObjective
end FreshGradientMinimax
