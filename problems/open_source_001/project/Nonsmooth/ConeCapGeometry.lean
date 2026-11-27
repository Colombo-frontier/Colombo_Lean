import Nonsmooth.ProtasovVolumeCertificate
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

open Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem wide_cone_contains_cap {x z e : E} {δ b B : ℝ} (he : ‖e‖ = 1)
    (hδ : 0 ≤ δ) (hx : ‖x‖ ≤ b) (hz : ‖z‖ ≤ B)
    (hcap : b + δ * (B + b) ≤ ⟪z, e⟫_ℝ) :
    δ * ‖z - x‖ ≤ ⟪z - x, e⟫_ℝ := by
  have hn : ‖z - x‖ ≤ B + b := (norm_sub_le z x).trans (add_le_add hz hx)
  have hi : ⟪x, e⟫_ℝ ≤ b := by
    have h := real_inner_le_norm x e
    simpa only [he, mul_one] using h.trans (by simpa only [he, mul_one] using hx)
  have hm := mul_le_mul_of_nonneg_left hn hδ
  rw [inner_sub_left]
  linarith

theorem convex_halfspace_contraction_subset_cap {G : Set E} (hG : Convex ℝ G)
    {r t : ℝ} {e : E} (he : ‖e‖ = 1) (hre : r • e ∈ G) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun y => (1 - t) • (r • e) + t • y) '' {y | y ∈ G ∧ 0 ≤ ⟪y, e⟫_ℝ} ⊆
      {z | z ∈ G ∧ (1 - t) * r ≤ ⟪z, e⟫_ℝ} := by
  rintro z ⟨y, ⟨hyG, hye⟩, rfl⟩
  refine ⟨hG hre hyG (sub_nonneg.mpr ht1) ht (by ring), ?_⟩
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
  exact le_add_of_nonneg_right (mul_nonneg ht hye)

theorem fixed_cap_contraction_bounds (d : ℕ) (hd : 0 < d) :
    0 ≤ (1 - 1 / (2 * (d : ℝ)) : ℝ) ∧ (1 - 1 / (2 * (d : ℝ)) : ℝ) ≤ 1 := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht : 0 ≤ 1 / (2 * (d : ℝ)) := by positivity
  have ht1 : 1 / (2 * (d : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  constructor <;> linarith

theorem fixed_cap_contraction_volume_factor (d : ℕ) (hd : 0 < d) :
    (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (d : ℝ))) ^ d := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hb := one_add_mul_sub_le_pow
    (show (-1 : ℝ) ≤ 1 - 1 / (2 * (d : ℝ)) from
      (by norm_num : (-1 : ℝ) ≤ 0).trans (fixed_cap_contraction_bounds d hd).1) d
  have heq : (1 : ℝ) + (d : ℝ) * ((1 - 1 / (2 * (d : ℝ))) - 1) = 1 / 2 := by
    field_simp
    ring
  rwa [heq] at hb

end
end Nonsmooth
