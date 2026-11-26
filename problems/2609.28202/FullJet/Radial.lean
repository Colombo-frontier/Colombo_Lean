import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open scoped ContDiff InnerProductSpace

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def radial (z : E) : E := (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ • z

theorem radial_contDiff : ContDiff ℝ ∞ (radial : E → E) := by
  have hpos (z : E) : 0 < 1 + ‖z‖ ^ 2 := by positivity
  exact (((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt
    (fun z => (hpos z).ne')).inv
    (fun z => (Real.sqrt_pos.mpr (hpos z)).ne')).smul contDiff_id

theorem radial_norm_le_one (z : E) : ‖radial z‖ ≤ 1 := by
  have hpos : 0 < Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 1 + ‖z‖ ^ 2 by positivity)
  have hle : ‖z‖ ≤ Real.sqrt (1 + ‖z‖ ^ 2) := by
    nlinarith [norm_nonneg z]
  rw [radial, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
    inv_mul_eq_div]
  exact (div_le_one hpos).mpr hle

noncomputable def alignment (θ z : E) : ℝ := ⟪θ, radial z⟫_ℝ

theorem alignment_bound (θ z : E) : |alignment θ z| ≤ ‖θ‖ := by
  calc
    _ ≤ ‖θ‖ * ‖radial z‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖θ‖ * 1 := mul_le_mul_of_nonneg_left (radial_norm_le_one z) (norm_nonneg θ)
    _ = _ := mul_one _

theorem unit_alignment_bound (θ z : E) (hθ : ‖θ‖ = 1) : |alignment θ z| ≤ 1 := by
  simpa [hθ] using alignment_bound θ z

theorem row_alignment_bound (s z : E) (ρ : ℝ) (hρ : 0 < ρ) (hs : ‖s‖ = 1) :
    |ρ⁻¹ * alignment s z| ≤ 1 / ρ := by
  rw [abs_mul, abs_of_pos (inv_pos.mpr hρ)]
  calc
    _ ≤ ρ⁻¹ * 1 := mul_le_mul_of_nonneg_left (unit_alignment_bound s z hs) (inv_nonneg.mpr hρ.le)
    _ = _ := by simp

/-- Exact table averaging is preserved by the radial map at every query. -/
theorem alignment_average {n : ℕ} (s : Fin n → E) (θ z : E) (ρ : ℝ)
    (hn : (n : ℝ) ≠ 0) (hρ : ρ ≠ 0)
    (htable : ∑ i, s i = ((n : ℝ) * ρ) • θ) :
    (n : ℝ)⁻¹ * (∑ i, ρ⁻¹ * alignment (s i) z) = alignment θ z := by
  unfold alignment
  rw [← Finset.mul_sum, ← sum_inner, htable, real_inner_smul_left]
  field_simp

end FullJet
