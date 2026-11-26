import Nonsmooth.AEDirectionalNorm

open MeasureTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unit_axis_plane_decomposition {u : E} (hu : ‖u‖ = 1) (v : E) :
    (∃ a : ℝ, v = a • u) ∨
      ∃ (a b : ℝ) (w : E), ‖w‖ = 1 ∧ ⟪u, w⟫_ℝ = 0 ∧
        v = a • u + b • w ∧ ‖v‖ ^ 2 = a ^ 2 + b ^ 2 := by
  let a := ⟪u, v⟫_ℝ
  let r := v - a • u
  by_cases hr : r = 0
  · exact Or.inl ⟨a, sub_eq_zero.mp hr⟩
  · let w := ‖r‖⁻¹ • r
    have hn : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
    have hw : ‖w‖ = 1 := by simp [w, norm_smul, Real.norm_eq_abs, hn]
    have hur : ⟪u, r⟫_ℝ = 0 := by
      simp [r, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, a]
    have huw : ⟪u, w⟫_ℝ = 0 := by simp [w, real_inner_smul_right, hur]
    have hv : v = a • u + ‖r‖ • w := by
      simp [w, smul_smul, hn, r]
    refine Or.inr ⟨a, ‖r‖, w, hw, huw, hv, ?_⟩
    rw [hv, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, hu, hw, mul_one, sq_abs,
      real_inner_smul_left, real_inner_smul_right, huw, mul_zero, add_zero]

variable [FiniteDimensional ℝ E] {α : Type} [MeasurableSpace α]

theorem exists_unit_orthogonal_direction {u : E} (hu : ‖u‖ = 1)
    (hd : 2 ≤ Module.finrank ℝ E) : ∃ w : E, ‖w‖ = 1 ∧ ⟪u, w⟫_ℝ = 0 := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hline : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu0
  let K := (ℝ ∙ u)ᗮ
  have hk : 0 < Module.finrank ℝ K := by
    have hsum := (ℝ ∙ u).finrank_add_finrank_orthogonal
    dsimp only [K]
    omega
  letI : Nontrivial K := Module.finrank_pos_iff.mp hk
  obtain ⟨z, hz⟩ := exists_ne (0 : K)
  have hzE : (z : E) ≠ 0 := by
    intro h
    exact hz (Subtype.ext h)
  have hn : ‖(z : E)‖ ≠ 0 := norm_ne_zero_iff.mpr hzE
  have horth : ⟪u, (z : E)⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.property
  refine ⟨‖(z : E)‖⁻¹ • (z : E), ?_, ?_⟩
  · simp [norm_smul, Real.norm_eq_abs, hn]
  · simp [real_inner_smul_right, horth]

omit [FiniteDimensional ℝ E] in
theorem ae_directional_inner_bound_of_planes (μ : Measure α) (m : α → E) (b : α → ℝ)
    {u : E} (hu : ‖u‖ = 1)
    (hbase : ∀ᵐ x ∂μ, ⟪u, m x⟫_ℝ ^ 2 ≤ b x)
    (hplanes : ∀ w : E, ‖w‖ = 1 → ⟪u, w⟫_ℝ = 0 →
      ∀ᵐ x ∂μ, ⟪u, m x⟫_ℝ ^ 2 + ⟪w, m x⟫_ℝ ^ 2 ≤ b x) (v : E) :
    ∀ᵐ x ∂μ, ⟪v, m x⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 * b x := by
  rcases unit_axis_plane_decomposition hu v with ⟨a, hv⟩ | ⟨a, c, w, hw, huw, hv, hn⟩
  · filter_upwards [hbase] with x hx
    rw [hv, real_inner_smul_left, norm_smul, hu, Real.norm_eq_abs, mul_one, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left hx (sq_nonneg a)
  · filter_upwards [hplanes w hw huw] with x hx
    calc
      ⟪v, m x⟫_ℝ ^ 2 = (a * ⟪u, m x⟫_ℝ + c * ⟪w, m x⟫_ℝ) ^ 2 := by
        rw [hv, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      _ ≤ (a ^ 2 + c ^ 2) * (⟪u, m x⟫_ℝ ^ 2 + ⟪w, m x⟫_ℝ ^ 2) := by
        nlinarith [sq_nonneg (a * ⟪w, m x⟫_ℝ - c * ⟪u, m x⟫_ℝ)]
      _ ≤ ‖v‖ ^ 2 * b x := by
        rw [hn]
        exact mul_le_mul_of_nonneg_left hx (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Each transverse direction can have its own null exception. The passage to
the full norm uses fixed directions first and a common dense-set exception last. -/
theorem ae_norm_sq_bound_of_planes (μ : Measure α) (m : α → E) (b : α → ℝ)
    {u : E} (hu : ‖u‖ = 1)
    (hbase : ∀ᵐ x ∂μ, ⟪u, m x⟫_ℝ ^ 2 ≤ b x)
    (hplanes : ∀ w : E, ‖w‖ = 1 → ⟪u, w⟫_ℝ = 0 →
      ∀ᵐ x ∂μ, ⟪u, m x⟫_ℝ ^ 2 + ⟪w, m x⟫_ℝ ^ 2 ≤ b x) :
    ∀ᵐ x ∂μ, ‖m x‖ ^ 2 ≤ b x := by
  apply ae_norm_sq_le_of_directional_inner_bound μ m b
  · exact hbase.mono (fun x hx => (sq_nonneg _).trans hx)
  · exact ae_directional_inner_bound_of_planes μ m b hu hbase hplanes

end
end Nonsmooth
