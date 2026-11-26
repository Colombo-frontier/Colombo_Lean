import Nonsmooth.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {α : Type} [MeasurableSpace α]

/-- Directionwise almost-everywhere quadratic bounds share one common exceptional
set. No measurable choice of a maximizing direction is needed. -/
theorem ae_all_directional_inner_bound (μ : Measure α) (m : α → E) (b : α → ℝ)
    (h : ∀ v : E, ∀ᵐ x ∂μ, ⟪v, m x⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 * b x) :
    ∀ᵐ x ∂μ, ∀ v : E, ⟪v, m x⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 * b x := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense E
  have hd : ∀ᵐ x ∂μ, ∀ v ∈ D, ⟪v, m x⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 * b x :=
    (ae_ball_iff hD).mpr (fun v _ => h v)
  filter_upwards [hd] with x hx
  have hs : IsClosed {v : E | ⟪v, m x⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 * b x} :=
    isClosed_le ((continuous_id.inner continuous_const).pow 2)
      ((continuous_norm.pow 2).mul continuous_const)
  have hsub := closure_minimal hx hs
  rw [hdense.closure_eq] at hsub
  exact fun v => hsub (mem_univ v)

omit [FiniteDimensional ℝ E] in
theorem norm_sq_le_of_all_directional_inner_bound (m : E) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ v : E, ⟪v, m⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 * b) : ‖m‖ ^ 2 ≤ b := by
  have hm := h m
  rw [real_inner_self_eq_norm_sq] at hm
  by_cases hn : ‖m‖ ^ 2 = 0
  · simpa only [hn] using hb
  · have hp : 0 < ‖m‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)
    nlinarith

theorem ae_norm_sq_le_of_directional_inner_bound (μ : Measure α) (m : α → E) (b : α → ℝ)
    (hb : ∀ᵐ x ∂μ, 0 ≤ b x)
    (h : ∀ v : E, ∀ᵐ x ∂μ, ⟪v, m x⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 * b x) :
    ∀ᵐ x ∂μ, ‖m x‖ ^ 2 ≤ b x := by
  filter_upwards [hb, ae_all_directional_inner_bound μ m b h] with x hx hh
  exact norm_sq_le_of_all_directional_inner_bound (m x) hx hh

theorem ae_norm_sq_le_of_directional_inner_bound_nontrivial [Nontrivial E]
    (μ : Measure α) (m : α → E) (b : α → ℝ)
    (h : ∀ v : E, ∀ᵐ x ∂μ, ⟪v, m x⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 * b x) :
    ∀ᵐ x ∂μ, ‖m x‖ ^ 2 ≤ b x := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hp : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
  filter_upwards [ae_all_directional_inner_bound μ m b h] with x hx
  have hb : 0 ≤ b x := nonneg_of_mul_nonneg_right ((sq_nonneg _).trans (hx v)) hp
  exact norm_sq_le_of_all_directional_inner_bound (m x) hb hx

end
end Nonsmooth
