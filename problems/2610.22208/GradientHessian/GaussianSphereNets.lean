import GradientHessian.GaussianSingularGeometry
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Actual finite nets of the compact unit sphere, with a quantitative
support-function error used to pass finite Gaussian comparisons to spheres. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open Set Metric
open scoped InnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure UnitSphereNet (ε : ℝ) where
  points : Finset E
  nonempty : points.Nonempty
  unit : ∀ x ∈ points, ‖x‖=1
  covers : ∀ x : E, ‖x‖=1 → ∃ y ∈ points, ‖x-y‖ < ε

namespace UnitSphereNet
variable {E} {ε : ℝ}

abbrev Index (N : UnitSphereNet E ε) := {x : E // x ∈ N.points}
instance (N : UnitSphereNet E ε) : Nonempty N.Index := N.nonempty.coe_sort

omit [InnerProductSpace ℝ E] in
theorem index_unit (N : UnitSphereNet E ε) (i : N.Index) : ‖(i : E)‖=1 := N.unit i i.property

omit [InnerProductSpace ℝ E] in
theorem radius_pos (N : UnitSphereNet E ε) : 0 < ε := by
  obtain ⟨i⟩ := inferInstanceAs (Nonempty N.Index)
  obtain ⟨y,_,hy⟩ := N.covers i (N.index_unit i)
  exact (norm_nonneg _).trans_lt hy

theorem support_upper (N : UnitSphereNet E ε) (y : E) :
    finiteMaximum (fun i : N.Index => ⟪(i : E),y⟫_ℝ) ≤ ‖y‖ := by
  apply finiteMaximum_le
  intro i
  simpa only [N.index_unit i,one_mul] using real_inner_le_norm (i : E) y

theorem support_lower (N : UnitSphereNet E ε) (y : E) :
    ‖y‖ - ε * ‖y‖ ≤ finiteMaximum (fun i : N.Index => ⟪(i : E),y⟫_ℝ) := by
  by_cases hy : y=0
  · subst y
    obtain ⟨i⟩ := inferInstanceAs (Nonempty N.Index)
    simpa only [norm_zero, mul_zero, sub_self, inner_zero_right] using
      le_finiteMaximum (fun i : N.Index => ⟪(i : E),(0 : E)⟫_ℝ) i
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let u : E := ‖y‖⁻¹ • y
  have hu : ‖u‖=1 := by
    dsimp only [u]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hi : ⟪u,y⟫_ℝ=‖y‖ := by
    dsimp only [u]
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp [hn.ne']
    ring
  obtain ⟨v,hv,hd⟩ := N.covers u hu
  have hc := real_inner_le_norm (u-v) y
  rw [inner_sub_left,hi] at hc
  have hh : ‖y‖ - ⟪v,y⟫_ℝ ≤ ε*‖y‖ := hc.trans (mul_le_mul_of_nonneg_right hd.le hn.le)
  have hm := le_finiteMaximum (fun i : N.Index => ⟪(i : E),y⟫_ℝ) (⟨v,hv⟩ : N.Index)
  dsimp only at hm
  linarith

theorem support_bounds (N : UnitSphereNet E ε) (y : E) :
    ‖y‖ - ε * ‖y‖ ≤ finiteMaximum (fun i : N.Index => ⟪(i : E),y⟫_ℝ) ∧
      finiteMaximum (fun i : N.Index => ⟪(i : E),y⟫_ℝ) ≤ ‖y‖ :=
  ⟨N.support_lower y,N.support_upper y⟩

end UnitSphereNet

theorem exists_unitSphereNet [FiniteDimensional ℝ E] [Nontrivial E] {ε : ℝ} (hε : 0 < ε) :
    Nonempty (UnitSphereNet E ε) := by
  classical
  obtain ⟨s,hs,hfin,hcover⟩ := (isCompact_sphere (0 : E) 1).finite_cover_balls hε
  have hnon : s.Nonempty := by
    obtain ⟨x,hx⟩ := unit_sphere_nonempty (E := E)
    have h := hcover hx
    rcases mem_iUnion₂.mp h with ⟨y,hy,_⟩
    exact ⟨y,hy⟩
  refine ⟨⟨hfin.toFinset,by simpa using hnon,?_,?_⟩⟩
  · intro x hx
    have h := hs (by simpa using hx)
    simpa only [mem_sphere,dist_zero_right] using h
  · intro x hx
    have hh := hcover (by simpa only [mem_sphere,dist_zero_right] using hx)
    rcases mem_iUnion₂.mp hh with ⟨y,hy,hxy⟩
    exact ⟨y,by simpa using hy,by simpa only [mem_ball,dist_eq_norm] using hxy⟩

end GradientHessian.GaussianConcentration
