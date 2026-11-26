import GradientHessian.GaussianSphereNets

/-! Quantitative convergence of the literal finite bilinear maximum and
min-max to the largest and least singular expansions. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ε : ℝ} (U : UnitSphereNet E ε) (V : UnitSphereNet F ε)

def netBilinear (T : E →L[ℝ] F) (p : U.Index × V.Index) : ℝ := ⟪(p.2 : F),T (p.1 : E)⟫_ℝ

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem netBilinear_row_bounds (T : E →L[ℝ] F) (i : U.Index) :
    ‖T (i : E)‖ - ε*‖T‖ ≤ finiteMaximum (fun j : V.Index => netBilinear U V T (i,j)) ∧
      finiteMaximum (fun j : V.Index => netBilinear U V T (i,j)) ≤ ‖T (i : E)‖ := by
  have ht : ‖T (i : E)‖ ≤ ‖T‖ := by simpa only [U.index_unit i,mul_one] using T.le_opNorm (i : E)
  have hs := V.support_bounds (T (i : E))
  refine ⟨?_,hs.2⟩
  change _ ≤ finiteMaximum (fun j : V.Index => ⟪(j : F),T (i : E)⟫_ℝ)
  have he := mul_le_mul_of_nonneg_left ht V.radius_pos.le
  linarith [hs.1]

theorem net_leastExpansion_bounds (T : E →L[ℝ] F) :
    leastExpansion T - ε*‖T‖ ≤ finiteMinMax (netBilinear U V T) ∧
      finiteMinMax (netBilinear U V T) ≤ leastExpansion T + ε*‖T‖ := by
  constructor
  · apply le_finiteMinimum
    intro i
    have hrow := (netBilinear_row_bounds U V T i).1
    have hmin := leastExpansion_le T (U.index_unit i)
    exact (sub_le_sub_right hmin _).trans hrow
  · obtain ⟨x,hx,he⟩ := leastExpansion_attained T
    obtain ⟨y,hy,hxy⟩ := U.covers x hx
    let i : U.Index := ⟨y,hy⟩
    have hm := finiteMinimum_le (finiteRows (netBilinear U V T)) i
    have hrow := (netBilinear_row_bounds U V T i).2
    have hn := norm_sub_norm_le (T y) (T x)
    have hd := T.le_opNorm (y-x)
    rw [map_sub,norm_sub_rev y x] at hd
    have hb := mul_le_mul_of_nonneg_left hxy.le (norm_nonneg T)
    change finiteMinMax (netBilinear U V T) ≤
      finiteMaximum (fun j : V.Index => netBilinear U V T (i,j)) at hm
    have hi : ‖T (i : E)‖=‖T y‖ := rfl
    rw [hi] at hrow
    linarith

theorem net_largestExpansion_bounds (T : E →L[ℝ] F) :
    ‖T‖ - 2*ε*‖T‖ ≤ finiteMaximum (netBilinear U V T) ∧
      finiteMaximum (netBilinear U V T) ≤ ‖T‖ := by
  have hrowle (i : U.Index) :
      finiteMaximum (fun j : V.Index => netBilinear U V T (i,j)) ≤
        finiteMaximum (netBilinear U V T) := by
    apply finiteMaximum_le
    intro j
    exact le_finiteMaximum _ (i,j)
  constructor
  · obtain ⟨x,hx,he⟩ := largestExpansion_attained T
    obtain ⟨y,hy,hxy⟩ := U.covers x hx
    let i : U.Index := ⟨y,hy⟩
    have hrow := (netBilinear_row_bounds U V T i).1
    have hm := hrowle i
    have hn := norm_sub_norm_le (T x) (T y)
    have hd := T.le_opNorm (x-y)
    rw [map_sub] at hd
    have hb := mul_le_mul_of_nonneg_left hxy.le (norm_nonneg T)
    have hi : ‖T (i : E)‖=‖T y‖ := rfl
    rw [hi] at hrow
    linarith
  · apply finiteMaximum_le
    rintro ⟨i,j⟩
    have h1 := real_inner_le_norm (j : F) (T (i : E))
    have h2 := T.le_opNorm (i : E)
    rw [V.index_unit j,one_mul] at h1
    rw [U.index_unit i,mul_one] at h2
    exact h1.trans h2

end GradientHessian.GaussianConcentration
