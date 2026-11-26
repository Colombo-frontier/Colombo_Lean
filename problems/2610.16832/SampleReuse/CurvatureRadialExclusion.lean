import SampleReuse.RadialExclusion
import SampleReuse.CurvatureScaleParameters
import SampleReuse.RandomFramePrefixLoss

open SecondOrder
open scoped InnerProductSpace Classical

namespace SampleReuse
noncomputable section

variable {d T : ℕ}

theorem frontier_radial_alignment
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    {x : Point d} (hx : R/2 ≤ ‖x‖) (j : Fin (T+1))
    (hj : |curvatureFrameMap U β x j| ≤ 1) :
    |⟪U (blockUnit j (1:ℝ)),radialUnit x⟫_ℝ| ≤ 2/(β*R) := by
  have hr : 0 < ‖x‖ := (half_pos hR).trans_le hx
  rw [RandomFrame.curvatureFrameMap_coordinate,abs_mul,abs_of_pos hβ] at hj
  rw [radialUnit,real_inner_smul_right,abs_mul,abs_of_pos (inv_pos.mpr hr)]
  calc
    _ ≤ ‖x‖⁻¹*(1/β) := mul_le_mul_of_nonneg_left ((le_div_iff₀ hβ).mpr
      (by simpa only [mul_comm] using hj)) (inv_nonneg.mpr hr.le)
    _ = 1/(β*‖x‖) := by field_simp; ring
    _ ≤ 2/(β*R) := (div_le_div_iff₀ (mul_pos hβ hr) (mul_pos hβ hR)).mpr (by
      nlinarith [mul_le_mul_of_nonneg_left hx hβ.le])

/-- Every stationary output of the actual globalized frame loss is inside the
wall and has completed every coordinate. All geometric budgets are explicit. -/
theorem curvature_radial_sosp_completed
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) {A β b R ε γ : ℝ}
    (hA : 0 ≤ A) (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 < R) (hγ : 0 < γ)
    (hnegative : 8*γ ≤ A*β^2*Real.exp (-(9:ℝ)/4))
    (hwall : 2*b/R ≤ γ)
    (htransverse : 4*(A*β^2*curvatureCoreConstant)/(β*R) ≤ γ)
    (hexterior : ε < b-A*β*(curvatureCoreConstant*Real.sqrt (T+1:ℕ)))
    {x : Point d} (hs : IsSOSP (radialGlobalization (curvatureFrameCore U A β) b R) ε γ x) :
    ‖x‖ < R ∧ ∀ j : Fin (T+1), 1 < |curvatureFrameMap U β x j| := by
  have hf := curvatureFrameCore_contDiff U A β 2
  have hx : ‖x‖ < R := by
    by_contra hn
    have he := radialGlobalization_exterior_gradient (hf.differentiable (by norm_num))
      (b := b) hR (B := A*β*(curvatureCoreConstant*Real.sqrt (T+1:ℕ)))
      (by have hC := curvatureCoreConstant_pos; positivity) (le_of_not_gt hn)
      (curvatureFrameCore_range U hA β x).2 (curvatureFrameCore_gradient_bound U hA hβ.le x)
    linarith [hs.1]
  refine ⟨hx, ?_⟩
  intro k
  by_contra hk
  let S := Finset.univ.filter (fun j : Fin (T+1) => |curvatureFrameMap U β x j| ≤ 1)
  have hS : S.Nonempty := ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_of_not_gt hk⟩⟩
  let j := S.min' hS
  have hj : |curvatureFrameMap U β x j| ≤ 1 :=
    (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  have hp : ∀ i : Fin (T+1), i < j → 1 < |curvatureFrameMap U β x i| := by
    intro i hij
    by_contra hi
    have hi' : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_of_not_gt hi⟩
    exact (not_lt_of_ge (Finset.min'_le S i hi')) hij
  have hh := curvatureFrameCore_frontier U hA β x j hj hp
  have hn : ⟪hessian (curvatureFrameCore U A β) x (U (blockUnit j (1:ℝ))),
      U (blockUnit j (1:ℝ))⟫_ℝ ≤ -8*γ := by linarith [hh.2]
  by_cases hr : ‖x‖ < R/2
  · exact radialGlobalization_core_not_sosp hf b hR hγ hr _ hh.1 hn hs
  · have he : 2*‖hessian (curvatureFrameCore U A β) x‖*
        |⟪U (blockUnit j (1:ℝ)),radialUnit x⟫_ℝ| ≤ γ := by
      calc
        _ ≤ 2*(A*β^2*curvatureCoreConstant)*(2/(β*R)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (curvatureFrameCore_hessian_bound U hA hβ.le x)
              (by norm_num))
            (frontier_radial_alignment U hβ hR (le_of_not_gt hr) j hj)
            (abs_nonneg _) (by have hC := curvatureCoreConstant_pos; positivity)
        _ = 4*(A*β^2*curvatureCoreConstant)/(β*R) := by ring
        _ ≤ γ := htransverse
    exact radialGlobalization_annulus_not_sosp hf hb hR hγ hwall
      (le_of_not_gt hr) hx _ hh.1 hn he hs

theorem curvature_radial_incomplete_not_sosp
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) {A β b R ε γ : ℝ}
    (hA : 0 ≤ A) (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 < R) (hγ : 0 < γ)
    (hnegative : 8*γ ≤ A*β^2*Real.exp (-(9:ℝ)/4))
    (hwall : 2*b/R ≤ γ)
    (htransverse : 4*(A*β^2*curvatureCoreConstant)/(β*R) ≤ γ)
    (hexterior : ε < b-A*β*(curvatureCoreConstant*Real.sqrt (T+1:ℕ)))
    {x : Point d} (j : Fin (T+1)) (hj : |curvatureFrameMap U β x j| ≤ 1/2) :
    ¬ IsSOSP (radialGlobalization (curvatureFrameCore U A β) b R) ε γ x := by
  intro hs
  have hh := (curvature_radial_sosp_completed U hA hβ hb hR hγ
    hnegative hwall htransverse hexterior hs).2 j
  linarith

end
end SampleReuse
