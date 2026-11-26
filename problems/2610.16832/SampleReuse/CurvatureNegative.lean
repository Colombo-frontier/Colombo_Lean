import SampleReuse.CurvatureChain

open SecondOrder
open scoped BigOperators InnerProductSpace Classical

namespace SampleReuse
noncomputable section

theorem deterministicCurvatureChain_frontier (T : ℕ) (x : Point (T+1)) (j : Fin (T+1))
    (hj : |x j| ≤ 1) (hprior : ∀ i : Fin (T+1), i < j → 1 < |x i|) :
    secondQuadratic (deterministicCurvatureChain T) x (blockUnit j (1:ℝ)) ≤
      -Real.exp (-(9:ℝ)/4) := by
  have hout : (∑ i : Fin T, if i.castSucc = j then curvaturePotential (x i.succ)*
      deriv (deriv curvatureGate) (x i.castSucc) else 0) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    split_ifs with he
    · rw [he]
      exact mul_nonpos_of_nonpos_of_nonneg (curvaturePotential_range _).2
        (curvatureGate_convex_region hj)
    · exact le_rfl
  rw [deterministicCurvatureChain_diagonal, Finset.sum_add_distrib]
  cases j using Fin.cases with
  | zero =>
    simp only [if_true, Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero]
    have hh := curvature_link_negative (p := 1) (by norm_num) hj 0
    rw [curvaturePotential_zero, mul_zero, add_zero] at hh
    linarith
  | succ k =>
    have hin : (∑ i : Fin T, if i.succ = k.succ then curvatureGate (x i.castSucc)*
        deriv (deriv curvaturePotential) (x i.succ) else 0) =
        curvatureGate (x k.castSucc)*deriv (deriv curvaturePotential) (x k.succ) := by
      simp only [Fin.succ_inj]
      simp
    rw [hin]
    simp only [(Fin.succ_ne_zero k).symm, if_false, mul_zero, zero_add]
    have hh := curvature_link_negative (hprior k.castSucc (by
      change k.val < k.val+1
      omega)).le hj 0
    rw [curvaturePotential_zero, mul_zero, add_zero] at hh
    linarith

/-- The genuine Hessian has a unit direction of curvature at most -exp(-9/4)
whenever any coordinate is incomplete (the curvature part of lem:chain). -/
theorem deterministicCurvatureChain_negative (T : ℕ) (x : Point (T+1))
    (h : ∃ j, |x j| ≤ 1) : ∃ v : Point (T+1), ‖v‖ = 1 ∧
      ⟪hessian (deterministicCurvatureChain T) x v,v⟫_ℝ ≤ -Real.exp (-(9:ℝ)/4) := by
  let S := Finset.univ.filter (fun j : Fin (T+1) => |x j| ≤ 1)
  have hs : S.Nonempty := by
    obtain ⟨j, hj⟩ := h
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let j := S.min' hs
  have hj : |x j| ≤ 1 := (Finset.mem_filter.mp (Finset.min'_mem S hs)).2
  have hp : ∀ i : Fin (T+1), i < j → 1 < |x i| := by
    intro i hij
    by_contra hi
    have hi' : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hi⟩
    exact (not_lt_of_ge (Finset.min'_le S i hi')) hij
  refine ⟨blockUnit j (1:ℝ), by simp, ?_⟩
  have hh := deterministicCurvatureChain_frontier T x j hj hp
  rwa [secondQuadratic_eq_inner (deterministicCurvatureChain_contDiff T 2)] at hh

end
end SampleReuse
