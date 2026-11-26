import SecondOrder.CurvatureChain

open scoped BigOperators Classical InnerProductSpace

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

/-- The outgoing link is nonpositive in a direction with nonnegative gate curvature. -/
theorem curvatureChain_second_block_le (Θ : Fin (T+1) → BalancedVector m)
    (x : CurvatureSpace m T) (j : Fin (T+1)) (v : Point (2*m))
    (hb : 0 ≤ secondQuadratic (periodicCompletion (Θ j)) (x j) v) :
    secondQuadratic (curvatureChain Θ) x (blockUnit j v) ≤
      (if (0 : Fin (T+1))=j then secondQuadratic (periodicBlockPotential (Θ 0)) (x 0) v else 0)+
      ∑ i : Fin T, 2*(if i.succ=j then periodicCompletion (Θ i.castSucc) (x i.castSucc)*
        secondQuadratic (periodicBlockPotential (Θ i.succ)) (x i.succ) v else 0) := by
  rw [curvatureChain_second_block]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  have ho : (if i.castSucc=j then periodicBlockPotential (Θ i.succ) (x i.succ)*
      secondQuadratic (periodicCompletion (Θ i.castSucc)) (x i.castSucc) v else 0) ≤ 0 := by
    split_ifs with hi
    · rw [hi]
      exact mul_nonpos_of_nonpos_of_nonneg (periodicBlockPotential_nonpos _ _) hb
    · exact le_rfl
  linarith

/-- A frontier block supplies a unit direction in the full Euclidean block space. -/
theorem curvatureChain_frontier_negative (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0 < m) (x : CurvatureSpace m T) (j : Fin (T+1))
    (hj : ‖periodicMean (x j) (Θ j)‖ ≤ 1/4)
    (hprior : ∀ i : Fin (T+1), i < j → 1/4 < ‖periodicMean (x i) (Θ i)‖) :
    ∃ v : CurvatureSpace m T, ‖v‖ = 1 ∧
      ⟪fderiv ℝ (gradient (curvatureChain Θ)) x v,v⟫_ℝ ≤ -1/(4*((2*m:ℕ):ℝ)) := by
  obtain ⟨v, hv, hq⟩ := periodicBlockPotential_negative (Θ j) (x j) hm hj
  have he : secondQuadratic (periodicBlockPotential (Θ j)) (x j) v ≤ -1/(4*((2*m:ℕ):ℝ)) := by
    simpa only [secondQuadratic_eq_inner (periodicBlockPotential_contDiff (Θ j) 2), hessian] using hq
  have hn : -1/(4*((2*m:ℕ):ℝ)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have hgate := periodicCompletion_nonneg_curvature (Θ j) (x j) v hj (he.trans hn)
  have hg := curvatureChain_second_block_le Θ x j v hgate
  refine ⟨blockUnit j v, by simpa using hv, ?_⟩
  rw [← secondQuadratic_eq_inner ((curvatureChain_contDiff Θ).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide))]
  cases j using Fin.cases with
  | zero =>
    simp only [if_true, Fin.succ_ne_zero, if_false, mul_zero, Finset.sum_const_zero, add_zero] at hg
    exact hg.trans he
  | succ k =>
    have hb := periodicCompletion_gt_half (Θ k.castSucc) (x k.castSucc)
      (hprior k.castSucc (by change k.val < k.val+1; omega))
    have hs : (∑ i : Fin T, 2*(if i.succ=k.succ then periodicCompletion (Θ i.castSucc) (x i.castSucc)*
        secondQuadratic (periodicBlockPotential (Θ i.succ)) (x i.succ) v else 0)) =
        2*(periodicCompletion (Θ k.castSucc) (x k.castSucc)*
        secondQuadratic (periodicBlockPotential (Θ k.succ)) (x k.succ) v) := by
      simp only [Fin.succ_inj, mul_ite, mul_zero]
      simp
    rw [hs] at hg
    simp only [(Fin.succ_ne_zero k).symm, if_false, zero_add] at hg
    have hc : 2*(periodicCompletion (Θ k.castSucc) (x k.castSucc)*
        secondQuadratic (periodicBlockPotential (Θ k.succ)) (x k.succ) v) ≤
        secondQuadratic (periodicBlockPotential (Θ k.succ)) (x k.succ) v := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2*periodicCompletion (Θ k.castSucc) (x k.castSucc)-1) (he.trans hn)]
    exact (hg.trans hc).trans he

/-- The negative-curvature assertion of the capped-gate chain lemma. -/
theorem curvatureChain_negative (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (x : CurvatureSpace m T) (h : ∃ j, ‖periodicMean (x j) (Θ j)‖ ≤ 1/4) :
    ∃ v : CurvatureSpace m T, ‖v‖ = 1 ∧
      ⟪fderiv ℝ (gradient (curvatureChain Θ)) x v,v⟫_ℝ ≤ -1/(4*((2*m:ℕ):ℝ)) := by
  classical
  let S := Finset.univ.filter (fun j : Fin (T+1) => ‖periodicMean (x j) (Θ j)‖ ≤ 1/4)
  have hs : S.Nonempty := by
    obtain ⟨j, hj⟩ := h
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let j := S.min' hs
  have hj : ‖periodicMean (x j) (Θ j)‖ ≤ 1/4 :=
    (Finset.mem_filter.mp (Finset.min'_mem S hs)).2
  apply curvatureChain_frontier_negative Θ hm x j hj
  intro i hij
  by_contra hi
  have hi' : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hi⟩
  have hle : j ≤ i := Finset.min'_le S i hi'
  exact (not_lt_of_ge hle) hij

end
end SecondOrder
