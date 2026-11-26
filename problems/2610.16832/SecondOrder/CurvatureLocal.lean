import SecondOrder.CurvatureNegative
import SecondOrder.PeriodicJets
import SecondOrder.ChainLocality

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

def chainLeft (i : Fin T) : chainSupport i := ⟨i.castSucc, by simp [chainSupport]⟩
def chainRight (i : Fin T) : chainSupport i := ⟨i.succ, by simp [chainSupport]⟩

def curvatureLocalLink (Θ : Fin (T+1) → BalancedVector m) (i : Fin T)
    (y : LocalBlockSpace (fun _ : Fin (T+1) => Point (2*m)) (chainSupport i)) : ℝ :=
  periodicCompletion (Θ i.castSucc) (y (chainLeft i))*periodicBlockPotential (Θ i.succ) (y (chainRight i))

theorem curvatureLocalLink_contDiff (Θ : Fin (T+1) → BalancedVector m) (i : Fin T) :
    ContDiff ℝ 3 (curvatureLocalLink Θ i) :=
  ((periodicCompletion_contDiff (Θ i.castSucc)).comp
    (blockProj (E := Point (2*m)) (chainLeft i)).contDiff).mul
    ((periodicBlockPotential_contDiff (Θ i.succ) 3).comp
    (blockProj (E := Point (2*m)) (chainRight i)).contDiff)

theorem curvatureLocalLink_bounds (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m) (i : Fin T)
    (y : LocalBlockSpace (fun _ : Fin (T+1) => Point (2*m)) (chainSupport i)) :
    ‖iteratedFDeriv ℝ 2 (curvatureLocalLink Θ i) y‖ ≤ 8*curvatureJetConstant^2/((2*m:ℕ):ℝ) ∧
    ‖iteratedFDeriv ℝ 3 (curvatureLocalLink Θ i) y‖ ≤ 8*curvatureJetConstant^2/((2*m:ℕ):ℝ) := by
  let L := blockProj (E := Point (2*m)) (chainLeft i)
  let R := blockProj (E := Point (2*m)) (chainRight i)
  have hf := (periodicCompletion_contDiff (Θ i.castSucc)).comp L.contDiff
  have hg := (periodicBlockPotential_contDiff (Θ i.succ) 3).comp R.contDiff
  have hjf := (periodicCompletion_dimensionJet (Θ i.castSucc) hm (L y)).comp_linear
    (periodicCompletion_contDiff (Θ i.castSucc)) L (blockProj_norm_le_one _) y
  have hjg := (periodicBlockPotential_dimensionJet (Θ i.succ) hm (R y)).comp_linear
    (periodicBlockPotential_contDiff (Θ i.succ) 3) R (blockProj_norm_le_one _) y
  have hD : (1:ℝ) ≤ (2*m:ℕ) := by exact_mod_cast (by omega : 1 ≤ 2*m)
  exact ⟨dimensionJet_product_second hf hg curvatureJetConstant_ge_one hD y hjf hjg,
    dimensionJet_product_third hf hg curvatureJetConstant_ge_one hD y hjf hjg⟩

theorem curvatureChain_eq_local (Θ : Fin (T+1) → BalancedVector m) :
    curvatureChain Θ = fun x => periodicBlockPotential (Θ 0) (x 0)+
      2*localObjective (fun _ : Fin (T+1) => Point (2*m)) chainSupport (curvatureLocalLink Θ) x := by
  funext x
  unfold curvatureChain localObjective curvatureLocalLink
  rw [Finset.mul_sum]
  rfl

/-- Bounded overlap removes the chain length from both derivative estimates. -/
theorem curvatureChain_iterated_bound (Θ : Fin (T+1) → BalancedVector m) (hm : 0 < m)
    (k : ℕ) (hk : k=2 ∨ k=3) (x : CurvatureSpace m T) :
    ‖iteratedFDeriv ℝ k (curvatureChain Θ) x‖ ≤ 33*curvatureJetConstant^2/((2*m:ℕ):ℝ) := by
  let head : CurvatureSpace m T → ℝ := fun y => periodicBlockPotential (Θ 0) (y 0)
  let links := localObjective (fun _ : Fin (T+1) => Point (2*m)) chainSupport (curvatureLocalLink Θ)
  have hk3 : (k:WithTop ℕ∞) ≤ 3 := by rcases hk with rfl | rfl <;> decide
  have hh3 : ContDiff ℝ 3 head := (periodicBlockPotential_contDiff (Θ 0) 3).comp
    (blockProj (E := Point (2*m)) (0 : Fin (T+1))).contDiff
  have hl3 : ContDiff ℝ 3 links := localObjective_contDiff _ _ _ (curvatureLocalLink_contDiff Θ)
  have hh : ‖iteratedFDeriv ℝ k head x‖ ≤ curvatureJetConstant/((2*m:ℕ):ℝ) := by
    have hj := (periodicBlockPotential_dimensionJet (Θ 0) hm (x 0)).comp_linear
      (periodicBlockPotential_contDiff (Θ 0) 3)
      (blockProj (E := Point (2*m)) (0 : Fin (T+1))) (blockProj_norm_le_one _) x
    rcases hk with rfl | rfl
    · exact hj.2.2.1
    · exact hj.2.2.2
  have hl : ‖iteratedFDeriv ℝ k links x‖ ≤ 16*curvatureJetConstant^2/((2*m:ℕ):ℝ) := by
    rcases hk with rfl | rfl
    · have hh := chainObjective_second_bound (fun _ : Fin (T+1) => Point (2*m)) (curvatureLocalLink Θ)
        (fun i => (curvatureLocalLink_contDiff Θ i).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide))
        (by positivity : 0 ≤ 8*curvatureJetConstant^2/((2*m:ℕ):ℝ))
        (fun i y => (curvatureLocalLink_bounds Θ hm i y).1) x
      convert hh using 1 <;> ring
    · have hh := chainObjective_third_bound (fun _ : Fin (T+1) => Point (2*m)) (curvatureLocalLink Θ)
        (curvatureLocalLink_contDiff Θ)
        (by positivity : 0 ≤ 8*curvatureJetConstant^2/((2*m:ℕ):ℝ))
        (fun i y => (curvatureLocalLink_bounds Θ hm i y).2) x
      convert hh using 1 <;> ring
  rw [curvatureChain_eq_local]
  change ‖iteratedFDeriv ℝ k (fun y => head y+(2:ℝ) • links y) x‖ ≤ _
  rw [iteratedFDeriv_add_apply' (hh3.of_le hk3).contDiffAt ((hl3.of_le hk3).const_smul 2).contDiffAt,
    iteratedFDeriv_const_smul_apply' (hl3.of_le hk3).contDiffAt]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k head x‖+‖(2:ℝ) • iteratedFDeriv ℝ k links x‖ := norm_add_le _ _
    _ = ‖iteratedFDeriv ℝ k head x‖+2*‖iteratedFDeriv ℝ k links x‖ := by
      rw [norm_smul]; norm_num
    _ ≤ curvatureJetConstant/((2*m:ℕ):ℝ)+2*(16*curvatureJetConstant^2/((2*m:ℕ):ℝ)) :=
      add_le_add hh (mul_le_mul_of_nonneg_left hl (by norm_num))
    _ ≤ _ := by
      have hc : curvatureJetConstant ≤ curvatureJetConstant^2 := by
        have hc1 := curvatureJetConstant_ge_one
        nlinarith
      have hdiv := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) (2*m))
      simp only [div_eq_mul_inv] at hdiv ⊢
      nlinarith

end
end SecondOrder
