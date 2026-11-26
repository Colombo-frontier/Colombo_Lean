import SecondOrder.RandomFirstOrder
import SecondOrder.BlockDirections

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

abbrev FirstOrderSpace (d T : ℕ) := HomogeneousBlocks (Fin (T+1)) (Point d)

/-- T links, T+1 signed blocks, and the public log-cosh regularizer. -/
def firstOrderChain (Θ : Fin (T+1) → Fin d → Bool) (x : FirstOrderSpace d T) : ℝ :=
  firstOrderBlockPotential (Θ 0) (x 0)+
    (∑ i : Fin T, 2*(firstOrderBlockCompletion (Θ i.castSucc) (x i.castSucc)*
      firstOrderBlockPotential (Θ i.succ) (x i.succ)))+
    ∑ i : Fin (T+1), firstOrderBlockRegularizer (x i)

theorem firstOrderChain_contDiff (Θ : Fin (T+1) → Fin d → Bool) : ContDiff ℝ 3 (firstOrderChain Θ) := by
  apply ContDiff.add
  · apply ContDiff.add
    · exact (firstOrderBlockPotential_contDiff (Θ 0) 3).comp (blockProj (E := Point d) (0:Fin (T+1))).contDiff
    · apply ContDiff.sum
      intro i _
      exact contDiff_const.mul (((firstOrderBlockCompletion_contDiff (Θ i.castSucc)).comp
        (blockProj (E := Point d) i.castSucc).contDiff).mul
        ((firstOrderBlockPotential_contDiff (Θ i.succ) 3).comp (blockProj (E := Point d) i.succ).contDiff))
  · apply ContDiff.sum
    intro i _
    exact (firstOrderBlockRegularizer_contDiff 3).comp (blockProj (E := Point d) i).contDiff

@[simp] theorem firstOrderChain_zero (Θ : Fin (T+1) → Fin d → Bool) : firstOrderChain Θ 0 = -6 := by
  simp [firstOrderChain]

theorem firstOrderChain_lower (Θ : Fin (T+1) → Fin d → Bool) (x : FirstOrderSpace d T) :
    -20*(T+1:ℕ)≤firstOrderChain Θ x := by
  have hh := (firstOrderBlockPotential_range (Θ 0) (x 0)).1
  have hl (i : Fin T) : -20≤2*(firstOrderBlockCompletion (Θ i.castSucc) (x i.castSucc)*
      firstOrderBlockPotential (Θ i.succ) (x i.succ)) := by
    have hb := firstOrderBlockCompletion_mem (Θ i.castSucc) (x i.castSucc)
    have hw := firstOrderBlockPotential_range (Θ i.succ) (x i.succ)
    nlinarith [mul_nonneg hb.1 (show 0≤firstOrderBlockPotential (Θ i.succ) (x i.succ)+10 by linarith)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  have hr := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => firstOrderBlockRegularizer_nonneg (x i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  unfold firstOrderChain
  push_cast
  linarith

theorem firstOrderChain_initial_gap (Θ : Fin (T+1) → Fin d → Bool) (x : FirstOrderSpace d T) :
    firstOrderChain Θ 0-firstOrderChain Θ x≤20*(T+1:ℕ) := by
  rw [firstOrderChain_zero]
  linarith [firstOrderChain_lower Θ x]

/-- The partial derivative of the scalar chain with respect to its j-th encoding. -/
def firstOrderChainCoefficient (Θ : Fin (T+1) → Fin d → Bool) (x : FirstOrderSpace d T)
    (j : Fin (T+1)) : ℝ :=
  (if (0:Fin (T+1))=j then -2 else 0)+
    (∑ i : Fin T, if i.succ=j then -4*firstOrderBlockCompletion (Θ i.castSucc) (x i.castSucc) else 0)+
    ∑ i : Fin T, if i.castSucc=j then
      2*firstOrderBlockPotential (Θ i.succ) (x i.succ)*
        deriv firstOrderCompletion (firstOrderBlockEncoding (Θ i.castSucc) (x i.castSucc)) else 0

theorem firstOrderChainCoefficient_frontier (Θ : Fin (T+1) → Fin d → Bool)
    (x : FirstOrderSpace d T) (j : Fin (T+1))
    (hprior : ∀ i : Fin (T+1), i<j → 1/2<firstOrderBlockEncoding (Θ i) (x i)) :
    firstOrderChainCoefficient Θ x j≤-2 := by
  have ho : (∑ i : Fin T, if i.castSucc=j then
      2*firstOrderBlockPotential (Θ i.succ) (x i.succ)*
        deriv firstOrderCompletion (firstOrderBlockEncoding (Θ i.castSucc) (x i.castSucc)) else 0)≤0 := by
    apply Finset.sum_nonpos
    intro i _
    split_ifs
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) ((firstOrderBlockPotential_range _ _).2.trans (by norm_num)))
        (firstOrderCompletion_deriv_nonneg _)
    · exact le_rfl
  unfold firstOrderChainCoefficient
  cases j using Fin.cases with
  | zero =>
    simp only [if_true,Fin.succ_ne_zero,if_false,Finset.sum_const_zero,add_zero]
    linarith
  | succ k =>
    have hb := firstOrderBlockCompletion_gt_half (Θ k.castSucc)
      (hprior k.castSucc (by change k.val<k.val+1; omega))
    have hs : (∑ i : Fin T, if i.succ=k.succ then -4*firstOrderBlockCompletion (Θ i.castSucc) (x i.castSucc) else 0)=
        -4*firstOrderBlockCompletion (Θ k.castSucc) (x k.castSucc) := by
      simp only [Fin.succ_inj]
      simp
    rw [hs]
    simp only [(Fin.succ_ne_zero k).symm,if_false,zero_add]
    linarith

end
end SecondOrder
