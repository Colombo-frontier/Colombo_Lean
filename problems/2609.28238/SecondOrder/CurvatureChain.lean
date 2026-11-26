import SecondOrder.CompletionCurvature
import SecondOrder.BlockDirections

open scoped BigOperators Classical InnerProductSpace

namespace SecondOrder
noncomputable section
variable {m T : ℕ}

abbrev CurvatureSpace (m T : ℕ) := HomogeneousBlocks (Fin (T+1)) (Point (2*m))

/-- The manuscript's chain, with T+1 blocks and T neighboring links. -/
def curvatureChain (Θ : Fin (T+1) → BalancedVector m) (x : CurvatureSpace m T) : ℝ :=
  periodicBlockPotential (Θ 0) (x 0)+
    ∑ i : Fin T, 2*(periodicCompletion (Θ i.castSucc) (x i.castSucc)*
      periodicBlockPotential (Θ i.succ) (x i.succ))

theorem curvatureChain_contDiff (Θ : Fin (T+1) → BalancedVector m) : ContDiff ℝ 3 (curvatureChain Θ) := by
  apply ContDiff.add
  · exact (periodicBlockPotential_contDiff (Θ 0) 3).comp
      (blockProj (E := Point (2*m)) (0 : Fin (T+1))).contDiff
  · apply ContDiff.sum
    intro i _
    exact contDiff_const.mul (((periodicCompletion_contDiff (Θ i.castSucc)).comp
      (blockProj (E := Point (2*m)) i.castSucc).contDiff).mul
      ((periodicBlockPotential_contDiff (Θ i.succ) 3).comp
      (blockProj (E := Point (2*m)) i.succ).contDiff))

theorem curvatureChain_zero (Θ : Fin (T+1) → BalancedVector m) : curvatureChain Θ 0 = 0 := by
  simp [curvatureChain, periodicBlockPotential_zero, periodicCompletion_zero]

theorem curvatureChain_range (Θ : Fin (T+1) → BalancedVector m) (x : CurvatureSpace m T) :
    -(T+1:ℕ) ≤ curvatureChain Θ x ∧ curvatureChain Θ x ≤ 0 := by
  have hh := periodicPotential_abs_le (x 0) (Θ 0)
  change |periodicBlockPotential (Θ 0) (x 0)| ≤ 1/2 at hh
  have h0 := periodicBlockPotential_nonpos (Θ 0) (x 0)
  have ht (i : Fin T) :
      -(1:ℝ) ≤ 2*(periodicCompletion (Θ i.castSucc) (x i.castSucc)*
        periodicBlockPotential (Θ i.succ) (x i.succ)) ∧
      2*(periodicCompletion (Θ i.castSucc) (x i.castSucc)*
        periodicBlockPotential (Θ i.succ) (x i.succ)) ≤ 0 := by
    have hb := periodicCompletion_mem (Θ i.castSucc) (x i.castSucc)
    have hw := periodicPotential_abs_le (x i.succ) (Θ i.succ)
    change |periodicBlockPotential (Θ i.succ) (x i.succ)| ≤ 1/2 at hw
    have hn := periodicBlockPotential_nonpos (Θ i.succ) (x i.succ)
    constructor
    · nlinarith [abs_le.mp hw, mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hb.2) hn]
    · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (mul_nonpos_of_nonneg_of_nonpos hb.1 hn)
  have hlo := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (ht i).1)
  have hhi := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (ht i).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg,
    mul_one, Finset.sum_const_zero] at hlo hhi
  unfold curvatureChain
  push_cast
  constructor <;> linarith [abs_le.mp hh]

theorem curvatureChain_second_block (Θ : Fin (T+1) → BalancedVector m)
    (x : CurvatureSpace m T) (j : Fin (T+1)) (v : Point (2*m)) :
    secondQuadratic (curvatureChain Θ) x (blockUnit j v) =
      (if (0 : Fin (T+1))=j then secondQuadratic (periodicBlockPotential (Θ 0)) (x 0) v else 0)+
      ∑ i : Fin T, 2*((if i.castSucc=j then periodicBlockPotential (Θ i.succ) (x i.succ)*
        secondQuadratic (periodicCompletion (Θ i.castSucc)) (x i.castSucc) v else 0)+
      (if i.succ=j then periodicCompletion (Θ i.castSucc) (x i.castSucc)*
        secondQuadratic (periodicBlockPotential (Θ i.succ)) (x i.succ) v else 0)) := by
  have hW (i : Fin (T+1)) : ContDiff ℝ 2 (periodicBlockPotential (Θ i)) := periodicBlockPotential_contDiff _ 2
  have hb (i : Fin (T+1)) : ContDiff ℝ 2 (periodicCompletion (Θ i)) :=
    (periodicCompletion_contDiff _).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide)
  have hhead : ContDiff ℝ 2 (fun y : CurvatureSpace m T => periodicBlockPotential (Θ 0) (y 0)) :=
    (hW 0).comp (blockProj (E := Point (2*m)) (0 : Fin (T+1))).contDiff
  have hlink (i : Fin T) : ContDiff ℝ 2 (fun y : CurvatureSpace m T =>
      periodicCompletion (Θ i.castSucc) (y i.castSucc)*periodicBlockPotential (Θ i.succ) (y i.succ)) :=
    ((hb _).comp (blockProj (E := Point (2*m)) i.castSucc).contDiff).mul
      ((hW _).comp (blockProj (E := Point (2*m)) i.succ).contDiff)
  unfold curvatureChain
  rw [secondQuadratic_add hhead (ContDiff.sum (fun i _ => contDiff_const.mul (hlink i))),
    secondQuadratic_block (hW 0), secondQuadratic_sum]
  · congr 1
    · split_ifs <;> rfl
    · apply Finset.sum_congr rfl
      intro i _
      have hne : i.castSucc ≠ i.succ := by
        intro h
        have hh := congrArg Fin.val h
        change i.val = i.val+1 at hh
        omega
      rw [secondQuadratic_const_mul (hlink i),
        secondQuadratic_two_blocks (hb _) (hW _) i.castSucc i.succ j hne x v]
      split_ifs <;> rfl
  · intro i
    exact contDiff_const.mul (hlink i)

end
end SecondOrder
