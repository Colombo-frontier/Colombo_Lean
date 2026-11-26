import SecondOrder.FirstOrderTruncation
import SecondOrder.CurvatureFrontierFormula

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

theorem firstOrderNoisePayload_sequence (Θ : Fin (T+1) → Fin d → Bool) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (x : FirstOrderSpace d T) (j : ℕ) :
    firstOrderNoisePayload Θ z j x=firstOrderPayloadScale j*
      (finZeroExtend (fun i => sampledFirstOrderPotential (z i) (x i)) j-
        finZeroExtend (fun i => firstOrderBlockPotential (Θ i) (x i)) j) := by
  unfold firstOrderNoisePayload finZeroExtend
  split_ifs <;> simp only [firstOrderBlockNoise,sub_self,mul_zero]

theorem firstOrderGatedChain_prefix (Θ : Fin (T+1) → Fin d → Bool)
    (k : ℕ) (hk : k≤T) (x : FirstOrderSpace d T) :
    firstOrderGatedChain Θ (prefixGates (fun i => firstOrderBlockCompletion (Θ i)) k) x=
      finZeroExtend (fun i => firstOrderBlockPotential (Θ i) (x i)) 0+
      (∑ j ∈ Finset.range k, 2*(finZeroExtend (fun i => firstOrderBlockCompletion (Θ i) (x i)) j*
        finZeroExtend (fun i => firstOrderBlockPotential (Θ i) (x i)) (j+1)))+
      ∑ i : Fin (T+1), firstOrderBlockRegularizer (x i) := by
  let a : ℕ → ℝ := fun j => 2*(finZeroExtend (fun i => firstOrderBlockCompletion (Θ i) (x i)) j*
    finZeroExtend (fun i => firstOrderBlockPotential (Θ i) (x i)) (j+1))
  have hs : (∑ i : Fin T, 2*(prefixGates (fun j => firstOrderBlockCompletion (Θ j)) k i.castSucc
      (x i.castSucc)*firstOrderBlockPotential (Θ i.succ) (x i.succ)))=
      ∑ j ∈ Finset.range T, if j<k then a j else 0 := by
    rw [←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hg : finZeroExtend (fun j => firstOrderBlockCompletion (Θ j) (x j)) i.val=
        firstOrderBlockCompletion (Θ i.castSucc) (x i.castSucc) := finZeroExtend_apply _ i.castSucc
    have hw : finZeroExtend (fun j => firstOrderBlockPotential (Θ j) (x j)) (i.val+1)=
        firstOrderBlockPotential (Θ i.succ) (x i.succ) := finZeroExtend_apply _ i.succ
    simp only [prefixGates,Fin.coe_castSucc,a,hg,hw]
    split_ifs <;> simp
  unfold firstOrderGatedChain
  rw [hs,sum_range_prefix a hk]
  have h0 : finZeroExtend (fun i => firstOrderBlockPotential (Θ i) (x i)) 0=
      firstOrderBlockPotential (Θ 0) (x 0) := finZeroExtend_apply _ (0:Fin (T+1))
  rw [h0]

/-- The fresh hidden potential cancels as a whole scalar function. The
regularizer on all blocks survives, but contains no hidden signs. -/
theorem firstOrderTruncatedLoss_frontier_formula (Θ : Fin (T+1) → Fin d → Bool) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (k : ℕ) (hk : k≤T) (x : FirstOrderSpace d T) :
    firstOrderTruncatedLoss Θ z k x=
      frontierLossValue (finZeroExtend (fun i => firstOrderBlockCompletion (Θ i) (x i)))
        (finZeroExtend (fun i => firstOrderBlockPotential (Θ i) (x i)))
        (finZeroExtend (fun i => sampledFirstOrderPotential (z i) (x i))) k+
      ∑ i : Fin (T+1), firstOrderBlockRegularizer (x i) := by
  unfold firstOrderTruncatedLoss
  rw [firstOrderGatedChain_prefix Θ k hk x]
  unfold reverseBlockSelector
  have hb : (fun j => if hj : j<T+1 then
      prefixGates (fun i => firstOrderBlockCompletion (Θ i)) k ⟨j,hj⟩ (x ⟨j,hj⟩) else 0)=
      (fun j => if j<k then finZeroExtend (fun i => firstOrderBlockCompletion (Θ i) (x i)) j else 0) := by
    funext j
    simp only [prefixGates,finZeroExtend]
    split_ifs <;> simp_all
  rw [hb,reverseSelectorValue_prefix _ _ (by omega : k≤T+1)]
  simp only [frontierLossValue,firstOrderNoisePayload_sequence,firstOrderPayloadScale,curvaturePayloadScale]
  ring

end
end SecondOrder
