import SecondOrder.FrontierSelectorAlgebra

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

def finZeroExtend {n : ℕ} (a : Fin n → ℝ) (j : ℕ) : ℝ :=
  if hj : j<n then a ⟨j,hj⟩ else 0

@[simp] theorem finZeroExtend_apply {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    finZeroExtend a i = a i := by simp [finZeroExtend, i.isLt]

theorem finZeroExtend_prefix {n : ℕ} (a : Fin n → ℝ) (k j : ℕ) :
    finZeroExtend (fun i => if i.val<k then a i else 0) j =
      if j<k then finZeroExtend a j else 0 := by
  unfold finZeroExtend
  split_ifs <;> simp_all

variable {m T : ℕ}

theorem curvatureNoisePayload_sequence (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (x : CurvatureSpace m T) (j : ℕ) :
    curvatureNoisePayload Θ z j x = curvaturePayloadScale j*
      (finZeroExtend (fun i => sampledPeriodicPotential (z i) (x i)) j-
        finZeroExtend (fun i => periodicBlockPotential (Θ i) (x i)) j) := by
  unfold curvatureNoisePayload finZeroExtend
  split_ifs <;> simp only [periodicBlockNoise, sub_self, mul_zero]

theorem curvatureGatedChain_prefix (Θ : Fin (T+1) → BalancedVector m)
    (k : ℕ) (hk : k≤T) (x : CurvatureSpace m T) :
    curvatureGatedChain Θ (prefixGates (fun i => periodicCompletion (Θ i)) k) x =
      finZeroExtend (fun i => periodicBlockPotential (Θ i) (x i)) 0+
      ∑ j ∈ Finset.range k, 2*(finZeroExtend (fun i => periodicCompletion (Θ i) (x i)) j*
        finZeroExtend (fun i => periodicBlockPotential (Θ i) (x i)) (j+1)) := by
  let a : ℕ → ℝ := fun j => 2*(finZeroExtend (fun i => periodicCompletion (Θ i) (x i)) j*
    finZeroExtend (fun i => periodicBlockPotential (Θ i) (x i)) (j+1))
  have hs : (∑ i : Fin T, 2*(prefixGates (fun j => periodicCompletion (Θ j)) k i.castSucc
      (x i.castSucc)*periodicBlockPotential (Θ i.succ) (x i.succ))) =
      ∑ j ∈ Finset.range T, if j<k then a j else 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hg : finZeroExtend (fun j => periodicCompletion (Θ j) (x j)) i.val =
        periodicCompletion (Θ i.castSucc) (x i.castSucc) := finZeroExtend_apply _ i.castSucc
    have hw : finZeroExtend (fun j => periodicBlockPotential (Θ j) (x j)) (i.val+1) =
        periodicBlockPotential (Θ i.succ) (x i.succ) := finZeroExtend_apply _ i.succ
    simp only [prefixGates, Fin.coe_castSucc, a, hg, hw]
    split_ifs <;> simp
  unfold curvatureGatedChain
  rw [hs, sum_range_prefix a hk]
  have h0 : finZeroExtend (fun i => periodicBlockPotential (Θ i) (x i)) 0 =
      periodicBlockPotential (Θ 0) (x 0) := finZeroExtend_apply _ (0 : Fin (T+1))
  rw [h0]

/-- An exact identity of scalar functions, not just an identity at the query
point. It exposes the cancellation of the fresh hidden block. -/
theorem curvatureTruncatedLoss_frontier_formula (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (k : ℕ) (hk : k≤T) (x : CurvatureSpace m T) :
    curvatureTruncatedLoss Θ z k x =
      frontierLossValue (finZeroExtend (fun i => periodicCompletion (Θ i) (x i)))
        (finZeroExtend (fun i => periodicBlockPotential (Θ i) (x i)))
        (finZeroExtend (fun i => sampledPeriodicPotential (z i) (x i))) k := by
  unfold curvatureTruncatedLoss
  rw [curvatureGatedChain_prefix Θ k hk x]
  unfold reverseBlockSelector
  have hb : (fun j => if hj : j<T+1 then
      prefixGates (fun i => periodicCompletion (Θ i)) k ⟨j,hj⟩ (x ⟨j,hj⟩) else 0) =
      (fun j => if j<k then finZeroExtend (fun i => periodicCompletion (Θ i) (x i)) j else 0) := by
    funext j
    simp only [prefixGates, finZeroExtend]
    split_ifs <;> simp_all
  rw [hb, reverseSelectorValue_prefix _ _ (by omega : k≤T+1)]
  simp only [frontierLossValue, curvatureNoisePayload_sequence]

end
end SecondOrder
