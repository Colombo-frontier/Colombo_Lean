import SecondOrder.ConservativeChain

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {T : ℕ} {E : Fin (T+1) → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

theorem conservativePayload_sequence (W S : (i : Fin (T+1)) → E i → ℝ)
    (x : PiLp 2 E) (j : ℕ) :
    conservativePayload W S j x = curvaturePayloadScale j*
      (finZeroExtend (fun i => S i (x i)) j-finZeroExtend (fun i => W i (x i)) j) := by
  unfold conservativePayload finZeroExtend
  split_ifs <;> simp only [sub_self,mul_zero]

theorem conservativePopulation_prefix (reg : PiLp 2 E → ℝ)
    (W p : (i : Fin (T+1)) → E i → ℝ) (k : ℕ) (hk : k ≤ T) (x : PiLp 2 E) :
    conservativePopulation reg W (dependentPrefixGates p k) x =
      reg x+finZeroExtend (fun i => W i (x i)) 0+
      ∑ j ∈ Finset.range k, 2*(finZeroExtend (fun i => p i (x i)) j*
        finZeroExtend (fun i => W i (x i)) (j+1)) := by
  let a : ℕ → ℝ := fun j => 2*(finZeroExtend (fun i => p i (x i)) j*
    finZeroExtend (fun i => W i (x i)) (j+1))
  have hs : (∑ i : Fin T, 2*(dependentPrefixGates p k i.castSucc (x i.castSucc)*W i.succ (x i.succ))) =
      ∑ j ∈ Finset.range T, if j<k then a j else 0 := by
    rw [←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hg : finZeroExtend (fun j => p j (x j)) i.val = p i.castSucc (x i.castSucc) :=
      finZeroExtend_apply _ i.castSucc
    have hw : finZeroExtend (fun j => W j (x j)) (i.val+1) = W i.succ (x i.succ) :=
      finZeroExtend_apply _ i.succ
    simp only [dependentPrefixGates,Fin.coe_castSucc,a,hg,hw]
    split_ifs <;> simp
  unfold conservativePopulation
  rw [hs,sum_range_prefix a hk]
  have h0 : finZeroExtend (fun i => W i (x i)) 0=W 0 (x 0) :=
    finZeroExtend_apply _ (0 : Fin (T+1))
  rw [h0]

/-- The general truncated conservative loss equals the finite scalar frontier
expression at every point, with the public regularizer unchanged. -/
theorem conservativeTruncatedChain_frontier_formula (reg : PiLp 2 E → ℝ)
    (W S p : (i : Fin (T+1)) → E i → ℝ) (k : ℕ) (hk : k ≤ T) (x : PiLp 2 E) :
    conservativeTruncatedChain reg W S p k x =
      reg x+frontierLossValue (finZeroExtend (fun i => p i (x i)))
        (finZeroExtend (fun i => W i (x i))) (finZeroExtend (fun i => S i (x i))) k := by
  unfold conservativeTruncatedChain conservativeChain
  rw [conservativePopulation_prefix reg W p k hk x]
  unfold dependentReverseSelector
  have hb : (fun j => if hj : j<T+1 then dependentPrefixGates p k ⟨j,hj⟩ (x ⟨j,hj⟩) else 0) =
      (fun j => if j<k then finZeroExtend (fun i => p i (x i)) j else 0) := by
    funext j
    simp only [dependentPrefixGates,finZeroExtend]
    split_ifs <;> simp_all
  rw [hb,reverseSelectorValue_prefix _ _ (by omega : k ≤ T+1)]
  simp only [frontierLossValue,conservativePayload_sequence]
  ring

/-- The entire scalar function, hence every derivative, is independent of
hidden potentials and gates at and beyond k. Only sampled potentials up to
and including k survive the last-block cancellation. -/
theorem conservativeTruncatedChain_prefix_invariant (reg : PiLp 2 E → ℝ)
    (W W' S S' p p' : (i : Fin (T+1)) → E i → ℝ) {k : ℕ} (hk : k ≤ T)
    (hW : ∀ i, i.val<k → W i=W' i) (hp : ∀ i, i.val<k → p i=p' i)
    (hS : ∀ i, i.val ≤ k → S i=S' i) :
    conservativeTruncatedChain reg W S p k = conservativeTruncatedChain reg W' S' p' k := by
  funext x
  rw [conservativeTruncatedChain_frontier_formula reg W S p k hk,
    conservativeTruncatedChain_frontier_formula reg W' S' p' k hk]
  congr 1
  apply frontierLossValue_congr
  · intro j hj
    have hjn : j<T+1 := by omega
    simp only [finZeroExtend,dif_pos hjn,hp ⟨j,hjn⟩ hj]
  · intro j hj
    have hjn : j<T+1 := by omega
    simp only [finZeroExtend,dif_pos hjn,hW ⟨j,hjn⟩ hj]
  · intro j hj
    have hjn : j<T+1 := by omega
    simp only [finZeroExtend,dif_pos hjn,hS ⟨j,hjn⟩ hj]

end
end SecondOrder
