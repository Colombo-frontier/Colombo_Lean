import GradientHessian.SelectorChainRule

/-! Fixed-order partition identities for the selector chain rule. -/

namespace GradientHessian.SelectorPartitions
open Classical
open scoped BigOperators
noncomputable section

theorem sum_partSize {n : ℕ} (c : OrderedFinpartition n) : ∑ l, c.partSize l = n := by
  have h := Fintype.card_congr c.equivSigma
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

theorem big_part_singleton {n : ℕ} (hn : n ≤ 3) (c : OrderedFinpartition n)
    (l : Fin c.length) (hl : 3 ≤ c.partSize l) : n = 3 ∧ c.length = 1 := by
  have hn3 : n = 3 := by have h := c.partSize_le l; omega
  refine ⟨hn3, ?_⟩
  have hp : c.partSize l = 3 := by have h := c.partSize_le l; omega
  have hs := sum_partSize c
  have herase : ∑ j ∈ Finset.univ.erase l, c.partSize j = 0 := by
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin c.length))
      c.partSize (Finset.mem_univ l)
    omega
  have he : (Finset.univ.erase l : Finset (Fin c.length)) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro j hj
    have hle : c.partSize j ≤ ∑ k ∈ Finset.univ.erase l, c.partSize k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
    have hjpos := c.partSize_pos j
    omega
  have hc := congrArg Finset.card he
  simp only [Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ,
    Fintype.card_fin, Finset.card_empty] at hc
  have hlpos : 0 < c.length := Nat.zero_lt_of_lt l.isLt
  omega

theorem singleton_partSize {n : ℕ} (c : OrderedFinpartition n) (hc : c.length = 1)
    (l : Fin c.length) : c.partSize l = n := by
  haveI : Subsingleton (Fin c.length) := by rw [hc]; infer_instance
  simpa only [Fintype.sum_subsingleton _ l] using sum_partSize c

theorem singleton_prod {n : ℕ} (c : OrderedFinpartition n) (hc : c.length = 1)
    (l : Fin c.length) (a : Fin n → ℝ) :
    (∏ j, a (c.emb l j)) = ∏ j, a j := by
  haveI : Subsingleton (Fin c.length) := by rw [hc]; infer_instance
  simpa only [Fintype.prod_subsingleton _ l] using c.prod_sigma_eq_prod a

theorem partition_scale_product {n : ℕ} (c : OrderedFinpartition n) (C R : ℝ) (a : Fin n → ℝ) :
    (∏ l, (C/R^(c.partSize l))*(∏ j, a (c.emb l j))) =
      C^c.length/R^n*(∏ j, a j) := by
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum, sum_partSize,
    c.prod_sigma_eq_prod]

theorem small_chaos_constant {k : ℕ} (hk : k ≤ 3) : (k:ℝ)^k ≤ 36 := by
  interval_cases k <;> norm_num

end
end GradientHessian.SelectorPartitions
