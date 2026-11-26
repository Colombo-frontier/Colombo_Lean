import NCConcave16991.DenseWeakRelativeEntropy

/-! # Mutual information equals actual joint-versus-product divergence -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

variable {I J : Type*} [Fintype I] [Fintype J]

theorem mass_le_fst (P : FiniteLaw (I × J)) (i : I) (j : J) :
    P.mass (i, j) ≤ P.fst.mass i :=
  Finset.single_le_sum (fun k _ ↦ P.nonneg (i,k)) (Finset.mem_univ j)

theorem mass_le_snd (P : FiniteLaw (I × J)) (i : I) (j : J) :
    P.mass (i, j) ≤ P.snd.mass j :=
  Finset.single_le_sum (fun k _ ↦ P.nonneg (k,j)) (Finset.mem_univ i)

theorem joint_supportedBy_product (P : FiniteLaw (I × J)) :
    P.SupportedBy (P.fst.product P.snd) := by
  intro z hz
  exact mul_pos (hz.trans_le (P.mass_le_fst z.1 z.2)) (hz.trans_le (P.mass_le_snd z.1 z.2))

theorem log_product_mass_weighted (P : FiniteLaw (I × J)) (z : I × J) :
    P.mass z * Real.log ((P.fst.product P.snd).mass z) =
      P.mass z * Real.log (P.fst.mass z.1) + P.mass z * Real.log (P.snd.mass z.2) := by
  by_cases hp : P.mass z = 0
  · simp only [hp, zero_mul, add_zero]
  · have hz := lt_of_le_of_ne (P.nonneg z) (Ne.symm hp)
    have hfst := hz.trans_le (P.mass_le_fst z.1 z.2)
    have hsnd := hz.trans_le (P.mass_le_snd z.1 z.2)
    change _ * Real.log (P.fst.mass z.1 * P.snd.mass z.2) = _
    rw [Real.log_mul hfst.ne' hsnd.ne', mul_add]

theorem mutualInformation_eq_relativeEntropy (P : FiniteLaw (I × J)) :
    P.mutualInformation = P.relativeEntropy (P.fst.product P.snd) := by
  have hfst : (∑ z, P.mass z * Real.log (P.fst.mass z.1)) =
      -P.fst.entropy := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_mul]
    simp only [entropy, finiteEntropy, Real.negMulLog_eq_neg, Finset.sum_neg_distrib,
      neg_neg, fst, rowMass]
  have hsnd : (∑ z, P.mass z * Real.log (P.snd.mass z.2)) =
      -P.snd.entropy := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.sum_mul, entropy, finiteEntropy, Real.negMulLog_eq_neg,
      Finset.sum_neg_distrib, neg_neg, snd]
  have hjoint : (∑ z, P.mass z * Real.log (P.mass z)) = -P.entropy := by
    simp only [entropy, finiteEntropy, Real.negMulLog_eq_neg, Finset.sum_neg_distrib, neg_neg]
  have hprod := Finset.sum_congr rfl (fun z (_ : z ∈ (Finset.univ : Finset (I × J))) ↦
    log_product_mass_weighted P z)
  rw [Finset.sum_add_distrib, hfst, hsnd] at hprod
  unfold relativeEntropy
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hjoint, hprod]
  unfold mutualInformation
  ring

end NCConcave16991.DenseWeakHiding.FiniteLaw
