import NCConcave16991.DenseWeakFiniteEntropy

/-! # Finite conditional entropy and nonnegative mutual information -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding

theorem rowMass_mul_conditionalMass {I J : Type*} [Fintype J] (mass : I × J → ℝ)
    (hp : ∀ z, 0 ≤ mass z) (i : I) (j : J) :
    rowMass mass i * conditionalMass mass i j = mass (i, j) := by
  by_cases hi : rowMass mass i = 0
  · rw [hi, zero_mul, rowMass_zero_entry mass hp i hi j]
  · unfold conditionalMass
    field_simp

namespace FiniteLaw

variable {I J : Type*} [Fintype I] [Fintype J]

theorem entropy_nonneg (P : FiniteLaw I) : 0 ≤ P.entropy :=
  Finset.sum_nonneg (fun i _ ↦ Real.negMulLog_nonneg (P.nonneg i) (P.mass_le_one i))

/-- Conditioning cannot increase the entropy of an actual finite law. -/
theorem conditional_entropy_le_snd (P : FiniteLaw (I × J)) :
    (∑ i, rowMass P.mass i * finiteEntropy (conditionalMass P.mass i)) ≤ P.snd.entropy := by
  have hw : ∑ i, rowMass P.mass i = 1 := P.fst.sum_one
  have hj (j : J) : (∑ i, rowMass P.mass i * Real.negMulLog (conditionalMass P.mass i j)) ≤
      Real.negMulLog (P.snd.mass j) := by
    have h := Real.concaveOn_negMulLog.le_map_sum
      (t := (Finset.univ : Finset I)) (w := rowMass P.mass)
      (p := fun i ↦ conditionalMass P.mass i j)
      (fun i _ ↦ rowMass_nonneg P.mass P.nonneg i) hw
      (fun i _ ↦ conditionalMass_nonneg P.mass P.nonneg i j)
    have hm : (∑ i, rowMass P.mass i • conditionalMass P.mass i j) = P.snd.mass j := by
      simp only [smul_eq_mul, rowMass_mul_conditionalMass P.mass P.nonneg]
      rfl
    rw [hm] at h
    simpa only [smul_eq_mul] using h
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) ↦ hj j)
  rw [Finset.sum_comm] at hsum
  simpa only [entropy, finiteEntropy, ← Finset.mul_sum] using hsum

theorem entropy_le_marginal_sum (P : FiniteLaw (I × J)) :
    P.entropy ≤ P.fst.entropy + P.snd.entropy := by
  change finiteEntropy P.mass ≤ finiteEntropy (rowMass P.mass) + P.snd.entropy
  rw [finiteEntropy_chain_rule P.mass P.nonneg]
  linarith only [conditional_entropy_le_snd P]

theorem mutualInformation_nonneg (P : FiniteLaw (I × J)) : 0 ≤ P.mutualInformation := by
  have h := entropy_le_marginal_sum P
  unfold mutualInformation
  linarith only [h]

end FiniteLaw

end NCConcave16991.DenseWeakHiding
