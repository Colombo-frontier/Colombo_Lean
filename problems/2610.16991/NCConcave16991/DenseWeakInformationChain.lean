import NCConcave16991.DenseWeakEntropyInequalities

/-! # Exact information chain rule for actual finite joint laws -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

def conditionalEntropy (P : FiniteLaw (I × J)) : ℝ :=
  ∑ i, rowMass P.mass i * finiteEntropy (conditionalMass P.mass i)

theorem entropy_chain_rule (P : FiniteLaw (I × J)) :
    P.entropy = P.fst.entropy + P.conditionalEntropy :=
  finiteEntropy_chain_rule P.mass P.nonneg

def reassoc (P : FiniteLaw (I × (J × K))) : FiniteLaw ((I × J) × K) where
  mass := fun z ↦ P.mass (z.1.1, z.1.2, z.2)
  nonneg := fun z ↦ P.nonneg _
  sum_one := by
    simpa only [Fintype.sum_prod_type] using P.sum_one

theorem reassoc_entropy (P : FiniteLaw (I × (J × K))) : P.reassoc.entropy = P.entropy := by
  simp only [entropy, finiteEntropy, reassoc, Fintype.sum_prod_type]

theorem reassoc_fst_fst_mass (P : FiniteLaw (I × (J × K))) :
    P.reassoc.fst.fst.mass = P.fst.mass := by
  funext i
  simp only [fst, rowMass, reassoc, Fintype.sum_prod_type]

theorem reassoc_fst_snd_mass (P : FiniteLaw (I × (J × K))) :
    P.reassoc.fst.snd.mass = P.snd.fst.mass := by
  funext j
  simp only [fst, snd, rowMass, reassoc]
  exact Finset.sum_comm

/-- Information after adding one actual response equals previous information
plus response entropy given history minus response entropy given label/history.
This is an equality of the actual joint mass, including null histories. -/
theorem mutualInformation_chain_rule (P : FiniteLaw (I × (J × K))) :
    P.mutualInformation = P.reassoc.fst.mutualInformation +
      P.snd.conditionalEntropy - P.reassoc.conditionalEntropy := by
  have h1 := entropy_chain_rule P.snd
  have h2 := entropy_chain_rule P.reassoc
  have h0 := reassoc_entropy P
  have hI : P.reassoc.fst.fst.entropy = P.fst.entropy := by
    unfold entropy
    rw [reassoc_fst_fst_mass]
  have hH : P.reassoc.fst.snd.entropy = P.snd.fst.entropy := by
    unfold entropy
    rw [reassoc_fst_snd_mass]
  unfold mutualInformation
  rw [hI, hH]
  linarith only [h1, h2, h0]

end NCConcave16991.DenseWeakHiding.FiniteLaw
