import NCConcave16991.DenseWeakInformationChain
import Mathlib.Algebra.BigOperators.Field

/-! # Actual conditional mutual-information increments, including null histories -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

variable {H I J : Type*} [Fintype H] [Fintype I] [Fintype J]

def historyLabels (P : FiniteLaw (H × (I × J))) : FiniteLaw (H × I) where
  mass := fun z ↦ ∑ j, P.mass (z.1, z.2, j)
  nonneg := fun z ↦ Finset.sum_nonneg (fun j _ ↦ P.nonneg _)
  sum_one := by simpa only [Fintype.sum_prod_type] using P.sum_one

def historyReplies (P : FiniteLaw (H × (I × J))) : FiniteLaw (H × J) where
  mass := fun z ↦ ∑ i, P.mass (z.1, i, z.2)
  nonneg := fun z ↦ Finset.sum_nonneg (fun i _ ↦ P.nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type]
    change (∑ h, ∑ j, ∑ i, P.mass (h,i,j)) = 1
    have he : (∑ h, ∑ j, ∑ i, P.mass (h,i,j)) = ∑ h, ∑ i, ∑ j, P.mass (h,i,j) := by
      apply Finset.sum_congr rfl
      intro h _
      exact Finset.sum_comm
    rw [he]
    simpa only [Fintype.sum_prod_type] using P.sum_one

def labelHistory (P : FiniteLaw (H × (I × J))) : FiniteLaw (I × H) where
  mass := fun z ↦ P.historyLabels.mass (z.2,z.1)
  nonneg := fun z ↦ P.historyLabels.nonneg _
  sum_one := by
    simp only [Fintype.sum_prod_type]
    change (∑ i, ∑ h, P.historyLabels.mass (h,i)) = 1
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using P.historyLabels.sum_one

def labelHistoryReply (P : FiniteLaw (H × (I × J))) : FiniteLaw (I × (H × J)) where
  mass := fun z ↦ P.mass (z.2.1, z.1, z.2.2)
  nonneg := fun z ↦ P.nonneg _
  sum_one := by
    simp only [Fintype.sum_prod_type]
    change (∑ i, ∑ h, ∑ j, P.mass (h,i,j)) = 1
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using P.sum_one

def conditionalPair (P : FiniteLaw (H × (I × J))) (h : H) (hh : 0 < P.fst.mass h) :
    FiniteLaw (I × J) where
  mass := conditionalMass P.mass h
  nonneg := conditionalMass_nonneg P.mass P.nonneg h
  sum_one := conditionalMass_sum P.mass h hh.ne'

theorem historyLabels_fst_mass (P : FiniteLaw (H × (I × J))) :
    P.historyLabels.fst.mass = P.fst.mass := by
  funext h
  simp only [fst, rowMass, historyLabels, Fintype.sum_prod_type]

theorem historyReplies_fst_mass (P : FiniteLaw (H × (I × J))) :
    P.historyReplies.fst.mass = P.fst.mass := by
  funext h
  simp only [fst, rowMass, historyReplies, Fintype.sum_prod_type]
  exact Finset.sum_comm

def conditionalPairInformation (P : FiniteLaw (H × (I × J))) (h : H) : ℝ :=
  finiteEntropy (conditionalMass P.historyLabels.mass h) +
    finiteEntropy (conditionalMass P.historyReplies.mass h) -
    finiteEntropy (conditionalMass P.mass h)

theorem conditionalPairInformation_eq (P : FiniteLaw (H × (I × J))) (h : H)
    (hh : 0 < P.fst.mass h) :
    P.conditionalPairInformation h = (P.conditionalPair h hh).mutualInformation := by
  have hf : (P.conditionalPair h hh).fst.mass = conditionalMass P.historyLabels.mass h := by
    funext i
    simp only [fst, rowMass, conditionalPair, conditionalMass, historyLabels, ← Finset.sum_div]
    congr 1
    exact (congrFun (historyLabels_fst_mass P) h).symm
  have hs : (P.conditionalPair h hh).snd.mass = conditionalMass P.historyReplies.mass h := by
    funext j
    simp only [snd, conditionalPair, conditionalMass, historyReplies, ← Finset.sum_div]
    congr 1
    exact (congrFun (historyReplies_fst_mass P) h).symm
  unfold conditionalPairInformation mutualInformation entropy
  rw [hf, hs]
  rfl

theorem history_information_increment (P : FiniteLaw (H × (I × J))) :
    P.labelHistoryReply.mutualInformation - P.labelHistory.mutualInformation =
      ∑ h, P.fst.mass h * P.conditionalPairInformation h := by
  have heL : P.labelHistory.entropy = P.historyLabels.entropy := by
    simp only [entropy, finiteEntropy, labelHistory, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have heP : P.labelHistoryReply.entropy = P.entropy := by
    simp only [entropy, finiteEntropy, labelHistoryReply, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hf : P.labelHistoryReply.fst.mass = P.labelHistory.fst.mass := by
    funext i
    simp only [fst, rowMass, labelHistoryReply, labelHistory, historyLabels, Fintype.sum_prod_type]
  have hs : P.labelHistoryReply.snd.mass = P.historyReplies.mass := by
    funext z
    rfl
  have hh : P.labelHistory.snd.mass = P.fst.mass := by
    funext h
    simp only [snd, labelHistory, historyLabels, fst, rowMass, Fintype.sum_prod_type]
  have hL := P.historyLabels.entropy_chain_rule
  have hR := P.historyReplies.entropy_chain_rule
  have hP := P.entropy_chain_rule
  have hLE : P.historyLabels.fst.entropy = P.fst.entropy := congrArg finiteEntropy (historyLabels_fst_mass P)
  have hRE : P.historyReplies.fst.entropy = P.fst.entropy := congrArg finiteEntropy (historyReplies_fst_mass P)
  rw [hLE] at hL
  rw [hRE] at hR
  have hLM : P.historyLabels.conditionalEntropy =
      ∑ h, P.fst.mass h * finiteEntropy (conditionalMass P.historyLabels.mass h) := by
    unfold conditionalEntropy
    rw [← historyLabels_fst_mass P]
    rfl
  have hRM : P.historyReplies.conditionalEntropy =
      ∑ h, P.fst.mass h * finiteEntropy (conditionalMass P.historyReplies.mass h) := by
    unfold conditionalEntropy
    rw [← historyReplies_fst_mass P]
    rfl
  rw [hLM] at hL
  rw [hRM] at hR
  have hPM : P.conditionalEntropy =
      ∑ h, P.fst.mass h * finiteEntropy (conditionalMass P.mass h) := rfl
  rw [hPM] at hP
  unfold mutualInformation
  change finiteEntropy P.labelHistoryReply.fst.mass + finiteEntropy P.labelHistoryReply.snd.mass -
    P.labelHistoryReply.entropy -
    (finiteEntropy P.labelHistory.fst.mass + finiteEntropy P.labelHistory.snd.mass - P.labelHistory.entropy) = _
  rw [hf, hs, hh, heL, heP]
  change finiteEntropy P.labelHistory.fst.mass + P.historyReplies.entropy - P.entropy -
    (finiteEntropy P.labelHistory.fst.mass + P.fst.entropy - P.historyLabels.entropy) = _
  simp only [conditionalPairInformation, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith only [hL, hR, hP]

theorem history_information_increment_le (P : FiniteLaw (H × (I × J))) (b : H → ℝ)
    (hb : ∀ h (hh : 0 < P.fst.mass h), (P.conditionalPair h hh).mutualInformation ≤ b h) :
    P.labelHistoryReply.mutualInformation - P.labelHistory.mutualInformation ≤
      ∑ h, P.fst.mass h * b h := by
  rw [history_information_increment]
  apply Finset.sum_le_sum
  intro h _
  by_cases hh : 0 < P.fst.mass h
  · rw [conditionalPairInformation_eq P h hh]
    exact mul_le_mul_of_nonneg_left (hb h hh) hh.le
  · have hz : P.fst.mass h = 0 := le_antisymm (le_of_not_gt hh) (P.fst.nonneg h)
    simp only [hz, zero_mul]
    exact le_rfl

end NCConcave16991.DenseWeakHiding.FiniteLaw
